//! Source function overload groups.
//!
//! The binder owns declaration grouping and order. This provider retains that
//! order and publishes one anonymous callable object. An implementation has its
//! own signature and checked body but is excluded from the public call list.
//! The shared call resolver reads the complete reverse-map/cache proof.

use std::{collections::HashSet, sync::Arc};

use ts_ast::{Node, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeHost, SignatureId, TypeId,
    array_types::CanonicalArrayTargets,
    bootstrap::LiteralTypeCacheError,
    callables::ValidatedSingleCallable,
    instantiate::{InstantiationSession, instantiate_type_with_vector_and_session},
    links::{
        DecoratorSignatureState, EffectsSignatureState, ResolvedSignatureState, SignatureLinks,
        ValueSymbolLinks,
    },
    relater::RelationUnavailable,
    relation::RelationKind,
    signatures::SignatureFlags,
    source_callables::{
        CallableTypePredicatePlan, SourceCallableBodyMode, SourceCallableDefaultType,
        SourceCallableError, SourceCallablePlan, SourceCallableReturnPlan,
        cached_annotation_identity, plan_callable_type_predicate,
        plan_source_ambient_overload_declaration, plan_source_exported_overload_declaration,
        plan_source_jsdoc_overload_declaration, valid_optional_type,
    },
    store::{
        PreparedSourceOverloadParameter, PreparedSourceOverloadPublication,
        PreparedSourceOverloadSignature, SourceCallableFamily, SourceNodeParent,
        SourceOverloadImplementation,
    },
    type_nodes::SourceCallableTypeQueryEvidence,
    type_records::{ConstrainedTypeData, TypeCacheState, TypeData},
    types::{ObjectFlags, TypeFlags},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceOverloadPlan {
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) declarations: Vec<SourceCallablePlan>,
    pub(super) implementation: Option<SourceOverloadImplementation>,
    pub(super) array_targets: Option<CanonicalArrayTargets>,
}

/// One annotated parameter retained without publishing a namespace overload.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceNamespaceAmbientOverloadParameter {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) annotation: NodeRef,
    pub(super) optional: bool,
    pub(super) rest: bool,
}

/// One generic parameter and its optional source-written bounds.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceNamespaceAmbientOverloadTypeParameter {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) constraint: Option<NodeRef>,
    pub(super) default_type: Option<NodeRef>,
}

/// One namespace-owned ambient signature in binder declaration order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceNamespaceAmbientOverloadDeclaration {
    pub(super) declaration: NodeRef,
    pub(super) type_parameters: Vec<SourceNamespaceAmbientOverloadTypeParameter>,
    pub(super) parameters: Vec<SourceNamespaceAmbientOverloadParameter>,
    pub(super) return_type: NodeRef,
    pub(super) type_predicate: Option<CallableTypePredicatePlan>,
}

/// An authenticated ambient namespace overload group with its export-local alias.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceNamespaceAmbientOverloadPlan {
    pub(super) namespace: SemanticSymbolId,
    pub(super) namespace_declaration: NodeRef,
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) export_local: SemanticSymbolId,
    pub(super) declarations: Vec<SourceNamespaceAmbientOverloadDeclaration>,
}

impl SourceNamespaceAmbientOverloadPlan {
    /// Returns generic bounds, parameter annotations, and return types in source order.
    pub(super) fn annotations(&self) -> impl Iterator<Item = NodeRef> + '_ {
        self.declarations.iter().flat_map(|declaration| {
            declaration
                .type_parameters
                .iter()
                .flat_map(|parameter| {
                    parameter
                        .constraint
                        .into_iter()
                        .chain(parameter.default_type)
                })
                .chain(
                    declaration
                        .parameters
                        .iter()
                        .map(|parameter| parameter.annotation),
                )
                .chain(std::iter::once(
                    declaration
                        .type_predicate
                        .map_or(declaration.return_type, |predicate| predicate.node),
                ))
        })
    }
}

#[derive(Clone, Debug)]
pub(super) struct ResolvedSourceOverloadSignature {
    pub(super) query_evidence: Option<Arc<SourceCallableTypeQueryEvidence>>,
    /// Base types and source-checked default literal proofs, in source order.
    pub(super) parameter_types: Vec<(TypeId, Option<SourceCallableDefaultType>)>,
    pub(super) return_type: TypeId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct MaterializedSourceOverload {
    pub(super) type_: TypeId,
    pub(super) signatures: Box<[SignatureId]>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum StoredSourceOverloadValidation {
    NotSourceOverload,
    Valid(Vec<TypeId>),
    Malformed,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceOverloadInvariant {
    EmptyGroup,
    Group(NodeRef),
    Cache(NodeRef),
    Publication(NodeRef),
    Capacity(NodeRef),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceOverloadError {
    Unsupported(NodeRef),
    Callable(SourceCallableError),
    Literal(LiteralTypeCacheError),
    Invariant(SourceOverloadInvariant),
}

impl SourceOverloadError {
    pub(super) const fn node(self) -> Option<NodeRef> {
        match self {
            Self::Callable(error) => error.node(),
            Self::Unsupported(node)
            | Self::Invariant(
                SourceOverloadInvariant::Group(node)
                | SourceOverloadInvariant::Cache(node)
                | SourceOverloadInvariant::Publication(node)
                | SourceOverloadInvariant::Capacity(node),
            ) => Some(node),
            Self::Literal(_) | Self::Invariant(SourceOverloadInvariant::EmptyGroup) => None,
        }
    }
}

impl From<SourceCallableError> for SourceOverloadError {
    fn from(error: SourceCallableError) -> Self {
        Self::Callable(error)
    }
}

impl From<LiteralTypeCacheError> for SourceOverloadError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::Literal(error)
    }
}

/// Checks the implementation against visible declarations in their original order.
pub(super) fn first_incompatible_source_overload(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    strict_function_types: bool,
    session: &mut super::instantiate::InstantiationSession,
    implementation: &super::callables::ValidatedSingleCallable,
    overloads: &[super::callables::ValidatedSingleCallable],
) -> Result<Option<SignatureId>, super::RelationUnavailable> {
    for overload in overloads {
        if !store.is_implementation_compatible_with_overload(
            implementation,
            overload,
            global_types,
            strict_function_types,
            session,
        )? {
            return Ok(Some(overload.signature));
        }
    }
    Ok(None)
}

/// Authenticates an implicitly or explicitly exported ambient overload group.
///
/// Generic declarations and rest parameters remain intact. Their later type
/// resolution and signature publication stay with the namespace executor.
#[allow(clippy::too_many_lines)] // Binder ownership and export provenance must be checked together.
pub(super) fn plan_source_namespace_ambient_overload_group(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    namespace: (NodeRef, SemanticSymbolId),
    owner_symbol: SemanticSymbolId,
    declarations: &[NodeRef],
) -> Result<SourceNamespaceAmbientOverloadPlan, SourceOverloadError> {
    let Some(first) = declarations.first().copied() else {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::EmptyGroup,
        ));
    };
    if declarations.len() < 2
        || declarations
            .iter()
            .enumerate()
            .any(|(index, declaration)| declarations[..index].contains(declaration))
    {
        return Err(namespace_overload_group_error(first));
    }

    let (namespace_declaration, namespace_symbol) = namespace;
    let (arena, bound) = host
        .source(namespace_declaration)
        .ok_or_else(|| namespace_overload_group_error(namespace_declaration))?;
    if declarations.iter().any(|declaration| {
        !declaration.is_for(namespace_declaration.arena, namespace_declaration.file)
    }) || bound
        .source_facts()
        .is_none_or(|facts| !facts.is_declaration_file() || facts.is_javascript_file())
    {
        return Err(SourceOverloadError::Unsupported(first));
    }

    let namespace_record = namespace_overload_node(host, namespace_declaration)?;
    let NodeData::ModuleDeclaration(module) = &namespace_record.data else {
        return Err(namespace_overload_group_error(namespace_declaration));
    };
    let body = module
        .body
        .map(|node| namespace_overload_child(namespace_declaration, node))
        .ok_or_else(|| namespace_overload_group_error(namespace_declaration))?;
    let body_record = namespace_overload_node(host, body)?;
    let NodeData::ModuleBlock(block) = &body_record.data else {
        return Err(namespace_overload_group_error(body));
    };
    let namespace_owner = store
        .symbol(namespace_symbol)
        .ok_or_else(|| namespace_overload_group_error(namespace_declaration))?;
    if namespace_record.kind != SyntaxKind::ModuleDeclaration
        || body_record.kind != SyntaxKind::ModuleBlock
        || body_record.parent != Some(namespace_declaration.node)
        || block.flow_node.is_some()
        || block.facts != 0
        || block.statements.has_trailing_comma
        || bound
            .symbol(namespace_declaration)
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(namespace_symbol)
        || !namespace_owner.flags().intersects(SymbolFlags::MODULE)
        || store.get_merged_symbol(namespace_symbol) != Some(namespace_symbol)
    {
        return Err(namespace_overload_group_error(namespace_declaration));
    }

    let owner = store
        .symbol(owner_symbol)
        .ok_or_else(|| namespace_overload_group_error(first))?;
    let Some(owner_name) = owner.name().as_utf8() else {
        return Err(namespace_overload_group_error(first));
    };
    let Some(exports) = namespace_owner
        .exports()
        .and_then(|exports| store.symbol_table(exports))
    else {
        return Err(namespace_overload_group_error(first));
    };
    if owner.flags() != SymbolFlags::FUNCTION
        || owner.check_flags() != CheckFlags::NONE
        || owner.declarations() != Some(declarations)
        || owner.value_declaration() != Some(first)
        || owner.members().is_some()
        || owner.exports().is_some()
        || owner
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(namespace_symbol)
        || store.get_parent_of_symbol(owner_symbol) != Some(namespace_symbol)
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
        || exports
            .get(owner.name())
            .and_then(|symbol| store.get_merged_symbol(symbol))
            != Some(owner_symbol)
    {
        return Err(namespace_overload_group_error(first));
    }

    let local = bound
        .local_symbol(first)
        .ok_or_else(|| namespace_overload_group_error(first))?;
    let local_record = store
        .symbol(local)
        .ok_or_else(|| namespace_overload_group_error(first))?;
    let namespace_locals = bound
        .locals(namespace_declaration)
        .and_then(|locals| store.symbol_table(locals))
        .ok_or_else(|| namespace_overload_group_error(first))?;
    if local == owner_symbol
        || local_record.flags() != SymbolFlags::EXPORT_VALUE
        || local_record.check_flags() != CheckFlags::NONE
        || local_record.name() != owner.name()
        || local_record.declarations() != Some(declarations)
        || local_record.value_declaration().is_some()
        || local_record.members().is_some()
        || local_record.exports().is_some()
        || local_record.parent().is_some()
        || local_record.export_symbol() != Some(owner_symbol)
        || store.get_merged_symbol(local) != Some(local)
        || namespace_locals.get(owner.name()) != Some(local)
    {
        return Err(namespace_overload_group_error(first));
    }
    if store
        .value_symbol_links(owner_symbol)
        .is_some_and(|links| links != &ValueSymbolLinks::default())
        || store
            .value_symbol_links(local)
            .is_some_and(|links| links != &ValueSymbolLinks::default())
        || store.source_overload_type_for_owner(owner_symbol).is_some()
        || store.source_callable_type_for_owner(owner_symbol).is_some()
    {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Cache(first),
        ));
    }

    let owned_declarations = block
        .statements
        .nodes
        .iter()
        .copied()
        .filter_map(|node| {
            let candidate = namespace_overload_child(namespace_declaration, node);
            (bound.symbol(candidate) == Some(owner_symbol)).then_some(candidate)
        })
        .collect::<Vec<_>>();
    if owned_declarations != declarations {
        return Err(namespace_overload_group_error(first));
    }

    let mut planned = Vec::with_capacity(declarations.len());
    for &declaration in declarations {
        planned.push(plan_namespace_ambient_overload_declaration(
            store,
            host,
            bound,
            body,
            owner_symbol,
            local,
            owner_name,
            declaration,
        )?);
    }
    debug_assert_eq!(arena.id(), namespace_declaration.arena);

    Ok(SourceNamespaceAmbientOverloadPlan {
        namespace: namespace_symbol,
        namespace_declaration,
        owner_symbol,
        export_local: local,
        declarations: planned,
    })
}

fn namespace_overload_group_error(node: NodeRef) -> SourceOverloadError {
    SourceOverloadError::Invariant(SourceOverloadInvariant::Group(node))
}

fn namespace_overload_node<'a>(
    host: &'a DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<&'a Node, SourceOverloadError> {
    host.node(node)
        .ok_or_else(|| namespace_overload_group_error(node))
}

fn namespace_overload_child(parent: NodeRef, node: NodeId) -> NodeRef {
    NodeRef::new(parent.arena, parent.file, node)
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)] // Retains every source-owned signature edge.
fn plan_namespace_ambient_overload_declaration(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    bound: &ts_binder::BoundFile,
    body: NodeRef,
    owner_symbol: SemanticSymbolId,
    local_symbol: SemanticSymbolId,
    owner_name: &str,
    declaration: NodeRef,
) -> Result<SourceNamespaceAmbientOverloadDeclaration, SourceOverloadError> {
    let record = namespace_overload_node(host, declaration)?;
    let NodeData::FunctionDeclaration(function) = &record.data else {
        return Err(namespace_overload_group_error(declaration));
    };
    if record.kind != SyntaxKind::FunctionDeclaration
        || record.flags.0 != 0
        || record.parent != Some(body.node)
        || function.end_flow_node.is_some()
        || function.flow_node.is_some()
        || function.full_signature.is_some()
        || function.local_symbol.is_some()
        || function.next_container.is_some()
        || function.return_flow_node.is_some()
        || function.symbol.is_some()
        || function.facts != 0
        || bound.symbol(declaration) != Some(owner_symbol)
        || bound.local_symbol(declaration) != Some(local_symbol)
    {
        return Err(namespace_overload_group_error(declaration));
    }
    if function.asterisk_token.is_some()
        || function.body.is_some()
        || function.parameters.has_trailing_comma
    {
        return Err(SourceOverloadError::Unsupported(declaration));
    }
    if store
        .signature_links(declaration)
        .is_some_and(|links| links != &SignatureLinks::default())
    {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Cache(declaration),
        ));
    }
    if let Some(modifiers) = function.modifiers.as_ref() {
        let [modifier] = modifiers.list.nodes.as_slice() else {
            return Err(SourceOverloadError::Unsupported(declaration));
        };
        let modifier = namespace_overload_child(declaration, *modifier);
        let modifier_record = namespace_overload_node(host, modifier)?;
        if modifiers.flags.0 != 0
            || modifiers.list.has_trailing_comma
            || modifier_record.kind != SyntaxKind::ExportKeyword
            || modifier_record.flags.0 != 0
            || modifier_record.parent != Some(declaration.node)
            || !matches!(modifier_record.data, NodeData::Token(_))
        {
            return Err(SourceOverloadError::Unsupported(modifier));
        }
    }

    let name = function
        .name
        .map(|name| namespace_overload_child(declaration, name))
        .ok_or_else(|| namespace_overload_group_error(declaration))?;
    let name_record = namespace_overload_node(host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(namespace_overload_group_error(name));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text != owner_name
    {
        return Err(namespace_overload_group_error(name));
    }

    let locals = bound
        .locals(declaration)
        .and_then(|locals| store.symbol_table(locals));
    let type_parameters = function
        .type_parameters
        .as_ref()
        .map(|parameters| {
            if parameters.nodes.is_empty() || parameters.has_trailing_comma {
                return Err(SourceOverloadError::Unsupported(declaration));
            }
            let mut planned = Vec::with_capacity(parameters.nodes.len());
            let mut seen_names = HashSet::with_capacity(parameters.nodes.len());
            let mut default_seen = false;
            for &node in &parameters.nodes {
                let parameter = namespace_overload_child(declaration, node);
                let record = namespace_overload_node(host, parameter)?;
                let NodeData::TypeParameterDeclaration(data) = &record.data else {
                    return Err(namespace_overload_group_error(parameter));
                };
                if data.expression.is_some()
                    || data.modifiers.is_some()
                    || default_seen && data.default_type.is_none()
                {
                    return Err(SourceOverloadError::Unsupported(parameter));
                }
                let name = namespace_overload_child(parameter, data.name);
                let name_record = namespace_overload_node(host, name)?;
                let NodeData::Identifier(identifier) = &name_record.data else {
                    return Err(namespace_overload_group_error(name));
                };
                let symbol = bound
                    .symbol(parameter)
                    .ok_or_else(|| namespace_overload_group_error(parameter))?;
                let symbol_record = store
                    .symbol(symbol)
                    .ok_or_else(|| namespace_overload_group_error(parameter))?;
                if record.kind != SyntaxKind::TypeParameter
                    || record.flags.0 != 0
                    || record.parent != Some(declaration.node)
                    || data.symbol.is_some()
                    || name_record.kind != SyntaxKind::Identifier
                    || name_record.flags.0 != 0
                    || name_record.parent != Some(parameter.node)
                    || identifier.flow_node.is_some()
                    || identifier.text.is_empty()
                    || !seen_names.insert(identifier.text.as_str())
                    || symbol_record.flags() != SymbolFlags::TYPE_PARAMETER
                    || symbol_record.check_flags() != CheckFlags::NONE
                    || symbol_record.declarations() != Some(&[parameter])
                    || symbol_record.value_declaration().is_some()
                    || symbol_record.members().is_some()
                    || symbol_record.exports().is_some()
                    || symbol_record.parent().is_some()
                    || symbol_record.export_symbol().is_some()
                    || store.get_merged_symbol(symbol) != Some(symbol)
                    || locals.and_then(|locals| locals.get_source(&identifier.text)) != Some(symbol)
                {
                    return Err(namespace_overload_group_error(parameter));
                }
                let constraint = data
                    .constraint
                    .map(|node| namespace_overload_child(parameter, node));
                let default_type = data
                    .default_type
                    .map(|node| namespace_overload_child(parameter, node));
                for annotation in [constraint, default_type].into_iter().flatten() {
                    if namespace_overload_node(host, annotation)?.parent != Some(parameter.node) {
                        return Err(namespace_overload_group_error(annotation));
                    }
                }
                default_seen |= default_type.is_some();
                planned.push(SourceNamespaceAmbientOverloadTypeParameter {
                    declaration: parameter,
                    symbol,
                    constraint,
                    default_type,
                });
            }
            Ok(planned)
        })
        .transpose()?
        .unwrap_or_default();

    let mut parameters = Vec::with_capacity(function.parameters.nodes.len());
    let mut optional_seen = false;
    for (index, &node) in function.parameters.nodes.iter().enumerate() {
        let parameter = namespace_overload_child(declaration, node);
        let record = namespace_overload_node(host, parameter)?;
        let NodeData::ParameterDeclaration(data) = &record.data else {
            return Err(namespace_overload_group_error(parameter));
        };
        let name = namespace_overload_child(parameter, data.name);
        let name_record = namespace_overload_node(host, name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(SourceOverloadError::Unsupported(parameter));
        };
        let optional = data.question_token.is_some();
        let rest = data.dot_dot_dot_token.is_some();
        if data.initializer.is_some()
            || data.modifiers.is_some()
            || identifier.text == "this"
            || optional && rest
            || optional_seen && !optional && !rest
            || rest && index + 1 != function.parameters.nodes.len()
        {
            return Err(SourceOverloadError::Unsupported(parameter));
        }
        let annotation = data
            .type_
            .map(|node| namespace_overload_child(parameter, node))
            .ok_or(SourceOverloadError::Unsupported(parameter))?;
        let annotation_record = namespace_overload_node(host, annotation)?;
        let symbol = bound
            .symbol(parameter)
            .ok_or_else(|| namespace_overload_group_error(parameter))?;
        let symbol_record = store
            .symbol(symbol)
            .ok_or_else(|| namespace_overload_group_error(parameter))?;
        if record.kind != SyntaxKind::Parameter
            || record.flags.0 != 0
            || record.parent != Some(declaration.node)
            || data.symbol.is_some()
            || data.facts != 0
            || name_record.kind != SyntaxKind::Identifier
            || name_record.flags.0 != 0
            || name_record.parent != Some(parameter.node)
            || identifier.flow_node.is_some()
            || identifier.text.is_empty()
            || annotation_record.parent != Some(parameter.node)
            || symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            || symbol_record.check_flags() != CheckFlags::NONE
            || symbol_record.declarations() != Some(&[parameter])
            || symbol_record.value_declaration() != Some(parameter)
            || symbol_record.members().is_some()
            || symbol_record.exports().is_some()
            || symbol_record.parent().is_some()
            || symbol_record.export_symbol().is_some()
            || store.get_merged_symbol(symbol) != Some(symbol)
            || locals.and_then(|locals| locals.get_source(&identifier.text)) != Some(symbol)
        {
            return Err(namespace_overload_group_error(parameter));
        }
        for (token, expected) in [
            (data.question_token, SyntaxKind::QuestionToken),
            (data.dot_dot_dot_token, SyntaxKind::DotDotDotToken),
        ] {
            if let Some(token) = token {
                let token = namespace_overload_child(parameter, token);
                let token_record = namespace_overload_node(host, token)?;
                if token_record.kind != expected || token_record.parent != Some(parameter.node) {
                    return Err(namespace_overload_group_error(token));
                }
            }
        }
        optional_seen |= optional;
        parameters.push(SourceNamespaceAmbientOverloadParameter {
            declaration: parameter,
            symbol,
            annotation,
            optional,
            rest,
        });
    }

    let return_type = function
        .type_
        .map(|node| namespace_overload_child(declaration, node))
        .ok_or(SourceOverloadError::Unsupported(declaration))?;
    if namespace_overload_node(host, return_type)?.parent != Some(declaration.node) {
        return Err(namespace_overload_group_error(return_type));
    }
    let type_predicate = if store.source_node_kind(return_type) == Some(SyntaxKind::TypePredicate) {
        let predicate = plan_callable_type_predicate(store, host, return_type)?;
        if predicate.owner != declaration
            || parameters
                .get(usize::try_from(predicate.parameter_index).unwrap_or(usize::MAX))
                .is_none_or(|parameter| parameter.symbol != predicate.parameter_symbol)
        {
            return Err(namespace_overload_group_error(return_type));
        }
        Some(predicate)
    } else {
        None
    };
    Ok(SourceNamespaceAmbientOverloadDeclaration {
        declaration,
        type_parameters,
        parameters,
        return_type,
        type_predicate,
    })
}

pub(super) fn plan_source_ambient_overload_group(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner_symbol: SemanticSymbolId,
    declarations: &[NodeRef],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceOverloadPlan, SourceOverloadError> {
    plan_source_overload_group(store, host, owner_symbol, declarations, None, array_targets)
}

pub(super) fn plan_source_jsdoc_overload_group(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner_symbol: SemanticSymbolId,
    declarations: &[NodeRef],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceOverloadPlan, SourceOverloadError> {
    let first = declarations
        .first()
        .copied()
        .ok_or(SourceOverloadError::Invariant(
            SourceOverloadInvariant::EmptyGroup,
        ))?;
    let (arena, _) = host.source(first).ok_or(SourceOverloadError::Invariant(
        SourceOverloadInvariant::Group(first),
    ))?;
    let group = super::jsdoc::authenticated_jsdoc_overload_group(arena, first)
        .filter(|group| group.declarations == declarations)
        .ok_or(SourceOverloadError::Unsupported(first))?;
    let Some(NodeData::FunctionDeclaration(function)) =
        arena.get(group.implementation.node).map(|node| &node.data)
    else {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Group(first),
        ));
    };
    let body = function.body.ok_or(SourceOverloadError::Invariant(
        SourceOverloadInvariant::Group(group.implementation),
    ))?;
    let implementation = SourceOverloadImplementation {
        declaration: group.implementation,
        body: NodeRef::new(first.arena, first.file, body),
    };
    plan_source_overload_group(
        store,
        host,
        owner_symbol,
        declarations,
        Some(implementation),
        array_targets,
    )
}

pub(super) fn plan_source_exported_overload_group(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner_symbol: SemanticSymbolId,
    declarations: &[NodeRef],
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceOverloadPlan, SourceOverloadError> {
    let declaration = declarations
        .last()
        .copied()
        .ok_or(SourceOverloadError::Invariant(
            SourceOverloadInvariant::EmptyGroup,
        ))?;
    if store
        .source_exported_overload_local(owner_symbol, declarations)
        .is_none()
    {
        return Err(SourceOverloadError::Unsupported(declaration));
    }
    let Some(NodeData::FunctionDeclaration(function)) =
        host.node(declaration).map(|node| &node.data)
    else {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Group(declaration),
        ));
    };
    let body = function
        .body
        .ok_or(SourceOverloadError::Unsupported(declaration))?;
    plan_source_overload_group(
        store,
        host,
        owner_symbol,
        declarations,
        Some(SourceOverloadImplementation {
            declaration,
            body: NodeRef::new(declaration.arena, declaration.file, body),
        }),
        array_targets,
    )
}

fn plan_source_overload_group(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    owner_symbol: SemanticSymbolId,
    declarations: &[NodeRef],
    implementation: Option<SourceOverloadImplementation>,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceOverloadPlan, SourceOverloadError> {
    let Some(first) = declarations.first().copied() else {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::EmptyGroup,
        ));
    };
    let global_namespace = implementation.is_none()
        && store
            .source_global_function_namespace_declarations(owner_symbol)
            .as_deref()
            == Some(declarations);
    if declarations.len() < 2 && !global_namespace
        || declarations
            .iter()
            .enumerate()
            .any(|(index, declaration)| declarations[..index].contains(declaration))
    {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Group(first),
        ));
    }
    if !global_namespace
        && declarations
            .iter()
            .any(|declaration| !declaration.is_for(first.arena, first.file))
    {
        return Err(SourceOverloadError::Unsupported(first));
    }
    let owner = store
        .symbol(owner_symbol)
        .ok_or(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Group(first),
        ))?;
    let export_local = implementation
        .and_then(|_| store.source_exported_overload_local(owner_symbol, declarations));
    if !global_namespace
        && (owner.flags() != SymbolFlags::FUNCTION
            || owner.declarations() != Some(declarations)
            || owner.exports().is_some())
        || owner.value_declaration() != Some(first)
        || owner.parent().is_some() && export_local.is_none()
        || export_local.is_none()
            && declarations.iter().any(|declaration| {
                store
                    .source_child_with_kind(*declaration, SyntaxKind::ExportKeyword)
                    .is_some()
                    && !(global_namespace
                        && store
                            .source_global_callable_augmentation_local(owner_symbol, *declaration)
                            .is_some())
            })
        || owner.export_symbol().is_some()
    {
        return Err(SourceOverloadError::Unsupported(first));
    }
    if owner.check_flags() != CheckFlags::NONE
        || owner.members().is_some()
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
    {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Group(first),
        ));
    }
    reject_conflicting_top_level_variables(host, first, owner.name().as_utf8())?;
    let mut plans = Vec::with_capacity(declarations.len());
    for declaration in declarations {
        let bound = host
            .bound_file(*declaration)
            .ok_or(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Group(*declaration),
            ))?;
        if bound.symbol(*declaration) != Some(owner_symbol)
            && !(global_namespace
                && bound
                    .symbol(*declaration)
                    .and_then(|raw| store.get_merged_symbol(raw))
                    == Some(owner_symbol))
        {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Group(*declaration),
            ));
        }
        let expected_local = if global_namespace {
            store.source_global_callable_augmentation_local(owner_symbol, *declaration)
        } else {
            export_local
        };
        if bound.local_symbol(*declaration) != expected_local {
            return Err(SourceOverloadError::Unsupported(*declaration));
        }
        if let Some(local) = export_local
            && bound
                .locals(bound.source_file())
                .and_then(|table| store.symbol_table(table))
                .and_then(|table| table.get(owner.name()))
                != Some(local)
        {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Group(*declaration),
            ));
        }
        let planner = if export_local.is_some() {
            plan_source_exported_overload_declaration
        } else if implementation.is_some() {
            plan_source_jsdoc_overload_declaration
        } else {
            plan_source_ambient_overload_declaration
        };
        plans.push(planner(
            store,
            host,
            *declaration,
            owner_symbol,
            declarations,
            array_targets,
        )?);
    }
    if !global_namespace
        && plans.iter().any(|plan| !plan.type_parameters.is_empty())
        && plans.iter().any(|plan| {
            plan.type_parameters.len() != 1
                && !(plan.type_parameters.is_empty()
                    && implementation.is_some_and(|implementation| {
                        implementation.declaration == plan.declaration
                            && implementation.body == plan.body
                            && plan.body_mode == SourceCallableBodyMode::Present
                    }))
        })
    {
        return Err(SourceOverloadError::Unsupported(first));
    }
    let plan = SourceOverloadPlan {
        owner_symbol,
        declarations: plans,
        implementation,
        array_targets,
    };
    validate_plan_state(store, &plan)?;
    Ok(plan)
}

fn reject_conflicting_top_level_variables(
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner_name: Option<&str>,
) -> Result<(), SourceOverloadError> {
    let Some(owner_name) = owner_name else {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Group(declaration),
        ));
    };
    let Some((arena, bound)) = host.source(declaration) else {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Group(declaration),
        ));
    };
    let source = bound.source_file();
    let Some(NodeData::SourceFile(source)) = arena.get(source.node).map(|node| &node.data) else {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Group(declaration),
        ));
    };
    for statement in &source.statements.nodes {
        let Some(NodeData::VariableStatement(statement)) =
            arena.get(*statement).map(|node| &node.data)
        else {
            continue;
        };
        let Some(NodeData::VariableDeclarationList(list)) =
            arena.get(statement.declaration_list).map(|node| &node.data)
        else {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Group(declaration),
            ));
        };
        for variable in &list.declarations.nodes {
            let Some(NodeData::VariableDeclaration(variable_data)) =
                arena.get(*variable).map(|node| &node.data)
            else {
                return Err(SourceOverloadError::Invariant(
                    SourceOverloadInvariant::Group(declaration),
                ));
            };
            let Some(NodeData::Identifier(name)) =
                arena.get(variable_data.name).map(|node| &node.data)
            else {
                continue;
            };
            if name.text == owner_name {
                return Err(SourceOverloadError::Unsupported(NodeRef::new(
                    declaration.arena,
                    declaration.file,
                    *variable,
                )));
            }
        }
    }
    Ok(())
}

pub(super) fn prepare_source_overload_publication(
    store: &mut CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    plan: &SourceOverloadPlan,
    resolved: &[ResolvedSourceOverloadSignature],
) -> Result<PreparedSourceOverloadPublication, SourceOverloadError> {
    let first = plan
        .declarations
        .first()
        .ok_or(SourceOverloadError::Invariant(
            SourceOverloadInvariant::EmptyGroup,
        ))?;
    if plan.declarations.len() != resolved.len() {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Publication(first.declaration),
        ));
    }
    let strict = store
        .intrinsic_bootstrap()
        .ok_or(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Capacity(first.declaration),
        ))?
        .options
        .strict_null_checks;
    let undefined = store
        .intrinsic_bootstrap()
        .expect("the bootstrap was checked")
        .undefined_type;
    let optional_count = plan
        .declarations
        .iter()
        .flat_map(|declaration| &declaration.parameters)
        .filter(|parameter| parameter.optional || parameter.has_string_default_type())
        .count();
    let mut prepared_types = store.prepare_type_query_types_with_global_types(
        &[],
        &[],
        &[],
        optional_count,
        0,
        global_types,
    )?;
    let mut signatures = Vec::with_capacity(plan.declarations.len());
    for (declaration, resolved) in plan.declarations.iter().zip(resolved) {
        if declaration.parameters.len() != resolved.parameter_types.len()
            || store.type_payload(resolved.return_type).is_none()
            || resolved
                .query_evidence
                .as_ref()
                .map_or(!declaration.type_parameters.is_empty(), |evidence| {
                    !evidence.matches_plan(declaration) || !evidence.is_exact(store)
                })
        {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Publication(declaration.declaration),
            ));
        }
        let (return_annotation, return_null_literal_identity) =
            match declaration.return_type.annotation_identity() {
                Some((annotation, null_literal_identity)) => {
                    if cached_annotation_identity(store, annotation, null_literal_identity)
                        != Some(resolved.return_type)
                    {
                        return Err(SourceOverloadError::Invariant(
                            SourceOverloadInvariant::Cache(annotation),
                        ));
                    }
                    (Some(annotation), null_literal_identity)
                }
                None if declaration.return_type.is_inferred()
                    && declaration.body_mode == SourceCallableBodyMode::Present
                    && declaration.type_parameters.is_empty()
                    && !declaration.is_async
                    && plan.implementation.is_some_and(|implementation| {
                        implementation.declaration == declaration.declaration
                            && implementation.body == declaration.body
                            && store.source_empty_overload_implementation_is_exact(
                                plan.owner_symbol,
                                implementation,
                            )
                    })
                    && store
                        .intrinsic_bootstrap()
                        .is_some_and(|bootstrap| resolved.return_type == bootstrap.void_type) =>
                {
                    (None, false)
                }
                None => {
                    return Err(SourceOverloadError::Invariant(
                        SourceOverloadInvariant::Publication(declaration.declaration),
                    ));
                }
            };
        let mut parameters = Vec::with_capacity(declaration.parameters.len());
        for (parameter, (base_type, default_parameter)) in
            declaration.parameters.iter().zip(&resolved.parameter_types)
        {
            let (annotation, annotation_null_literal_identity) = parameter.annotation_identity();
            let default_parameter = *default_parameter;
            let type_is_exact = match default_parameter {
                Some(proof) => {
                    proof.parameter() == *parameter
                        && declaration.type_parameters.is_empty()
                        && plan.implementation.is_some_and(|implementation| {
                            implementation.declaration == declaration.declaration
                                && implementation.body == declaration.body
                        })
                        && proof.is_exact(store, declaration.declaration, *base_type)
                }
                None => {
                    !parameter.has_string_default_type()
                        && cached_annotation_identity(
                            store,
                            annotation,
                            annotation_null_literal_identity,
                        ) == Some(*base_type)
                }
            };
            if !type_is_exact {
                return Err(SourceOverloadError::Invariant(
                    SourceOverloadInvariant::Cache(annotation),
                ));
            }
            if parameter.rest
                && !default_library_overload_rest_parameter_is_exact(
                    store,
                    plan.owner_symbol,
                    declaration.declaration,
                    parameter.declaration,
                    annotation,
                    *base_type,
                    plan.array_targets,
                )
                && !resolved.query_evidence.as_ref().is_some_and(|evidence| {
                    generic_global_overload_rest_parameter_is_exact(
                        store,
                        evidence,
                        parameter.declaration,
                        annotation,
                        *base_type,
                        plan.array_targets,
                    )
                })
            {
                return Err(SourceOverloadError::Unsupported(parameter.declaration));
            }
            let optional = parameter.optional || default_parameter.is_some();
            let call_type = if strict && optional {
                store.literal_union_type_prepared_with_global_types(
                    global_types,
                    &[*base_type, undefined],
                    None,
                    &mut prepared_types,
                )?
            } else {
                *base_type
            };
            if (optional
                && if strict {
                    !valid_optional_type(store, plan.array_targets, *base_type, call_type)
                } else {
                    call_type != *base_type
                })
                || (!optional && call_type != *base_type)
            {
                return Err(SourceOverloadError::Invariant(
                    SourceOverloadInvariant::Cache(parameter.declaration),
                ));
            }
            parameters.push(PreparedSourceOverloadParameter {
                declaration: parameter.declaration,
                symbol: parameter.symbol,
                annotation,
                annotation_null_literal_identity,
                base_type: *base_type,
                call_type,
                optional,
                default_parameter,
            });
        }
        signatures.push(PreparedSourceOverloadSignature {
            declaration: declaration.declaration,
            query_evidence: resolved.query_evidence.clone(),
            parameters,
            flags: declaration.flags,
            min_argument_count: declaration.min_argument_count,
            return_annotation,
            return_annotation_null_literal_identity: return_null_literal_identity,
            return_type: resolved.return_type,
        });
    }
    Ok(PreparedSourceOverloadPublication {
        owner_symbol: plan.owner_symbol,
        signatures,
        implementation: plan.implementation,
        array_targets: plan.array_targets,
    })
}

/// Checks the written final array parameter of a merged default-library function.
pub(super) fn default_library_overload_rest_parameter_is_exact(
    store: &CanonicalTypeMapperStore,
    owner: SemanticSymbolId,
    declaration: NodeRef,
    parameter: NodeRef,
    annotation: NodeRef,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> bool {
    let Some(targets) = array_targets else {
        return false;
    };
    if !store.source_is_default_library_declaration(declaration)
        || store
            .source_global_function_namespace_declarations(owner)
            .is_none_or(|declarations| !declarations.contains(&declaration))
        || store.source_node_kind(declaration) != Some(SyntaxKind::FunctionDeclaration)
        || store.source_node_kind(parameter) != Some(SyntaxKind::Parameter)
        || store.source_node_parent(parameter) != Some(SourceNodeParent::Parent(declaration))
        || store.source_direct_type_annotation(parameter) != Some(annotation)
        || store.source_node_kind(annotation) != Some(SyntaxKind::ArrayType)
        || !store.source_direct_type_annotation_is_exact(annotation, type_)
        || store
            .source_child_with_kind(parameter, SyntaxKind::DotDotDotToken)
            .is_none()
        || store
            .source_child_with_kind(parameter, SyntaxKind::QuestionToken)
            .is_some()
        || store
            .source_direct_children(declaration)
            .is_none_or(|children| {
                children
                    .iter()
                    .any(|child| store.source_node_kind(*child) == Some(SyntaxKind::TypeParameter))
                    || children
                        .into_iter()
                        .filter(|child| {
                            store.source_node_kind(*child) == Some(SyntaxKind::Parameter)
                        })
                        .last()
                        != Some(parameter)
            })
    {
        return false;
    }
    let Ok(Some(array)) = store.canonical_array_reference_with_targets(targets, type_) else {
        return false;
    };
    let Some(children) = store.source_direct_children(annotation) else {
        return false;
    };
    let [element] = children.as_slice() else {
        return false;
    };
    !array.readonly
        && !array.array_literal
        && store.source_node_parent(*element) == Some(SourceNodeParent::Parent(annotation))
        && store.source_direct_type_annotation_is_exact(*element, array.element_type)
}

/// Checks a written rest formal against its retained global-overload query.
pub(super) fn generic_global_overload_rest_parameter_is_exact(
    store: &CanonicalTypeMapperStore,
    evidence: &SourceCallableTypeQueryEvidence,
    parameter: NodeRef,
    annotation: NodeRef,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> bool {
    let Some(targets) = array_targets else {
        return false;
    };
    let plan = evidence.callable();
    let Some(rest) = plan.parameters.last() else {
        return false;
    };
    if plan.type_parameters.is_empty()
        || plan.body_mode != SourceCallableBodyMode::AmbientDeclaration
        || plan.array_targets != array_targets
        || plan.export_local.is_none()
        || store.source_global_callable_augmentation_local(plan.owner_symbol, plan.declaration)
            != plan.export_local
        || store
            .source_global_function_namespace_declarations(plan.owner_symbol)
            .is_none_or(|declarations| !declarations.contains(&plan.declaration))
        || !evidence.is_exact(store)
        || rest.declaration != parameter
        || !rest.rest
        || rest.optional
        || rest.initializer.is_some()
        || rest.explicit_type_node() != Some(annotation)
        || store.source_direct_type_annotation(parameter) != Some(annotation)
        || !store.source_direct_type_annotation_is_exact(annotation, type_)
        || evidence.annotation_type(annotation) != Some(type_)
    {
        return false;
    }
    let Some(formal) = evidence
        .type_parameters()
        .iter()
        .find(|formal| formal.provenance.type_parameter == type_)
    else {
        return false;
    };
    let Some(constraint_node) = formal.provenance.constraint else {
        return false;
    };
    if store.source_node_kind(constraint_node) != Some(SyntaxKind::ArrayType)
        || !store.source_direct_type_annotation_is_exact(constraint_node, formal.constraint)
    {
        return false;
    }
    store
        .canonical_array_reference_with_targets(targets, formal.constraint)
        .is_ok_and(|array| array.is_some_and(|array| !array.readonly && !array.array_literal))
}

pub(super) fn publish_source_overload_batch(
    store: &mut CanonicalTypeMapperStore,
    plans: &[SourceOverloadPlan],
    prepared: &[PreparedSourceOverloadPublication],
) -> Result<Vec<MaterializedSourceOverload>, SourceOverloadError> {
    let first = plans
        .first()
        .and_then(|plan| plan.declarations.first())
        .ok_or(SourceOverloadError::Invariant(
            SourceOverloadInvariant::EmptyGroup,
        ))?;
    if plans.len() != prepared.len() {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Publication(first.declaration),
        ));
    }
    let mut cold = Vec::new();
    for (plan, publication) in plans.iter().zip(prepared) {
        if !prepared_matches_plan(store, plan, publication) {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Publication(first.declaration),
            ));
        }
        match source_overload_state(store, plan)? {
            SourceOverloadState::Cold => cold.push(publication.clone()),
            SourceOverloadState::Resolved { .. } => {}
        }
    }
    let cold_len = cold.len();
    let published =
        store
            .publish_source_overload_batch(cold)
            .ok_or(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Publication(first.declaration),
            ))?;
    if published.len() != cold_len {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Publication(first.declaration),
        ));
    }
    let mut result = Vec::with_capacity(plans.len());
    for plan in plans {
        let SourceOverloadState::Resolved { type_, signatures } =
            source_overload_state(store, plan)?
        else {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Publication(first.declaration),
            ));
        };
        result.push(MaterializedSourceOverload { type_, signatures });
    }
    Ok(result)
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SourceOverloadState {
    Cold,
    Resolved {
        type_: TypeId,
        signatures: Box<[SignatureId]>,
    },
}

fn validate_plan_state(
    store: &CanonicalTypeMapperStore,
    plan: &SourceOverloadPlan,
) -> Result<(), SourceOverloadError> {
    source_overload_state(store, plan).map(|_| ())
}

fn source_overload_state(
    store: &CanonicalTypeMapperStore,
    plan: &SourceOverloadPlan,
) -> Result<SourceOverloadState, SourceOverloadError> {
    let first = plan
        .declarations
        .first()
        .ok_or(SourceOverloadError::Invariant(
            SourceOverloadInvariant::EmptyGroup,
        ))?;
    let declaration_nodes = plan
        .declarations
        .iter()
        .map(|row| row.declaration)
        .collect::<Vec<_>>();
    let global_namespace = plan.implementation.is_none()
        && store
            .source_global_function_namespace_declarations(plan.owner_symbol)
            .as_deref()
            == Some(declaration_nodes.as_slice());
    if plan.declarations.len() < 2 && !global_namespace
        || plan
            .declarations
            .iter()
            .enumerate()
            .any(|(index, declaration)| {
                let invalid_body = match plan.implementation {
                    Some(implementation) if index + 1 == plan.declarations.len() => {
                        declaration.declaration != implementation.declaration
                            || declaration.body != implementation.body
                            || declaration.body_mode != SourceCallableBodyMode::Present
                    }
                    Some(_) => declaration.body_mode != SourceCallableBodyMode::OverloadDeclaration,
                    None => declaration.body_mode != SourceCallableBodyMode::AmbientDeclaration,
                };
                invalid_body
                    || declaration.return_type.is_inferred()
                        && (declaration.is_async
                            || !declaration.type_parameters.is_empty()
                            || plan.implementation.is_none_or(|implementation| {
                                implementation.declaration != declaration.declaration
                                    || implementation.body != declaration.body
                                    || !store.source_empty_overload_implementation_is_exact(
                                        plan.owner_symbol,
                                        implementation,
                                    )
                            }))
            })
    {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Group(first.declaration),
        ));
    }
    let owner_links = store.value_symbol_links(plan.owner_symbol);
    let declarations_cold = plan.declarations.iter().all(|declaration| {
        store
            .signature_links(declaration.declaration)
            .is_none_or(|links| links == &SignatureLinks::default())
            && declaration.parameters.iter().all(|parameter| {
                store
                    .value_symbol_links(parameter.symbol)
                    .is_none_or(|links| links == &ValueSymbolLinks::default())
            })
    });
    let maps_cold = store
        .source_overload_type_for_owner(plan.owner_symbol)
        .is_none()
        && store
            .source_callable_type_for_owner(plan.owner_symbol)
            .is_none()
        && plan.declarations.iter().all(|declaration| {
            store
                .source_overload_type_for_declaration(declaration.declaration)
                .is_none()
                && store
                    .source_callable_type_for_declaration(declaration.declaration)
                    .is_none()
        })
        && !store.source_overload_provenance_claims(
            plan.owner_symbol,
            &plan
                .declarations
                .iter()
                .map(|declaration| declaration.declaration)
                .collect::<Vec<_>>(),
        );
    if owner_links.is_none_or(|links| links == &ValueSymbolLinks::default())
        && declarations_cold
        && maps_cold
    {
        return Ok(SourceOverloadState::Cold);
    }
    let type_ = owner_links
        .and_then(|links| {
            (links
                == &ValueSymbolLinks {
                    resolved_type: links.resolved_type,
                    ..ValueSymbolLinks::default()
                })
                .then_some(links.resolved_type)
                .flatten()
        })
        .ok_or(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Cache(first.declaration),
        ))?;
    if store.source_overload_type_for_owner(plan.owner_symbol) != Some(type_)
        || !matches!(
            validate_stored_source_overload(store, type_),
            StoredSourceOverloadValidation::Valid(_)
        )
    {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Cache(first.declaration),
        ));
    }
    let provenance =
        store
            .source_overload_provenance(type_)
            .ok_or(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Cache(first.declaration),
            ))?;
    if provenance.owner_symbol != plan.owner_symbol
        || provenance.implementation != plan.implementation
        || provenance.array_targets != plan.array_targets
        || provenance.signatures.len() != plan.declarations.len()
    {
        return Err(SourceOverloadError::Invariant(
            SourceOverloadInvariant::Cache(first.declaration),
        ));
    }
    for (declaration, row) in plan.declarations.iter().zip(&provenance.signatures) {
        let return_annotation = declaration.return_type.annotation_identity();
        if row.declaration != declaration.declaration
            || row.flags != declaration.flags
            || row
                .return_annotation
                .map(|annotation| (annotation, row.return_annotation_null_literal_identity))
                != return_annotation
            || return_annotation.is_none()
                && (!declaration.return_type.is_inferred()
                    || plan.implementation.is_none_or(|implementation| {
                        implementation.declaration != declaration.declaration
                            || implementation.body != declaration.body
                            || !store.source_empty_overload_implementation_is_exact(
                                plan.owner_symbol,
                                implementation,
                            )
                    }))
            || row.parameters.len() != declaration.parameters.len()
            || row.type_parameters.len() != declaration.type_parameters.len()
            || store
                .source_callable_type_query(row.signature)
                .map_or(!declaration.type_parameters.is_empty(), |evidence| {
                    !evidence.matches_plan(declaration)
                })
        {
            return Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Cache(declaration.declaration),
            ));
        }
        for (parameter, stored) in declaration.parameters.iter().zip(&row.parameters) {
            let (annotation, null_literal_identity) = parameter.annotation_identity();
            if stored.declaration != parameter.declaration
                || stored.symbol != parameter.symbol
                || stored.annotation != annotation
                || stored.annotation_null_literal_identity != null_literal_identity
                || stored.optional != (parameter.optional || parameter.has_string_default_type())
                || stored.default_parameter.map(|proof| proof.parameter())
                    != parameter.has_string_default_type().then_some(*parameter)
            {
                return Err(SourceOverloadError::Invariant(
                    SourceOverloadInvariant::Cache(parameter.declaration),
                ));
            }
        }
    }
    Ok(SourceOverloadState::Resolved {
        type_,
        signatures: provenance
            .signatures
            .iter()
            .map(|signature| signature.signature)
            .collect(),
    })
}

fn prepared_matches_plan(
    store: &CanonicalTypeMapperStore,
    group: &SourceOverloadPlan,
    prepared: &PreparedSourceOverloadPublication,
) -> bool {
    group.owner_symbol == prepared.owner_symbol
        && group.implementation == prepared.implementation
        && group.array_targets == prepared.array_targets
        && group.declarations.len() == prepared.signatures.len()
        && group
            .declarations
            .iter()
            .zip(&prepared.signatures)
            .all(|(plan, prepared)| {
                plan.declaration == prepared.declaration
                    && prepared
                        .query_evidence
                        .as_ref()
                        .map_or(plan.type_parameters.is_empty(), |evidence| {
                            evidence.matches_plan(plan)
                        })
                    && plan.flags == prepared.flags
                    && plan.min_argument_count == prepared.min_argument_count
                    && plan.parameters.len() == prepared.parameters.len()
                    && plan
                        .parameters
                        .iter()
                        .zip(&prepared.parameters)
                        .all(|(plan, prepared)| {
                            let (annotation, null_literal_identity) = plan.annotation_identity();
                            plan.declaration == prepared.declaration
                                && plan.symbol == prepared.symbol
                                && annotation == prepared.annotation
                                && null_literal_identity
                                    == prepared.annotation_null_literal_identity
                                && (plan.optional || plan.has_string_default_type())
                                    == prepared.optional
                                && prepared.default_parameter.map(|proof| proof.parameter())
                                    == plan.has_string_default_type().then_some(*plan)
                        })
                    && match prepared.return_annotation {
                        Some(_) => {
                            matches!(plan.return_type, SourceCallableReturnPlan::Annotated { .. })
                        }
                        None => {
                            plan.return_type.is_inferred()
                                && plan.body_mode == SourceCallableBodyMode::Present
                                && plan.type_parameters.is_empty()
                                && !plan.is_async
                                && !prepared.return_annotation_null_literal_identity
                                && group.implementation.is_some_and(|implementation| {
                                    implementation.declaration == plan.declaration
                                        && implementation.body == plan.body
                                        && store.source_empty_overload_implementation_is_exact(
                                            group.owner_symbol,
                                            implementation,
                                        )
                                })
                                && store.intrinsic_bootstrap().is_some_and(|bootstrap| {
                                    prepared.return_type == bootstrap.void_type
                                })
                        }
                    }
            })
}

pub(super) fn validate_stored_source_overload(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> StoredSourceOverloadValidation {
    let provenance = store.source_overload_provenance(type_);
    let malformed_or_not = || {
        if provenance.is_some() {
            StoredSourceOverloadValidation::Malformed
        } else {
            StoredSourceOverloadValidation::NotSourceOverload
        }
    };
    let Some(record) = store.type_payload(type_) else {
        return malformed_or_not();
    };
    let Some(owner_symbol) = record.symbol() else {
        return malformed_or_not();
    };
    let Some(owner) = store.symbol(owner_symbol) else {
        return malformed_or_not();
    };
    let Some(provenance) = provenance else {
        return if store.source_overload_type_for_owner(owner_symbol) == Some(type_) {
            StoredSourceOverloadValidation::Malformed
        } else {
            StoredSourceOverloadValidation::NotSourceOverload
        };
    };
    let declarations = provenance
        .signatures
        .iter()
        .map(|signature| signature.declaration)
        .collect::<Vec<_>>();
    let signatures = provenance
        .signatures
        .iter()
        .map(|signature| signature.signature)
        .collect::<Vec<_>>();
    let public_count = signatures
        .len()
        .saturating_sub(usize::from(provenance.implementation.is_some()));
    let export_local = provenance
        .implementation
        .and_then(|_| store.source_exported_overload_local(owner_symbol, &declarations));
    let global_namespace = provenance.implementation.is_none()
        && store
            .source_global_function_namespace_declarations(owner_symbol)
            .as_deref()
            == Some(declarations.as_slice());
    let TypeData::Object(object) = record.data() else {
        return StoredSourceOverloadValidation::Malformed;
    };
    if provenance.owner_symbol != owner_symbol
        || provenance.signatures.len() < 2 && !global_namespace
        || !global_namespace
            && (owner.flags() != SymbolFlags::FUNCTION
                || owner.declarations() != Some(declarations.as_slice())
                || owner.exports().is_some())
        || owner.check_flags() != CheckFlags::NONE
        || owner.value_declaration() != declarations.first().copied()
        || owner.members().is_some()
        || owner.parent().is_some() && export_local.is_none()
        || export_local.is_none()
            && declarations.iter().any(|declaration| {
                store
                    .source_child_with_kind(*declaration, SyntaxKind::ExportKeyword)
                    .is_some()
                    && !(global_namespace
                        && store
                            .source_global_callable_augmentation_local(owner_symbol, *declaration)
                            .is_some())
            })
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
        || store.source_overload_type_for_owner(owner_symbol) != Some(type_)
        || store.value_symbol_links(owner_symbol)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
        || record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.alias().is_some()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.structured.members
            != if global_namespace {
                owner.exports()
            } else {
                None
            }
        || object.structured.properties.is_some()
        || object.structured.signatures.as_deref() != Some(&signatures[..public_count])
        || object.structured.call_signature_count != public_count
        || provenance.implementation.is_some_and(|implementation| {
            declarations.last().copied() != Some(implementation.declaration)
                || store.source_node_kind(implementation.body) != Some(SyntaxKind::Block)
                || store.source_node_parent(implementation.body)
                    != Some(SourceNodeParent::Parent(implementation.declaration))
        })
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
        || provenance.array_targets.is_some_and(|targets| {
            store.type_payload(targets.array_type()).is_none()
                || store.type_payload(targets.readonly_array_type()).is_none()
        })
    {
        return StoredSourceOverloadValidation::Malformed;
    }

    let mut edges = Vec::new();
    let Some(strict_null_checks) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.options.strict_null_checks)
    else {
        return StoredSourceOverloadValidation::Malformed;
    };
    let mut unique_signatures = HashSet::with_capacity(signatures.len());
    let mut unique_parameters = HashSet::new();
    let mut unique_type_parameters = HashSet::new();
    for row in &provenance.signatures {
        if !unique_signatures.insert(row.signature)
            || store.source_node_kind(row.declaration) != Some(SyntaxKind::FunctionDeclaration)
            || store.source_overload_type_for_declaration(row.declaration) != Some(type_)
            || store.source_overload_type_for_signature(row.signature) != Some(type_)
            || store.signature_links(row.declaration)
                != Some(&SignatureLinks {
                    resolved_signature: ResolvedSignatureState::Resolved(row.signature),
                    effects_signature: EffectsSignatureState::Unresolved,
                    decorator_signature: DecoratorSignatureState::Unresolved,
                })
            || store.function_signature_return_annotation(row.signature)
                != row
                    .return_annotation
                    .map(|annotation| (annotation, row.return_annotation_null_literal_identity))
            || match row.return_annotation {
                Some(annotation) => {
                    cached_annotation_identity(
                        store,
                        annotation,
                        row.return_annotation_null_literal_identity,
                    ) != Some(row.return_type)
                }
                None => {
                    row.return_annotation_null_literal_identity
                        || !row.type_parameters.is_empty()
                        || store.signature_has_circular_return_type(row.signature)
                        || provenance.implementation.is_none_or(|implementation| {
                            implementation.declaration != row.declaration
                                || !store.source_empty_overload_implementation_is_exact(
                                    owner_symbol,
                                    implementation,
                                )
                        })
                        || store
                            .intrinsic_bootstrap()
                            .is_none_or(|bootstrap| row.return_type != bootstrap.void_type)
                }
            }
        {
            return StoredSourceOverloadValidation::Malformed;
        }
        let Some(signature) = store.signature(row.signature) else {
            return StoredSourceOverloadValidation::Malformed;
        };
        let parameter_symbols = row
            .parameters
            .iter()
            .map(|parameter| parameter.symbol)
            .collect::<Vec<_>>();
        let parameter_types = row
            .parameters
            .iter()
            .map(|parameter| parameter.call_type)
            .collect::<Vec<_>>();
        let type_parameters = row
            .type_parameters
            .iter()
            .map(|parameter| parameter.type_parameter)
            .collect::<Vec<_>>();
        let has_rest = row.flags.contains(SignatureFlags::HAS_REST_PARAMETER);
        if row.flags.bits()
            & !(SignatureFlags::HAS_LITERAL_TYPES | SignatureFlags::HAS_REST_PARAMETER).bits()
            != 0
            || has_rest && (row.parameters.is_empty() || !global_namespace)
            || signature.flags() != row.flags
            || signature.declaration() != Some(row.declaration)
            || signature.type_parameters() != type_parameters.as_slice()
            || signature.this_parameter().is_some()
            || signature.parameters() != parameter_symbols.as_slice()
            || signature.resolved_return_type() != Some(row.return_type)
            || signature.resolved_type_predicate().is_some()
            || signature.min_argument_count() < 0
            || usize::try_from(signature.min_argument_count())
                .map_or(true, |minimum| minimum > row.parameters.len())
            || signature.resolved_min_argument_count() != -1
            || signature.target().is_some()
            || signature.mapper().is_some()
            || signature.isolated_signature_type().is_some()
            || signature.composite().is_some()
            || store.callable_signature_parameter_types(row.signature)
                != Some(parameter_types.as_slice())
        {
            return StoredSourceOverloadValidation::Malformed;
        }
        if row.type_parameters.is_empty() {
            if store
                .source_callable_type_parameters(row.signature)
                .is_some()
                || store.source_callable_type_query(row.signature).is_some()
            {
                return StoredSourceOverloadValidation::Malformed;
            }
        } else {
            let Some(evidence) = store.source_callable_type_query(row.signature) else {
                return StoredSourceOverloadValidation::Malformed;
            };
            let plan = evidence.callable();
            let (body, body_mode, row_export_local) = if global_namespace {
                (
                    row.declaration,
                    SourceCallableBodyMode::AmbientDeclaration,
                    store.source_global_callable_augmentation_local(owner_symbol, row.declaration),
                )
            } else if let Some(implementation) = provenance.implementation {
                if row.declaration == implementation.declaration {
                    (
                        implementation.body,
                        SourceCallableBodyMode::Present,
                        export_local,
                    )
                } else {
                    (
                        row.declaration,
                        SourceCallableBodyMode::OverloadDeclaration,
                        export_local,
                    )
                }
            } else {
                return StoredSourceOverloadValidation::Malformed;
            };
            if !global_namespace && row.type_parameters.len() != 1
                || !plan.requires_type_query_evidence()
                || plan.family != SourceCallableFamily::FunctionDeclaration
                || plan.declaration != row.declaration
                || plan.owner_symbol != owner_symbol
                || plan.owner_parent != owner.parent()
                || plan.export_local != row_export_local
                || plan.body != body
                || plan.body_mode != body_mode
                || plan.is_async
                || plan.type_predicate.is_some()
                || plan.flags != row.flags
                || plan.min_argument_count != signature.min_argument_count()
                || plan.array_targets != provenance.array_targets
                || store.source_callable_type_for_owner(owner_symbol).is_some()
                || store
                    .source_callable_type_for_declaration(row.declaration)
                    .is_some()
                || store
                    .source_callable_type_for_signature(row.signature)
                    .is_some()
                || plan.return_type.annotation_identity()
                    != row
                        .return_annotation
                        .map(|annotation| (annotation, row.return_annotation_null_literal_identity))
                || !evidence.is_exact(store)
                || store.source_callable_type_parameters(row.signature)
                    != Some(row.type_parameters.as_ref())
                || evidence.type_parameters().len() != row.type_parameters.len()
                || plan.parameters.len() != row.parameters.len()
            {
                return StoredSourceOverloadValidation::Malformed;
            }
            for (parameter, resolved) in row.type_parameters.iter().zip(evidence.type_parameters())
            {
                if *parameter != resolved.provenance
                    || !global_namespace
                        && (parameter.constraint.is_some() || parameter.default_type.is_some())
                    || !unique_type_parameters.insert(parameter.symbol)
                {
                    return StoredSourceOverloadValidation::Malformed;
                }
                edges.push(parameter.type_parameter);
            }
            for (parameter, planned) in row.parameters.iter().zip(&plan.parameters) {
                if parameter.declaration != planned.declaration
                    || parameter.symbol != planned.symbol
                    || parameter.default_parameter.is_some()
                    || parameter.optional != planned.optional
                    || planned.optional && row_export_local.is_none() && !global_namespace
                    || planned.rest && !global_namespace
                    || planned.initializer.is_some()
                    || planned.explicit_type_node().is_none()
                    || planned.annotation_identity()
                        != (
                            parameter.annotation,
                            parameter.annotation_null_literal_identity,
                        )
                    || evidence.annotation_type(parameter.annotation) != Some(parameter.base_type)
                {
                    return StoredSourceOverloadValidation::Malformed;
                }
            }
        }
        let minimum =
            usize::try_from(signature.min_argument_count()).expect("the minimum was validated");
        let mut optional_seen = false;
        for (index, parameter) in row.parameters.iter().enumerate() {
            let rest = has_rest && index + 1 == row.parameters.len();
            let Some(symbol) = store.symbol(parameter.symbol) else {
                return StoredSourceOverloadValidation::Malformed;
            };
            let type_is_exact = match parameter.default_parameter {
                Some(proof) => {
                    let planned = proof.parameter();
                    parameter.optional
                        && row.type_parameters.is_empty()
                        && provenance.implementation.is_some_and(|implementation| {
                            implementation.declaration == row.declaration
                        })
                        && planned.declaration == parameter.declaration
                        && planned.symbol == parameter.symbol
                        && planned.annotation_identity()
                            == (
                                parameter.annotation,
                                parameter.annotation_null_literal_identity,
                            )
                        && proof.is_exact(store, row.declaration, parameter.base_type)
                }
                None => cached_annotation_identity(
                    store,
                    parameter.annotation,
                    parameter.annotation_null_literal_identity,
                ) == Some(parameter.base_type),
            };
            if !unique_parameters.insert(parameter.symbol)
                || symbol.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
                || symbol.check_flags() != CheckFlags::NONE
                || symbol.declarations() != Some(&[parameter.declaration])
                || symbol.value_declaration() != Some(parameter.declaration)
                || symbol.members().is_some()
                || symbol.exports().is_some()
                || symbol.parent().is_some()
                || symbol.export_symbol().is_some()
                || store.get_merged_symbol(parameter.symbol) != Some(parameter.symbol)
                || store.source_node_kind(parameter.declaration) != Some(SyntaxKind::Parameter)
                || store.source_node_parent(parameter.declaration)
                    != Some(SourceNodeParent::Parent(row.declaration))
                || !type_is_exact
                || store.value_symbol_links(parameter.symbol)
                    != Some(&ValueSymbolLinks {
                        resolved_type: Some(if parameter.default_parameter.is_some() {
                            parameter.base_type
                        } else {
                            parameter.call_type
                        }),
                        ..ValueSymbolLinks::default()
                    })
                || parameter.optional
                    && if strict_null_checks {
                        !valid_optional_type(
                            store,
                            provenance.array_targets,
                            parameter.base_type,
                            parameter.call_type,
                        )
                    } else {
                        parameter.call_type != parameter.base_type
                    }
                || !parameter.optional && parameter.call_type != parameter.base_type
                || optional_seen && !parameter.optional && !rest
                || parameter.optional != (index >= minimum && !rest)
                || rest && minimum > index
                || store
                    .source_child_with_kind(parameter.declaration, SyntaxKind::DotDotDotToken)
                    .is_some()
                    != rest
                || rest
                    && !default_library_overload_rest_parameter_is_exact(
                        store,
                        owner_symbol,
                        row.declaration,
                        parameter.declaration,
                        parameter.annotation,
                        parameter.base_type,
                        provenance.array_targets,
                    )
                    && !store
                        .source_callable_type_query(row.signature)
                        .is_some_and(|evidence| {
                            generic_global_overload_rest_parameter_is_exact(
                                store,
                                evidence,
                                parameter.declaration,
                                parameter.annotation,
                                parameter.base_type,
                                provenance.array_targets,
                            )
                        })
            {
                return StoredSourceOverloadValidation::Malformed;
            }
            optional_seen |= parameter.optional;
            if let Some(proof) = parameter.default_parameter {
                edges.push(proof.fresh());
            }
            edges.push(parameter.base_type);
            if parameter.call_type != parameter.base_type {
                edges.push(parameter.call_type);
            }
        }
        edges.push(row.return_type);
    }
    StoredSourceOverloadValidation::Valid(edges)
}

/// Rechecks the inferred return after the normal checker visits an empty implementation.
pub(super) fn source_overload_inferred_implementation_return(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
) -> Option<TypeId> {
    let type_ = store.source_overload_type_for_signature(signature)?;
    if !matches!(
        validate_stored_source_overload(store, type_),
        StoredSourceOverloadValidation::Valid(_)
    ) {
        return None;
    }
    let provenance = store.source_overload_provenance(type_)?;
    let implementation = provenance.implementation?;
    let row = provenance.signatures.last()?;
    let owner = store.symbol(provenance.owner_symbol)?;
    let declarations = owner.declarations()?;
    if row.signature != signature
        || row.declaration != plan.declaration
        || row.return_annotation.is_some()
        || implementation.declaration != plan.declaration
        || implementation.body != plan.body
        || !store.source_empty_overload_implementation_is_exact(plan.owner_symbol, implementation)
        || plan.family != SourceCallableFamily::FunctionDeclaration
        || plan.body_mode != SourceCallableBodyMode::Present
        || !plan.return_type.is_inferred()
        || !plan.type_parameters.is_empty()
        || plan.owner_symbol != provenance.owner_symbol
        || plan.owner_parent != owner.parent()
        || plan.export_local
            != store.source_exported_overload_local(plan.owner_symbol, declarations)
        || plan.is_async
        || plan.this_parameter.is_some()
        || plan.type_predicate.is_some()
        || plan.flags != row.flags
        || plan.min_argument_count != store.signature(signature)?.min_argument_count()
        || plan.array_targets != provenance.array_targets
        || plan.parameters.len() != row.parameters.len()
        || plan
            .parameters
            .iter()
            .zip(&row.parameters)
            .any(|(planned, stored)| {
                planned.declaration != stored.declaration
                    || planned.symbol != stored.symbol
                    || planned.annotation_identity()
                        != (stored.annotation, stored.annotation_null_literal_identity)
                    || planned.optional != stored.optional
                    || planned.rest
                    || planned.initializer.is_some()
                    || planned.is_implicit_any()
            })
    {
        return None;
    }
    Some(row.return_type)
}

/// Reads a real generic row's query proof, including the hidden implementation.
/// Call consumers must also prove membership in the public call list.
pub(super) fn source_overload_signature_type_query(
    store: &CanonicalTypeMapperStore,
    owner: TypeId,
    signature: SignatureId,
) -> Option<&SourceCallableTypeQueryEvidence> {
    if !matches!(
        validate_stored_source_overload(store, owner),
        StoredSourceOverloadValidation::Valid(_)
    ) {
        return None;
    }
    let provenance = store.source_overload_provenance(owner)?;
    let row = provenance
        .signatures
        .iter()
        .find(|row| row.signature == signature)?;
    store.source_callable_type_query(row.signature)
}

/// Projects one real cached signature, including the hidden implementation.
/// This does not allocate a callable type or change the public call list.
pub(super) fn source_overload_signature_projection(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    signature: SignatureId,
) -> Option<super::callables::ValidatedSingleCallable> {
    if !matches!(
        validate_stored_source_overload(store, type_),
        StoredSourceOverloadValidation::Valid(_)
    ) {
        return None;
    }
    let row = store
        .source_overload_provenance(type_)?
        .signatures
        .iter()
        .find(|row| row.signature == signature)?;
    let record = store.signature(signature)?;
    let mut parameters = row
        .parameters
        .iter()
        .map(|parameter| parameter.call_type)
        .collect::<Vec<_>>();
    let rest_parameter = if record.has_rest_parameter() {
        Some(parameters.pop()?)
    } else {
        None
    };
    Some(super::callables::ValidatedSingleCallable {
        owner: type_,
        signature,
        parameters,
        rest_parameter,
        min_argument_count: usize::try_from(record.min_argument_count()).ok()?,
        return_type: Some(row.return_type),
        strict_variance_exempt: false,
    })
}

/// Pinned `getErasedSignature` for implementation compatibility only.
/// The real declaration signatures and their templates remain unchanged.
#[allow(clippy::too_many_lines)] // Validate the complete mapped row before publishing its cache.
pub(super) fn source_overload_compatibility_projection(
    store: &mut CanonicalTypeMapperStore,
    owner: TypeId,
    signature: SignatureId,
    array_targets: Option<CanonicalArrayTargets>,
    session: &mut InstantiationSession,
) -> Result<ValidatedSingleCallable, RelationUnavailable> {
    let invalid = || RelationUnavailable::MalformedFunctionType(owner);
    let original =
        source_overload_signature_projection(store, owner, signature).ok_or_else(invalid)?;
    let original_record = store.signature(signature).ok_or_else(invalid)?;
    let sources = original_record.type_parameters().to_vec();
    if sources.is_empty() {
        return Ok(original);
    }
    let original_parameters = original_record.parameters().to_vec();
    let declaration = original_record.declaration();
    let flags = original_record.flags() & SignatureFlags::PROPAGATING_FLAGS;
    let minimum = original_record.min_argument_count();
    let any = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?
        .any_type;
    let targets = vec![any; sources.len()];
    let limit_mark = session.limit_event_mark();
    let mut types = Vec::with_capacity(original.parameters.len() + 1);
    for type_ in original
        .parameters
        .iter()
        .copied()
        .chain(original.return_type)
    {
        types.push(
            instantiate_type_with_vector_and_session(
                store,
                type_,
                &sources,
                &targets,
                array_targets,
                session,
            )
            .map_err(|_| RelationUnavailable::StructuralRelation {
                source: owner,
                target: owner,
                relation: RelationKind::Assignable,
            })?,
        );
    }
    if session.limit_event_occurred_since(limit_mark) {
        return Err(RelationUnavailable::StructuralRelation {
            source: owner,
            target: owner,
            relation: RelationKind::Assignable,
        });
    }
    if types.len() != original.parameters.len() + 1 {
        return Err(invalid());
    }
    let returned = types.pop().ok_or_else(invalid)?;
    let cached = store.source_overload_erased_signature(signature);
    let erased = if let Some(cached) = cached {
        cached
    } else {
        if !store.try_reserve_source_overload_erased_signatures(1) || !store.try_reserve_mappers(1)
        {
            return Err(RelationUnavailable::UnionValidationCapacity(owner));
        }
        let mapper = store
            .new_type_mapper(sources.clone(), targets.clone())
            .ok_or_else(invalid)?;
        store
            .instantiate_signature_ex(signature, mapper, true)
            .map_err(|error| match error {
                super::signatures::SignatureInstantiationError::Capacity(_) => {
                    RelationUnavailable::UnionValidationCapacity(owner)
                }
                _ => invalid(),
            })?
    };
    let record = store.signature(erased).ok_or_else(invalid)?;
    let mapper = record.mapper().ok_or_else(invalid)?;
    if record.target() != Some(signature)
        || record.declaration() != declaration
        || record.flags() != flags
        || record.min_argument_count() != minimum
        || !record.type_parameters().is_empty()
        || record.this_parameter().is_some()
        || record.resolved_type_predicate().is_some()
        || record.isolated_signature_type().is_some()
        || record.composite().is_some()
        || record.parameters().len() != original_parameters.len()
        || store.type_mapper_has_exact_endpoints(mapper, &sources, &targets) != Some(true)
        || record
            .resolved_return_type()
            .is_some_and(|value| value != returned)
        || cached.is_some() && record.resolved_return_type() != Some(returned)
    {
        return Err(invalid());
    }
    let parameters = record.parameters().to_vec();
    let mut publications = Vec::new();
    for ((source, parameter), type_) in original_parameters.iter().zip(&parameters).zip(&types) {
        if source == parameter {
            if store
                .value_symbol_links(*source)
                .and_then(|links| links.resolved_type)
                != Some(*type_)
            {
                return Err(invalid());
            }
            continue;
        }
        let source_record = store.symbol(*source).ok_or_else(invalid)?;
        let parameter_record = store.symbol(*parameter).ok_or_else(invalid)?;
        let links = store.value_symbol_links(*parameter).ok_or_else(invalid)?;
        let expected = ValueSymbolLinks {
            resolved_type: links.resolved_type,
            target: Some(*source),
            mapper: Some(mapper),
            ..ValueSymbolLinks::default()
        };
        if parameter_record.flags() != source_record.flags() | SymbolFlags::TRANSIENT
            || parameter_record.check_flags() != CheckFlags::INSTANTIATED
            || parameter_record.name() != source_record.name()
            || parameter_record.declarations() != source_record.declarations()
            || parameter_record.value_declaration() != source_record.value_declaration()
            || parameter_record.parent() != source_record.parent()
            || parameter_record.members().is_some()
            || parameter_record.exports().is_some()
            || parameter_record.export_symbol().is_some()
            || store.get_merged_symbol(*parameter) != Some(*parameter)
            || *links != expected
            || links.resolved_type.is_some_and(|value| value != *type_)
            || cached.is_some() && links.resolved_type != Some(*type_)
        {
            return Err(invalid());
        }
        if links.resolved_type.is_none() {
            publications.push((
                *parameter,
                ValueSymbolLinks {
                    resolved_type: Some(*type_),
                    ..expected
                },
            ));
        }
    }
    for (parameter, links) in publications {
        if !store.set_value_symbol_links(parameter, links) {
            return Err(invalid());
        }
    }
    if cached.is_none()
        && (!store.set_signature_resolved_return_type(erased, Some(returned))
            || !store.set_source_overload_erased_signature(signature, erased))
    {
        return Err(invalid());
    }
    Ok(ValidatedSingleCallable {
        owner,
        signature: erased,
        parameters: types,
        rest_parameter: None,
        min_argument_count: original.min_argument_count,
        return_type: Some(returned),
        strict_variance_exempt: original.strict_variance_exempt,
    })
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData};
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::parse_source_file;

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
        SourceCheckError, TypeNodeLinks, bootstrap::UnionReduction, signatures::TypePredicateKind,
    };

    fn generic_jsdoc_context(
        parsed: &ts_parser::ParseResult,
        file: FileId,
    ) -> CanonicalCheckerContext<'_> {
        assert!(parsed.diagnostics.is_empty());
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/generic-overload-ownership.js\""),
                    CanonicalSourceLanguage::JavaScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_javascript_declaration_slice(&parsed.arena, file)
            .unwrap();
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![(file, &parsed.arena)],
            CanonicalCheckerOptions {
                no_emit: true,
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap()
    }

    fn generic_jsdoc_source() -> ts_parser::ParseResult {
        ts_parser::parse_javascript_source_file(concat!(
            "/** @template T @param {T} value @returns {T}\n",
            " * @overload @param {T} value @returns {T}\n",
            " * @overload @param {T} value @param {number} count @returns {T} */\n",
            "function keep(value) { return value; }\n",
        ))
    }

    #[test]
    fn jsdoc_generic_rows_keep_query_owners_and_reuse_compatibility_signatures() {
        let parsed = generic_jsdoc_source();
        let file = FileId::new(8_227);
        for query_first in [false, true] {
            let mut context = generic_jsdoc_context(&parsed, file);
            let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data
            else {
                unreachable!()
            };
            let first = NodeRef::new(parsed.arena.id(), file, source.statements.nodes[0]);
            let early = if query_first {
                let NodeData::FunctionDeclaration(function) =
                    &parsed.arena.get(first.node).unwrap().data
                else {
                    unreachable!()
                };
                Some(
                    context
                        .get_type_from_type_node(NodeRef::new(
                            first.arena,
                            first.file,
                            function.type_.unwrap(),
                        ))
                        .unwrap(),
                )
            } else {
                None
            };
            context.check_source_file(file).unwrap();
            assert!(context.diagnostics().is_empty());
            let owner = context.file(file).unwrap().1.symbol(first).unwrap();
            let callable = context
                .store()
                .source_overload_type_for_owner(owner)
                .unwrap();
            let rows = context
                .store()
                .source_overload_provenance(callable)
                .unwrap()
                .signatures
                .clone();
            assert_eq!(rows.len(), 3);
            if let Some(early) = early {
                assert_eq!(early, rows[0].type_parameters[0].type_parameter);
            }
            let parameters = rows
                .iter()
                .map(|row| row.type_parameters[0].type_parameter)
                .collect::<HashSet<_>>();
            assert_eq!(parameters.len(), 3);
            let any = context.store().intrinsic_bootstrap().unwrap().any_type;
            for row in &rows {
                let evidence = context
                    .store()
                    .source_callable_type_query(row.signature)
                    .unwrap();
                assert!(evidence.is_exact(context.store()));
                assert_eq!(evidence.callable().declaration, row.declaration);
                assert_eq!(row.return_type, row.type_parameters[0].type_parameter);
                assert_ne!(row.return_type, any);
                let erased = context
                    .store()
                    .source_overload_erased_signature(row.signature)
                    .unwrap();
                let record = context.store().signature(erased).unwrap();
                assert_eq!(record.target(), Some(row.signature));
                assert_eq!(record.resolved_return_type(), Some(any));
                assert!(record.type_parameters().is_empty());
                assert_eq!(
                    context.store().cached_signatures_contain(erased),
                    Some(true)
                );
            }
            let before = (
                context.store().type_len(),
                context.store().symbol_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
            );
            for _ in 0..2 {
                context.recheck_source_file(file).unwrap();
                assert!(matches!(
                    validate_stored_source_overload(context.store(), callable),
                    StoredSourceOverloadValidation::Valid(_)
                ));
                assert_eq!(
                    context
                        .store()
                        .source_overload_provenance(callable)
                        .unwrap()
                        .signatures,
                    rows
                );
                assert_eq!(
                    before,
                    (
                        context.store().type_len(),
                        context.store().symbol_len(),
                        context.store().signature_len(),
                        context.store().mapper_len(),
                    )
                );
            }
        }
    }

    #[test]
    fn jsdoc_generic_rows_reject_cross_row_query_and_compatibility_cache_changes() {
        let parsed = generic_jsdoc_source();
        let file = FileId::new(8_228);
        let mut context = generic_jsdoc_context(&parsed, file);
        context.check_source_file(file).unwrap();
        let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data
        else {
            unreachable!()
        };
        let first = NodeRef::new(parsed.arena.id(), file, source.statements.nodes[0]);
        let owner = context.file(file).unwrap().1.symbol(first).unwrap();
        let callable = context
            .store()
            .source_overload_type_for_owner(owner)
            .unwrap();
        let rows = context
            .store()
            .source_overload_provenance(callable)
            .unwrap()
            .signatures
            .clone();
        let evidence = context
            .store_mut_for_test()
            .replace_source_callable_type_query_for_test(rows[0].signature, None)
            .unwrap();
        context
            .store_mut_for_test()
            .replace_source_callable_type_query_for_test(
                rows[0].signature,
                Some(Arc::clone(&evidence)),
            );
        let original = context
            .store_mut_for_test()
            .replace_source_callable_type_query_for_test(rows[1].signature, Some(evidence));
        assert_eq!(
            validate_stored_source_overload(context.store(), callable),
            StoredSourceOverloadValidation::Malformed
        );
        context
            .store_mut_for_test()
            .replace_source_callable_type_query_for_test(rows[1].signature, original);
        assert!(matches!(
            validate_stored_source_overload(context.store(), callable),
            StoredSourceOverloadValidation::Valid(_)
        ));

        let erased = context
            .store()
            .source_overload_erased_signature(rows[0].signature)
            .unwrap();
        let wrong = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(
            context
                .store_mut_for_test()
                .set_signature_resolved_return_type(erased, Some(wrong))
        );
        let mut session =
            InstantiationSession::new(crate::semantic::instantiate::InstantiationLimits::default());
        assert_eq!(
            source_overload_compatibility_projection(
                context.store_mut_for_test(),
                callable,
                rows[0].signature,
                None,
                &mut session,
            ),
            Err(RelationUnavailable::MalformedFunctionType(callable))
        );
        assert_eq!(
            context
                .store()
                .signature(rows[0].signature)
                .unwrap()
                .resolved_return_type(),
            Some(rows[0].return_type)
        );
    }

    fn namespace_overload_context(
        parsed: &ts_parser::ParseResult,
        file: FileId,
        declaration_file: bool,
    ) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/namespace-overloads.d.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    declaration_file,
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

    fn namespace_overload_nodes(
        parsed: &ts_parser::ParseResult,
        file: FileId,
    ) -> (NodeRef, Vec<NodeRef>) {
        let namespace = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ModuleDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let mut declarations = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration).then_some((
                    record.range.start,
                    NodeRef::new(parsed.arena.id(), file, node),
                ))
            })
            .collect::<Vec<_>>();
        declarations.sort_by_key(|(start, _)| *start);
        (
            namespace,
            declarations
                .into_iter()
                .map(|(_, declaration)| declaration)
                .collect(),
        )
    }

    #[test]
    fn ambient_namespace_predicate_overloads_retain_generic_and_assertion_ownership() {
        let source = concat!(
            "declare namespace Guards { ",
            "function select<Value>(value: Value): value is Value; ",
            "function select(value: unknown): value is string; ",
            "function select(value: unknown): asserts value is string; ",
            "}",
        );
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_550);
        let context = namespace_overload_context(&parsed, file, true);
        let (namespace, declarations) = namespace_overload_nodes(&parsed, file);
        let (_, bound) = context.file(file).unwrap();
        let namespace_symbol = bound.symbol(namespace).unwrap();
        let owner = bound.symbol(declarations[0]).unwrap();
        let host = DeclaredTypeHost::new([(&parsed.arena, bound)]).unwrap();
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().type_predicate_len(),
            context.store().checker_link_allocated_lengths(),
        );

        let plan = plan_source_namespace_ambient_overload_group(
            context.store(),
            &host,
            (namespace, namespace_symbol),
            owner,
            &declarations,
        )
        .unwrap();
        assert_eq!(plan.declarations.len(), 3);
        assert_eq!(plan.declarations[0].type_parameters.len(), 1);
        assert_eq!(
            plan.declarations
                .iter()
                .map(|declaration| {
                    let predicate = declaration.type_predicate.unwrap();
                    assert_eq!(predicate.owner, declaration.declaration);
                    assert_eq!(predicate.parameter_index, 0);
                    assert_eq!(predicate.parameter_symbol, declaration.parameters[0].symbol);
                    predicate.kind
                })
                .collect::<Vec<_>>(),
            [
                TypePredicateKind::Identifier,
                TypePredicateKind::Identifier,
                TypePredicateKind::AssertsIdentifier,
            ],
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().type_predicate_len(),
                context.store().checker_link_allocated_lengths(),
            ),
            before,
        );
    }

    #[test]
    fn ambient_namespace_overloads_retain_implicit_exports_generics_and_rest() {
        for (index, source) in [
            concat!(
                "declare namespace React { ",
                "function createFactory(value: string): string; ",
                "function createFactory<T extends object>(value: T): T; ",
                "function createFactory(...children: string[]): string; ",
                "}",
            ),
            concat!(
                "declare module 'react' { ",
                "export function createFactory(value: string): string; ",
                "export function createFactory<T extends object>(value: T): T; ",
                "export function createFactory(...children: string[]): string; ",
                "}",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(2_540 + u32::try_from(index).unwrap());
            let context = namespace_overload_context(&parsed, file, true);
            let (namespace, declarations) = namespace_overload_nodes(&parsed, file);
            let (_, bound) = context.file(file).unwrap();
            let namespace_symbol = bound
                .symbol(namespace)
                .and_then(|symbol| context.store().get_merged_symbol(symbol))
                .unwrap();
            let owner = bound.symbol(declarations[0]).unwrap();
            let local = bound.local_symbol(declarations[0]).unwrap();
            let host = DeclaredTypeHost::new([(&parsed.arena, bound)]).unwrap();
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
                context.store().source_callable_provenance_lengths(),
            );

            let first = plan_source_namespace_ambient_overload_group(
                context.store(),
                &host,
                (namespace, namespace_symbol),
                owner,
                &declarations,
            )
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            let second = plan_source_namespace_ambient_overload_group(
                context.store(),
                &host,
                (namespace, namespace_symbol),
                owner,
                &declarations,
            )
            .unwrap();

            assert_eq!(first, second, "{source}");
            assert_eq!(first.namespace, namespace_symbol, "{source}");
            assert_eq!(first.owner_symbol, owner, "{source}");
            assert_eq!(first.export_local, local, "{source}");
            assert_eq!(first.declarations.len(), 3, "{source}");
            assert_eq!(first.declarations[1].type_parameters.len(), 1, "{source}");
            assert!(
                first.declarations[1].type_parameters[0]
                    .constraint
                    .is_some()
            );
            assert!(first.declarations[2].parameters[0].rest, "{source}");
            assert_eq!(first.annotations().count(), 7, "{source}");
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                    context.store().source_callable_provenance_lengths(),
                ),
                before,
                "{source}",
            );
            assert!(context.store().value_symbol_links(owner).is_none());
            assert!(context.store().value_symbol_links(local).is_none());
        }
    }

    #[test]
    fn ambient_namespace_overloads_preserve_noncontiguous_react_groups() {
        for (index, source) in [
            concat!(
                "declare namespace React { ",
                "function createRef<T>(): T; ",
                "interface Separator { value: string; } ",
                "function forwardRef<T, P = {}>(value: T): P; ",
                "type Between = number; ",
                "function createRef<T>(): T; ",
                "interface AnotherSeparator {} ",
                "function forwardRef<T, P = {}>(value: T): P; ",
                "}",
            ),
            concat!(
                "declare module 'react' { ",
                "export = React; ",
                "namespace React { ",
                "function createRef<T>(): T; ",
                "interface Separator { value: string; } ",
                "function forwardRef<T, P = {}>(value: T): P; ",
                "type Between = number; ",
                "function createRef<T>(): T; ",
                "interface AnotherSeparator {} ",
                "function forwardRef<T, P = {}>(value: T): P; ",
                "} }",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(2_544 + u32::try_from(index).unwrap());
            let context = namespace_overload_context(&parsed, file, true);
            let namespace = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    let NodeData::ModuleDeclaration(module) = &record.data else {
                        return None;
                    };
                    let NodeData::Identifier(name) = &parsed.arena.get(module.name)?.data else {
                        return None;
                    };
                    (name.text == "React").then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
            let (_, bound) = context.file(file).unwrap();
            let namespace_symbol = bound
                .symbol(namespace)
                .and_then(|symbol| context.store().get_merged_symbol(symbol))
                .unwrap();
            let exports = context
                .store()
                .symbol(namespace_symbol)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| context.store().symbol_table(exports))
                .unwrap();
            let host = DeclaredTypeHost::new([(&parsed.arena, bound)]).unwrap();
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().checker_link_allocated_lengths(),
            );

            for name in ["createRef", "forwardRef"] {
                let owner = exports
                    .get_source(name)
                    .and_then(|symbol| context.store().get_merged_symbol(symbol))
                    .unwrap();
                let declarations = context
                    .store()
                    .symbol(owner)
                    .and_then(ts_binder::semantic::Symbol::declarations)
                    .unwrap();
                assert_eq!(declarations.len(), 2, "{name}: {source}");
                let first = plan_source_namespace_ambient_overload_group(
                    context.store(),
                    &host,
                    (namespace, namespace_symbol),
                    owner,
                    declarations,
                )
                .unwrap_or_else(|error| panic!("{name}: {source}: {error:?}"));
                let second = plan_source_namespace_ambient_overload_group(
                    context.store(),
                    &host,
                    (namespace, namespace_symbol),
                    owner,
                    declarations,
                )
                .unwrap();

                assert_eq!(first, second, "{name}: {source}");
                assert_eq!(first.declarations.len(), 2, "{name}: {source}");
                assert_eq!(
                    first
                        .declarations
                        .iter()
                        .map(|declaration| declaration.type_parameters.len())
                        .collect::<Vec<_>>(),
                    if name == "createRef" {
                        vec![1, 1]
                    } else {
                        vec![2, 2]
                    },
                    "{name}: {source}",
                );
                assert!(context.store().value_symbol_links(owner).is_none());
            }

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().signature_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before,
                "{source}",
            );
        }
    }

    #[test]
    fn namespace_overloads_classify_unsupported_signatures_without_cache_failures() {
        for (index, source) in [
            concat!(
                "declare namespace React { ",
                "function select(value: string,): string; ",
                "function select(value: number): number; ",
                "}",
            ),
            concat!(
                "declare namespace React { ",
                "function select(this: object, value: string): string; ",
                "function select(value: number): number; ",
                "}",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(2_546 + u32::try_from(index).unwrap());
            let context = namespace_overload_context(&parsed, file, true);
            let (namespace, declarations) = namespace_overload_nodes(&parsed, file);
            let (_, bound) = context.file(file).unwrap();
            let namespace_symbol = bound.symbol(namespace).unwrap();
            let owner = bound.symbol(declarations[0]).unwrap();
            let host = DeclaredTypeHost::new([(&parsed.arena, bound)]).unwrap();

            assert!(
                matches!(
                    plan_source_namespace_ambient_overload_group(
                        context.store(),
                        &host,
                        (namespace, namespace_symbol),
                        owner,
                        &declarations,
                    ),
                    Err(SourceOverloadError::Unsupported(_))
                ),
                "{source}",
            );
        }
    }

    #[test]
    fn ambient_namespace_overloads_reject_reordered_groups_and_poisoned_owners() {
        let source = concat!(
            "declare namespace React { ",
            "function createFactory(value: string): string; ",
            "function createFactory(value: number): number; ",
            "}",
        );
        let parsed = parse_source_file(source);
        let file = FileId::new(2_542);
        let mut context = namespace_overload_context(&parsed, file, true);
        let (namespace, declarations) = namespace_overload_nodes(&parsed, file);
        let (_, bound) = context.file(file).unwrap();
        let namespace_symbol = bound.symbol(namespace).unwrap();
        let owner = bound.symbol(declarations[0]).unwrap();
        {
            let host = DeclaredTypeHost::new([(&parsed.arena, bound)]).unwrap();
            assert!(matches!(
                plan_source_namespace_ambient_overload_group(
                    context.store(),
                    &host,
                    (namespace, namespace_symbol),
                    owner,
                    &[declarations[1], declarations[0]],
                ),
                Err(SourceOverloadError::Invariant(
                    SourceOverloadInvariant::Group(_)
                )),
            ));
            assert!(matches!(
                plan_source_namespace_ambient_overload_group(
                    context.store(),
                    &host,
                    (namespace, namespace_symbol),
                    owner,
                    &declarations[..1],
                ),
                Err(SourceOverloadError::Invariant(
                    SourceOverloadInvariant::Group(_)
                )),
            ));
        }

        let wrong = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(context.store_mut_for_test().set_value_symbol_links(
            owner,
            ValueSymbolLinks {
                resolved_type: Some(wrong),
                ..ValueSymbolLinks::default()
            },
        ));
        let (_, bound) = context.file(file).unwrap();
        let host = DeclaredTypeHost::new([(&parsed.arena, bound)]).unwrap();
        assert!(matches!(
            plan_source_namespace_ambient_overload_group(
                context.store(),
                &host,
                (namespace, namespace_symbol),
                owner,
                &declarations,
            ),
            Err(SourceOverloadError::Invariant(
                SourceOverloadInvariant::Cache(_)
            )),
        ));
    }

    #[test]
    fn namespace_overloads_classify_poisoned_signature_links_as_cache_errors() {
        let parsed = parse_source_file(concat!(
            "declare namespace React { ",
            "function createRef<T>(): T; ",
            "function createRef<T>(): T; ",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(2_548);
        let mut context = namespace_overload_context(&parsed, file, true);
        let (namespace, declarations) = namespace_overload_nodes(&parsed, file);
        let (_, bound) = context.file(file).unwrap();
        let namespace_symbol = bound.symbol(namespace).unwrap();
        let owner = bound.symbol(declarations[0]).unwrap();
        assert!(context.store_mut_for_test().set_signature_links(
            declarations[1],
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolving,
                ..SignatureLinks::default()
            },
        ));
        let (_, bound) = context.file(file).unwrap();
        let host = DeclaredTypeHost::new([(&parsed.arena, bound)]).unwrap();

        assert!(matches!(
            plan_source_namespace_ambient_overload_group(
                context.store(),
                &host,
                (namespace, namespace_symbol),
                owner,
                &declarations,
            ),
            Err(SourceOverloadError::Invariant(SourceOverloadInvariant::Cache(node)))
                if node == declarations[1],
        ));
    }

    #[test]
    fn namespace_overloads_require_declaration_file_ambientness() {
        let source = concat!(
            "declare namespace React { ",
            "function createFactory(value: string): string; ",
            "function createFactory(value: number): number; ",
            "}",
        );
        let parsed = parse_source_file(source);
        let file = FileId::new(2_543);
        let context = namespace_overload_context(&parsed, file, false);
        let (namespace, declarations) = namespace_overload_nodes(&parsed, file);
        let (_, bound) = context.file(file).unwrap();
        let namespace_symbol = bound.symbol(namespace).unwrap();
        let owner = bound.symbol(declarations[0]).unwrap();
        let host = DeclaredTypeHost::new([(&parsed.arena, bound)]).unwrap();

        assert!(matches!(
            plan_source_namespace_ambient_overload_group(
                context.store(),
                &host,
                (namespace, namespace_symbol),
                owner,
                &declarations,
            ),
            Err(SourceOverloadError::Unsupported(node)) if node == declarations[0],
        ));
    }

    #[test]
    fn later_bad_callable_provider_preflights_before_overload_publication() {
        let ready = concat!(
            "declare function ready(value: number): number;\n",
            "declare function ready(value: string): string;\n",
        );
        for (index, source) in [
            format!(
                "{ready}{}",
                concat!(
                    "declare function bad(",
                    "this: object, value: number",
                    "): number;\n",
                )
            ),
            format!(
                "{ready}{}",
                concat!(
                    "const bad = (",
                    "{ value }: { value: number }",
                    "): number => 1;\n",
                )
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(&source);
            assert!(parsed.diagnostics.is_empty());
            let file = FileId::new(2_494 + u32::try_from(index).unwrap());
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!(
                            "\"/project/overload-provider-boundary-{index}.ts\""
                        )),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
            let mut context = CanonicalCheckerContext::new(
                binder.finish(),
                [(file, &parsed.arena)].into_iter().collect(),
                CanonicalCheckerOptions::default(),
            )
            .unwrap();
            let mut declarations = parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    matches!(&record.data, NodeData::FunctionDeclaration(_)).then_some((
                        record.range.start,
                        NodeRef::new(parsed.arena.id(), file, node),
                    ))
                })
                .collect::<Vec<_>>();
            declarations.sort_by_key(|(start, _)| *start);
            let [(_, first), (_, second), ..] = declarations.as_slice() else {
                panic!("fixture must retain the ordered overload group")
            };
            let ready = [*first, *second];
            let owner = context
                .file(file)
                .unwrap()
                .1
                .symbol(*first)
                .and_then(|symbol| context.store().get_merged_symbol(symbol))
                .unwrap();
            let before = (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().source_callable_provenance_lengths(),
            );

            for _ in 0..2 {
                assert!(matches!(
                    context.check_source_file(file),
                    Err(SourceCheckError::Unsupported(_))
                ));
                assert_eq!(
                    (
                        context.store().type_len(),
                        context.store().signature_len(),
                        context.store().source_callable_provenance_lengths(),
                    ),
                    before
                );
                assert!(context.store().value_symbol_links(owner).is_none());
                assert!(
                    context
                        .store()
                        .source_overload_type_for_owner(owner)
                        .is_none()
                );
                assert!(
                    !context
                        .store()
                        .source_overload_provenance_claims(owner, ready.as_slice())
                );
                assert!(ready.iter().all(|declaration| {
                    context.store().signature_links(*declaration).is_none()
                        && context
                            .store()
                            .source_overload_type_for_declaration(*declaration)
                            .is_none()
                }));
                assert!(declarations.iter().all(|(_, declaration)| {
                    context.store().signature_links(*declaration).is_none()
                }));
            }
        }
    }

    #[test]
    fn literal_signature_flag_poison_rejects_warm_recheck_before_call_publication() {
        let parsed = parse_source_file(concat!(
            "declare function f(value: number): 'broad';\n",
            "declare function f(value: 1): 'literal';\n",
            "const result: 'literal' = f(1);\n",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(2_497);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/overload-flag-poison.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let declaration =
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(&record.data, NodeData::FunctionDeclaration(_))
                        .then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
        let call = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(&record.data, NodeData::CallExpression(_)).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();

        context.check_source_file(file).unwrap();

        let owner = context
            .file(file)
            .unwrap()
            .1
            .symbol(declaration)
            .and_then(|symbol| context.store().get_merged_symbol(symbol))
            .unwrap();
        let callable = context
            .store()
            .source_overload_type_for_owner(owner)
            .unwrap();
        let provenance = context
            .store()
            .source_overload_provenance(callable)
            .unwrap();
        let [broad, literal] = provenance.signatures.as_ref() else {
            panic!("fixture must retain two overload signatures")
        };
        assert_eq!(broad.flags, SignatureFlags::NONE);
        assert_eq!(literal.flags, SignatureFlags::HAS_LITERAL_TYPES);
        assert_eq!(
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature()),
            Some(literal.signature)
        );
        let literal_signature = literal.signature;

        assert!(
            context
                .store_mut_for_test()
                .set_signature_flags(literal_signature, SignatureFlags::NONE)
        );
        assert!(
            context
                .store_mut_for_test()
                .set_signature_links(call, SignatureLinks::default())
        );
        assert!(
            context
                .store_mut_for_test()
                .set_type_node_links(call, TypeNodeLinks::default())
        );
        let before = (context.store().type_len(), context.store().signature_len());
        assert!(matches!(
            validate_stored_source_overload(context.store(), callable),
            StoredSourceOverloadValidation::Malformed
        ));

        assert!(matches!(
            context.recheck_source_file(file),
            Err(SourceCheckError::Function(_))
        ));

        assert_eq!(
            (context.store().type_len(), context.store().signature_len()),
            before
        );
        assert_eq!(
            context.store().signature_links(call),
            Some(&SignatureLinks::default())
        );
        assert_eq!(
            context.store().type_node_links(call),
            Some(&TypeNodeLinks::default())
        );
        assert_eq!(
            context
                .store()
                .signature(literal_signature)
                .unwrap()
                .flags(),
            SignatureFlags::NONE
        );
    }

    #[test]
    fn structured_poison_dirties_and_invalidates_a_warm_callable_union() {
        let parsed = parse_source_file(concat!(
            "declare function f(value: number): number;\n",
            "declare function f(value: string): string;\n",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(2_498);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/overload-union-poison.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
                ..CanonicalCheckerOptions::default()
            },
        )
        .unwrap();
        let declaration =
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    matches!(&record.data, NodeData::FunctionDeclaration(_))
                        .then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();

        context.check_source_file(file).unwrap();

        let owner = context
            .file(file)
            .unwrap()
            .1
            .symbol(declaration)
            .and_then(|symbol| context.store().get_merged_symbol(symbol))
            .unwrap();
        let callable = context
            .store()
            .source_overload_type_for_owner(owner)
            .unwrap();
        let first_signature = context
            .store()
            .source_overload_provenance(callable)
            .unwrap()
            .signatures[0]
            .signature;
        let (undefined, string, number) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.undefined_type,
                bootstrap.string_type,
                bootstrap.number_type,
            )
        };
        let callable_union = context
            .store_mut_for_test()
            .expression_union_type(&[callable, undefined], UnionReduction::Literal)
            .unwrap();
        assert_eq!(
            context
                .store_mut_for_test()
                .expression_union_type(&[callable, undefined], UnionReduction::Literal),
            Ok(callable_union),
        );
        let control_union = context
            .store_mut_for_test()
            .expression_union_type(&[string, number], UnionReduction::Literal)
            .unwrap();
        assert_eq!(
            context
                .store_mut_for_test()
                .expression_union_type(&[string, number], UnionReduction::Literal),
            Ok(control_union),
        );
        assert!(!context.store().union_cache_needs_validation);

        let scans = context.store().union_cache_validation_scan_count();
        assert!(context.store_mut_for_test().set_structured_type_members(
            callable,
            None,
            None,
            Some(vec![first_signature]),
            None,
            None,
        ));
        assert!(context.store().union_cache_needs_validation);
        assert!(matches!(
            validate_stored_source_overload(context.store(), callable),
            StoredSourceOverloadValidation::Malformed
        ));
        let validation = context
            .store_mut_for_test()
            .expression_union_type(&[string, number], UnionReduction::Literal);
        assert!(
            matches!(validation, Err(LiteralTypeCacheError::InvalidCachedUnion(type_)) if type_ == callable),
            "poisoned callable union returned {validation:?}; callable={callable:?}, union={callable_union:?}"
        );
        assert_eq!(
            context.store().union_cache_validation_scan_count(),
            scans + 1
        );
    }

    #[test]
    fn missing_reverse_map_poison_fails_closed_without_republication() {
        let parsed = parse_source_file(concat!(
            "declare function f(value: number): number;\n",
            "declare function f(value: string): string;\n",
        ));
        assert!(parsed.diagnostics.is_empty());
        let file = FileId::new(2_499);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/overload-poison.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let mut declarations = parsed
            .arena
            .iter()
            .filter_map(|(node, record)| {
                matches!(&record.data, NodeData::FunctionDeclaration(_)).then_some((
                    record.range.start,
                    NodeRef::new(parsed.arena.id(), file, node),
                ))
            })
            .collect::<Vec<_>>();
        declarations.sort_by_key(|(start, _)| *start);
        let declarations = declarations
            .into_iter()
            .map(|(_, declaration)| declaration)
            .collect::<Vec<_>>();

        context.check_source_file(file).unwrap();

        let owner = context
            .file(file)
            .unwrap()
            .1
            .symbol(declarations[0])
            .and_then(|symbol| context.store().get_merged_symbol(symbol))
            .unwrap();
        let callable = context
            .store()
            .source_overload_type_for_owner(owner)
            .unwrap();
        assert!(matches!(
            validate_stored_source_overload(context.store(), callable),
            StoredSourceOverloadValidation::Valid(_)
        ));
        assert_eq!(
            context
                .store_mut_for_test()
                .replace_source_overload_type_for_declaration_for_test(declarations[1], None,),
            Some(callable)
        );
        let before = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().relation_state_snapshot(),
            context.store().signature_links(declarations[0]).cloned(),
            context.store().signature_links(declarations[1]).cloned(),
        );

        assert!(matches!(
            context.recheck_source_file(file),
            Err(SourceCheckError::Function(_))
        ));

        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().relation_state_snapshot(),
                context.store().signature_links(declarations[0]).cloned(),
                context.store().signature_links(declarations[1]).cloned(),
            ),
            before
        );
        assert!(matches!(
            validate_stored_source_overload(context.store(), callable),
            StoredSourceOverloadValidation::Malformed
        ));
    }
}
