//! Source-owned identities for nongeneric declared constructor values.
//!
//! A value, its constructor interface, and each construct signature's return
//! have separate identities. Consumers own overload selection and heritage
//! checks. Preparing one signature does not resolve the interface's members.
//! Direct generic annotations need complete explicit arguments and a stored
//! source proof. Defaulted generic annotations are not supported here yet.

use ts_ast::{NodeData, NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, SemanticSymbolId, SymbolFlags};

#[cfg(test)]
mod tests;

use super::{
    CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, SignatureId, SymbolNodeLinks,
    TypeId, TypeNodeLinks, ValueSymbolLinks,
    declared::preflight_class_or_interface_reference,
    instantiate::InstantiationSession,
    object_members::{
        self, PlannedCallSignature, PropertyObjectError, PropertyObjectPlan,
        ResolvedCallSignatureTypes, interface_state, plan_interface,
    },
    type_nodes::CanonicalTypeQuery,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DeclaredConstructorValuePlan {
    value_symbol: SemanticSymbolId,
    value_declaration: NodeRef,
    value_annotation: NodeRef,
    owner: PropertyObjectPlan,
    construct_indexes: Box<[usize]>,
}

impl DeclaredConstructorValuePlan {
    pub(super) const fn value_symbol(&self) -> SemanticSymbolId {
        self.value_symbol
    }

    pub(super) const fn value_declaration(&self) -> NodeRef {
        self.value_declaration
    }

    pub(super) const fn value_annotation(&self) -> NodeRef {
        self.value_annotation
    }

    pub(super) const fn owner_symbol(&self) -> SemanticSymbolId {
        self.owner.symbol
    }

    pub(super) fn construct_declarations(&self) -> impl ExactSizeIterator<Item = NodeRef> + '_ {
        self.construct_indexes
            .iter()
            .map(|&index| self.owner.call_signatures[index].declaration)
    }

    fn signature(&self, declaration: NodeRef) -> Option<&PlannedCallSignature> {
        self.construct_indexes
            .iter()
            .map(|&index| &self.owner.call_signatures[index])
            .find(|signature| signature.declaration == declaration)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DeclaredConstructorValue {
    value_symbol: SemanticSymbolId,
    constructor_type: TypeId,
}

impl DeclaredConstructorValue {
    pub(super) const fn value_symbol(self) -> SemanticSymbolId {
        self.value_symbol
    }

    pub(super) const fn constructor_type(self) -> TypeId {
        self.constructor_type
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DeclaredConstructSignature {
    value: DeclaredConstructorValue,
    declaration: NodeRef,
    signature: SignatureId,
    return_type: TypeId,
}

impl DeclaredConstructSignature {
    pub(super) const fn value(self) -> DeclaredConstructorValue {
        self.value
    }

    pub(super) const fn declaration(self) -> NodeRef {
        self.declaration
    }

    pub(super) const fn signature(self) -> SignatureId {
        self.signature
    }

    pub(super) const fn return_type(self) -> TypeId {
        self.return_type
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DeclaredConstructorValueError {
    Unsupported { node: NodeRef, kind: SyntaxKind },
    InvalidValue(SemanticSymbolId),
    InvalidSignature(NodeRef),
    Capacity(NodeRef),
    DeclaredType(DeclaredTypeError),
    Members(PropertyObjectError),
}

impl From<DeclaredTypeError> for DeclaredConstructorValueError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<PropertyObjectError> for DeclaredConstructorValueError {
    fn from(error: PropertyObjectError) -> Self {
        Self::Members(error)
    }
}

fn unsupported(node: NodeRef, kind: SyntaxKind) -> DeclaredConstructorValueError {
    DeclaredConstructorValueError::Unsupported { node, kind }
}

/// Plans the declaration, not an expression that happens to use its value.
pub(super) fn plan_declared_constructor_value(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    value_symbol: SemanticSymbolId,
) -> Result<DeclaredConstructorValuePlan, DeclaredConstructorValueError> {
    let invalid = || DeclaredConstructorValueError::InvalidValue(value_symbol);
    let value = store.symbol(value_symbol).ok_or_else(invalid)?;
    let declaration = value.value_declaration().ok_or_else(invalid)?;
    let record = host.node(declaration).ok_or_else(invalid)?;
    let NodeData::VariableDeclaration(variable) = &record.data else {
        return Err(unsupported(declaration, record.kind));
    };
    let bound = host.bound_file(declaration).ok_or_else(invalid)?;
    let list = record
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(invalid)?;
    let list_record = host.node(list).ok_or_else(invalid)?;
    let NodeData::VariableDeclarationList(declarations) = &list_record.data else {
        return Err(invalid());
    };
    let statement = list_record
        .parent
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(invalid)?;
    let statement_record = host.node(statement).ok_or_else(invalid)?;
    let NodeData::VariableStatement(statement_data) = &statement_record.data else {
        return Err(invalid());
    };
    let name = NodeRef::new(declaration.arena, declaration.file, variable.name);
    let name_record = host.node(name).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported(name, name_record.kind));
    };
    let annotation = variable
        .type_
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
        .ok_or_else(|| unsupported(declaration, record.kind))?;
    let annotation_record = host.node(annotation).ok_or_else(invalid)?;
    let ambient_file = bound
        .source_facts()
        .is_some_and(|facts| facts.is_declaration_file() && !facts.is_javascript_file());
    let declared = match statement_data.modifiers.as_ref() {
        None => false,
        Some(modifiers) => {
            let [modifier] = modifiers.list.nodes.as_slice() else {
                return Err(unsupported(statement, statement_record.kind));
            };
            let modifier = NodeRef::new(statement.arena, statement.file, *modifier);
            if modifiers.flags.0 != 0
                || modifiers.list.has_trailing_comma
                || host.node(modifier).is_none_or(|record| {
                    record.kind != SyntaxKind::DeclareKeyword
                        || record.flags.0 != 0
                        || record.parent != Some(statement.node)
                        || !matches!(record.data, NodeData::Token(_))
                })
            {
                return Err(unsupported(statement, statement_record.kind));
            }
            true
        }
    };
    if !ambient_file && !declared {
        return Err(unsupported(declaration, record.kind));
    }
    let variable_flags = if list_record.flags.0 == 0 {
        SymbolFlags::FUNCTION_SCOPED_VARIABLE
    } else {
        SymbolFlags::BLOCK_SCOPED_VARIABLE
    };
    let expected_flags = variable_flags | (value.flags() & SymbolFlags::INTERFACE);
    if store.get_merged_symbol(value_symbol) != Some(value_symbol)
        || !store.source_merged_symbol_declarations_match(value_symbol)
        || value.flags().without(SymbolFlags::TRANSIENT) != expected_flags
        || value.check_flags() != CheckFlags::NONE
        || value.name().as_utf8() != Some(identifier.text.as_str())
        || value.parent().is_some()
        || value.exports().is_some()
        || value.export_symbol().is_some()
        || !value.flags().contains(SymbolFlags::INTERFACE) && value.members().is_some()
        || value.declarations().is_none_or(|declarations| {
            declarations
                .iter()
                .filter(|&&node| node == declaration)
                .count()
                != 1
                || declarations.iter().any(|&node| {
                    node != declaration
                        && store.source_node_kind(node) != Some(SyntaxKind::InterfaceDeclaration)
                })
        })
        || !host.symbol_matches(store, declaration, value_symbol)
        || record.kind != SyntaxKind::VariableDeclaration
        || record.flags.0 != 0
        || variable.initializer.is_some()
        || variable.exclamation_token.is_some()
        || variable.local_symbol.is_some()
        || variable.symbol.is_some()
        || variable.facts != 0
        || list_record.kind != SyntaxKind::VariableDeclarationList
        || !matches!(list_record.flags.0, 0..=2)
        || declarations.declarations.has_trailing_comma
        || !declarations.declarations.nodes.contains(&declaration.node)
        || statement_record.kind != SyntaxKind::VariableStatement
        || statement_record.flags.0 != 0
        || statement_record.parent != Some(bound.source_file().node)
        || statement_data.declaration_list != list.node
        || statement_data.flow_node.is_some()
        || statement_data.facts != 0
        || name_record.flags.0 != 0
        || name_record.parent != Some(declaration.node)
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
        || annotation_record.flags.0 != 0
        || annotation_record.parent != Some(declaration.node)
    {
        return Err(invalid());
    }

    let NodeData::TypeReferenceNode(reference) = &annotation_record.data else {
        return Err(unsupported(annotation, annotation_record.kind));
    };
    if reference.type_arguments.is_some() {
        return Err(unsupported(annotation, annotation_record.kind));
    }
    let type_name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
    let type_name_record = host.node(type_name).ok_or_else(invalid)?;
    let NodeData::Identifier(type_identifier) = &type_name_record.data else {
        return Err(unsupported(type_name, type_name_record.kind));
    };
    if type_name_record.flags.0 != 0
        || type_name_record.parent != Some(annotation.node)
        || type_identifier.flow_node.is_some()
        || type_identifier.text.is_empty()
    {
        return Err(invalid());
    }
    let owner_symbol = host
        .name_resolver_host(store)?
        .resolve_entity_name(type_name, SymbolFlags::TYPE)
        .map_err(|_| invalid())?
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(|| unsupported(annotation, annotation_record.kind))?;
    let owner_record = store.symbol(owner_symbol).ok_or_else(invalid)?;
    if !owner_record.flags().contains(SymbolFlags::INTERFACE)
        || owner_record
            .flags()
            .intersects(SymbolFlags::CLASS | SymbolFlags::TYPE_ALIAS)
    {
        return Err(unsupported(annotation, annotation_record.kind));
    }
    if preflight_class_or_interface_reference(store, host, owner_symbol, owner_record.flags())? != 0
    {
        return Err(unsupported(annotation, annotation_record.kind));
    }
    let owner = plan_interface(store, host, owner_symbol)?;
    if owner.heritage.is_some() {
        return Err(unsupported(owner.node, SyntaxKind::InterfaceDeclaration));
    }
    let mut construct_indexes = Vec::new();
    for (index, signature) in owner.call_signatures.iter().enumerate() {
        if signature.is_construct() {
            if !signature.type_parameters.is_empty()
                || signature.implicit_any_return
                || signature.type_predicate.is_some()
                || signature.parameters.iter().any(|parameter| parameter.implicit_any_rest)
                || host.node(signature.declaration).is_none_or(|record| {
                    !matches!(&record.data, NodeData::ConstructSignatureDeclaration(data)
                        if data.parameters.nodes.iter().all(|&node| {
                            let parameter = NodeRef::new(signature.declaration.arena, signature.declaration.file, node);
                            matches!(host.node(parameter).map(|record| &record.data), Some(NodeData::ParameterDeclaration(data)) if data.dot_dot_dot_token.is_none())
                        }))
                })
            {
                return Err(unsupported(signature.declaration, SyntaxKind::ConstructSignature));
            }
            construct_indexes.push(index);
        }
    }
    Ok(DeclaredConstructorValuePlan {
        value_symbol,
        value_declaration: declaration,
        value_annotation: annotation,
        owner,
        construct_indexes: construct_indexes.into_boxed_slice(),
    })
}

fn validate_plan(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &DeclaredConstructorValuePlan,
) -> Result<(), DeclaredConstructorValueError> {
    if plan_declared_constructor_value(store, host, plan.value_symbol())? == *plan {
        Ok(())
    } else {
        Err(DeclaredConstructorValueError::InvalidValue(
            plan.value_symbol,
        ))
    }
}

fn validate_ready_annotation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<(), DeclaredConstructorValueError> {
    let invalid = || DeclaredConstructorValueError::InvalidSignature(node);
    let record = host.node(node).ok_or_else(invalid)?;
    object_members::cached_constructor_interface_annotation(store, node).ok_or_else(invalid)?;
    if let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data {
        return validate_ready_annotation(
            store,
            host,
            NodeRef::new(node.arena, node.file, parenthesized.type_),
        );
    }
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return Ok(());
    };
    let name = NodeRef::new(node.arena, node.file, reference.type_name);
    let symbol = host
        .name_resolver_host(store)?
        .resolve_entity_name(name, SymbolFlags::TYPE)
        .map_err(|_| invalid())?
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .ok_or_else(invalid)?;
    validate_reference_name_cache(store, host, node, symbol)?;
    let type_ = store
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .ok_or_else(invalid)?;
    if store
        .symbol_node_links(node)
        .and_then(|links| links.resolved_symbol)
        != Some(symbol)
        || !store.source_direct_type_annotation_is_exact(node, type_)
    {
        return Err(invalid());
    }
    let owner = store.symbol(symbol).ok_or_else(invalid)?;
    if reference.type_arguments.is_none()
        && owner
            .flags()
            .intersects(SymbolFlags::CLASS | SymbolFlags::INTERFACE)
        && preflight_class_or_interface_reference(store, host, symbol, owner.flags())? == 0
        && store
            .declared_type_links(symbol)
            .and_then(|links| links.declared_type)
            != Some(type_)
    {
        return Err(invalid());
    }
    Ok(())
}

fn validate_reference_name_cache(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    annotation: NodeRef,
    symbol: SemanticSymbolId,
) -> Result<(), DeclaredConstructorValueError> {
    let invalid = || DeclaredConstructorValueError::InvalidSignature(annotation);
    let Some(NodeData::TypeReferenceNode(reference)) = host.node(annotation).map(|node| &node.data)
    else {
        return Err(invalid());
    };
    let name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
    if store
        .symbol_node_links(name)
        .and_then(|links| links.resolved_symbol)
        .is_some_and(|cached| cached != symbol)
    {
        return Err(invalid());
    }
    Ok(())
}

fn validate_partial_annotation_admission(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<(), DeclaredConstructorValueError> {
    let invalid = || DeclaredConstructorValueError::InvalidSignature(node);
    let record = host.node(node).ok_or_else(invalid)?;
    if let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data {
        return validate_partial_annotation_admission(
            store,
            host,
            NodeRef::new(node.arena, node.file, parenthesized.type_),
        );
    }
    let NodeData::TypeReferenceNode(reference) = &record.data else {
        return Ok(());
    };
    let name = NodeRef::new(node.arena, node.file, reference.type_name);
    if host
        .node(name)
        .is_none_or(|name| name.kind != SyntaxKind::Identifier)
    {
        return Err(unsupported(node, record.kind));
    }
    let symbol = host
        .name_resolver_host(store)?
        .resolve_entity_name(name, SymbolFlags::TYPE)
        .map_err(|_| invalid())?
        .and_then(|symbol| store.get_merged_symbol(symbol));
    if let Some(symbol) = symbol {
        let owner = store.symbol(symbol).ok_or_else(invalid)?;
        let declarations = owner.declarations().ok_or_else(invalid)?;
        let provided = reference
            .type_arguments
            .as_ref()
            .map_or(0, |arguments| arguments.nodes.len());
        for &declaration in declarations {
            if !host.symbol_matches(store, declaration, symbol) {
                return Err(invalid());
            }
            let parameters = match host.node(declaration).map(|node| &node.data) {
                Some(NodeData::TypeAliasDeclaration(alias)) => alias.type_parameters.as_ref(),
                Some(NodeData::InterfaceDeclaration(interface)) => {
                    interface.type_parameters.as_ref()
                }
                Some(NodeData::ClassDeclaration(class)) => class.type_parameters.as_ref(),
                _ => continue,
            };
            if parameters.is_some_and(|parameters| {
                provided < parameters.nodes.len()
                    && parameters.nodes[provided..].iter().all(|&parameter| {
                        matches!(host.node(NodeRef::new(declaration.arena, declaration.file, parameter)).map(|node| &node.data),
                            Some(NodeData::TypeParameterDeclaration(parameter)) if parameter.default_type.is_some())
                    })
            }) {
                return Err(unsupported(node, record.kind));
            }
        }
    }
    for &argument in reference
        .type_arguments
        .as_ref()
        .map_or(&[][..], |arguments| arguments.nodes.as_slice())
    {
        validate_partial_annotation_admission(
            store,
            host,
            NodeRef::new(node.arena, node.file, argument),
        )?;
    }
    Ok(())
}

/// Reads a complete value binding. An interface may still have lazy members.
pub(super) fn resolve_declared_constructor_value(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &DeclaredConstructorValuePlan,
) -> Result<Option<DeclaredConstructorValue>, DeclaredConstructorValueError> {
    validate_plan(store, host, plan)?;
    let invalid = || DeclaredConstructorValueError::InvalidValue(plan.value_symbol);
    validate_reference_name_cache(store, host, plan.value_annotation, plan.owner.symbol)
        .map_err(|_| invalid())?;
    let owner = store
        .declared_type_links(plan.owner_symbol())
        .and_then(|links| links.declared_type);
    if let Some(type_) = owner {
        interface_state(store, &plan.owner, type_)?;
    }
    let value = store
        .value_symbol_links(plan.value_symbol)
        .and_then(|links| links.resolved_type);
    let annotation = store
        .type_node_links(plan.value_annotation())
        .and_then(|links| links.resolved_type);
    let resolved_symbol = store
        .symbol_node_links(plan.value_annotation)
        .and_then(|links| links.resolved_symbol);
    if store
        .value_symbol_links(plan.value_symbol)
        .is_some_and(|links| {
            links
                != &ValueSymbolLinks {
                    resolved_type: value,
                    ..ValueSymbolLinks::default()
                }
        })
        || store
            .type_node_links(plan.value_annotation)
            .is_some_and(|links| {
                links
                    != &TypeNodeLinks {
                        resolved_type: annotation,
                        ..TypeNodeLinks::default()
                    }
            })
        || value.is_some_and(|type_| Some(type_) != owner)
        || annotation.is_some_and(|type_| Some(type_) != owner)
        || resolved_symbol.is_some_and(|symbol| symbol != plan.owner.symbol)
    {
        return Err(invalid());
    }
    Ok(match (owner, value, annotation, resolved_symbol) {
        (Some(constructor_type), Some(_), Some(_), Some(_)) => Some(DeclaredConstructorValue {
            value_symbol: plan.value_symbol,
            constructor_type,
        }),
        _ => None,
    })
}

/// Publishes only the declared value's type identity and annotation links.
#[allow(clippy::too_many_arguments)] // Both preparation operations keep the caller's query context.
pub(super) fn prepare_declared_constructor_value(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    _globals: &CanonicalGlobalTypes,
    _options: CanonicalCheckerOptions,
    _session: &mut InstantiationSession,
    _diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &DeclaredConstructorValuePlan,
) -> Result<DeclaredConstructorValue, DeclaredConstructorValueError> {
    if let Some(value) = resolve_declared_constructor_value(store, host, plan)? {
        return Ok(value);
    }
    if !store.try_reserve_value_symbol_links(1)
        || !store.try_reserve_type_node_links(1)
        || !store.try_reserve_symbol_node_links(1)
    {
        return Err(DeclaredConstructorValueError::Capacity(
            plan.value_declaration(),
        ));
    }
    let type_ = store.get_declared_type_of_symbol(host, plan.owner.symbol)?;
    interface_state(store, &plan.owner, type_)?;
    assert!(store.set_value_symbol_links(
        plan.value_symbol,
        ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        }
    ));
    assert!(store.set_type_node_links(
        plan.value_annotation,
        TypeNodeLinks {
            resolved_type: Some(type_),
            ..TypeNodeLinks::default()
        }
    ));
    assert!(store.set_symbol_node_links(
        plan.value_annotation,
        SymbolNodeLinks {
            resolved_symbol: Some(plan.owner.symbol),
        }
    ));
    resolve_declared_constructor_value(store, host, plan)?.ok_or(
        DeclaredConstructorValueError::InvalidValue(plan.value_symbol),
    )
}

/// Reads one original overload without resolving any other overload.
pub(super) fn resolve_declared_construct_signature(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &DeclaredConstructorValuePlan,
    declaration: NodeRef,
) -> Result<Option<DeclaredConstructSignature>, DeclaredConstructorValueError> {
    validate_plan(store, host, plan)?;
    let planned = plan
        .signature(declaration)
        .ok_or(DeclaredConstructorValueError::InvalidSignature(declaration))?;
    validate_partial_annotation_admission(store, host, planned.return_type)?;
    for parameter in &planned.parameters {
        validate_partial_annotation_admission(store, host, parameter.type_node)?;
    }
    let value = resolve_declared_constructor_value(store, host, plan)?;
    let Some(signature) =
        object_members::resolve_single_construct_signature(store, &plan.owner, planned)?
    else {
        return Ok(None);
    };
    let Some(value) = value else {
        return Ok(None);
    };
    let return_type = store
        .signature(signature)
        .and_then(super::signatures::Signature::resolved_return_type)
        .ok_or(DeclaredConstructorValueError::InvalidSignature(declaration))?;
    validate_ready_annotation(store, host, planned.return_type)?;
    for parameter in &planned.parameters {
        validate_ready_annotation(store, host, parameter.type_node)?;
    }
    Ok(Some(DeclaredConstructSignature {
        value,
        declaration,
        signature,
        return_type,
    }))
}

/// Resolves the requested annotations in the caller's session, then publishes
/// one original construct signature. No overload result is replaced or merged.
#[allow(clippy::too_many_arguments)] // The retained overload and caller query context are independent.
pub(super) fn prepare_declared_construct_signature(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &DeclaredConstructorValuePlan,
    declaration: NodeRef,
) -> Result<DeclaredConstructSignature, DeclaredConstructorValueError> {
    if let Some(signature) = resolve_declared_construct_signature(store, host, plan, declaration)? {
        return Ok(signature);
    }
    let planned = plan
        .signature(declaration)
        .ok_or(DeclaredConstructorValueError::InvalidSignature(declaration))?;
    prepare_declared_constructor_value(store, host, globals, options, session, diagnostics, plan)?;
    let mut parameter_types = Vec::with_capacity(planned.parameters.len());
    for parameter in &planned.parameters {
        let annotation = CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            globals,
            options,
            session,
            diagnostics,
        )?
        .get_type_from_type_node(parameter.type_node)?;
        parameter_types.push(object_members::prepare_declared_construct_parameter_type(
            store, planned, parameter, annotation,
        )?);
    }
    let return_type = CanonicalTypeQuery::new_with_global_types_and_session(
        store,
        host,
        globals,
        options,
        session,
        diagnostics,
    )?
    .get_type_from_type_node(planned.return_type)?;
    if object_members::cached_constructor_interface_annotation(store, planned.return_type)
        != Some(return_type)
    {
        return Err(unsupported(
            planned.return_type,
            host.node(planned.return_type)
                .map_or(SyntaxKind::Unknown, |node| node.kind),
        ));
    }
    validate_ready_annotation(store, host, planned.return_type)?;
    object_members::publish_single_construct_signature(
        store,
        &plan.owner,
        planned,
        &ResolvedCallSignatureTypes {
            parameter_types,
            return_type,
        },
    )?;
    resolve_declared_construct_signature(store, host, plan, declaration)?
        .ok_or(DeclaredConstructorValueError::InvalidSignature(declaration))
}
