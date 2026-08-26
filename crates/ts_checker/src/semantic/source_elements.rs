//! Exact read-only source integration for direct `receiver[index]` access.
//!
//! This is the dependency-closed expression prefix of pinned
//! `checkElementAccessExpression` plus `getPropertyTypeForIndexType`. It
//! supports canonical `any`, direct `Array<T>`/`ReadonlyArray<T>` references,
//! validated fixed tuple elements,
//! required own and shared union properties selected by string or number
//! literals, authenticated enum members and numeric reverse indices, primitive
//! string indexing, resolved anonymous string/number index signatures, finite
//! unions of valid literal keys, optional properties, and optional chains.
//! Authenticated evolving-array element assignments reuse the same index
//! validation. Other writes, generic indexed access types, and apparent/global
//! property lookup stay typed boundaries.

use std::collections::HashSet;

use ts_ast::{NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, InternalSymbolName, SemanticSymbolId, SymbolFlags, SymbolTableId};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    ArrayTypeError, CanonicalCheckerDiagnostic, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalGlobalTypes, CanonicalTypeFormatFlags,
    CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost, RelationUnavailable,
    SymbolNodeLinks, TypeDisplayUnavailable, TypeId, TypeNodeLinks, ValueSymbolLinks,
    array_types::CanonicalArrayTargets,
    bootstrap::{LiteralTypeCacheError, UnionReduction},
    enums,
    formatter::{
        type_to_string_with_host_and_flags, type_to_string_with_host_global_types_and_flags,
    },
    member_resolution::UnionPropertyError,
    object_members::{self, PropertyObjectState},
    source::PlannedExpression,
    source_callables::cached_annotation_identity,
    store::SourceNodeParent,
    type_nodes::CanonicalTypeQuery,
    type_records::{LiteralValue, StructuredTypeData, TypeCacheState, TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

/// Source element syntax or semantic families outside this exact read slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceElementUnsupported {
    Access(NodeRef),
    Receiver(NodeRef),
    Index(NodeRef),
    MemberCall(NodeRef),
    Write(NodeRef),
    IndexType(TypeId),
    OptionalProperty {
        node: NodeRef,
        property: SemanticSymbolId,
    },
    IndexSignatureSurface(TypeId),
}

/// Exact indexed-access planning or checking failure without a guessed type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceElementError {
    Unsupported(SourceElementUnsupported),
    InvalidCache(NodeRef),
    InvalidType(TypeId),
    Relation(RelationUnavailable),
    Array(ArrayTypeError),
    Declared(DeclaredTypeError),
    Literal(LiteralTypeCacheError),
    Display(TypeDisplayUnavailable),
    MissingDiagnostic(u32),
}

impl From<RelationUnavailable> for SourceElementError {
    fn from(error: RelationUnavailable) -> Self {
        Self::Relation(error)
    }
}

impl From<ArrayTypeError> for SourceElementError {
    fn from(error: ArrayTypeError) -> Self {
        Self::Array(error)
    }
}

impl From<DeclaredTypeError> for SourceElementError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::Declared(error)
    }
}

impl From<LiteralTypeCacheError> for SourceElementError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::Literal(error)
    }
}

impl From<TypeDisplayUnavailable> for SourceElementError {
    fn from(error: TypeDisplayUnavailable) -> Self {
        Self::Display(error)
    }
}

impl std::fmt::Display for SourceElementError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unsupported(error) => {
                write!(formatter, "source element access is unsupported: {error:?}")
            }
            Self::InvalidCache(node) => {
                write!(formatter, "source element cache is invalid at {node:?}")
            }
            Self::InvalidType(type_) => {
                write!(formatter, "source element type is invalid: {type_:?}")
            }
            Self::Relation(error) => error.fmt(formatter),
            Self::Array(error) => error.fmt(formatter),
            Self::Declared(error) => error.fmt(formatter),
            Self::Literal(error) => write!(formatter, "source element literal failed: {error:?}"),
            Self::Display(error) => error.fmt(formatter),
            Self::MissingDiagnostic(code) => {
                write!(formatter, "source element diagnostic TS{code} is missing")
            }
        }
    }
}

impl std::error::Error for SourceElementError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Relation(error) => Some(error),
            Self::Array(error) => Some(error),
            Self::Declared(error) => Some(error),
            Self::Display(error) => Some(error),
            Self::Unsupported(_)
            | Self::InvalidCache(_)
            | Self::InvalidType(_)
            | Self::Literal(_)
            | Self::MissingDiagnostic(_) => None,
        }
    }
}

/// Element-access syntax proven before either child is recursively planned.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DirectSourceElementSyntax {
    node: NodeRef,
    receiver: NodeRef,
    index: NodeRef,
    optional: bool,
}

impl DirectSourceElementSyntax {
    pub(super) const fn receiver(self) -> NodeRef {
        self.receiver
    }

    pub(super) const fn index(self) -> NodeRef {
        self.index
    }
}

/// Fully planned direct read with both recursive expression children retained.
#[derive(Clone, Debug)]
pub(super) struct SourceElementPlan {
    pub(super) node: NodeRef,
    pub(super) receiver: PlannedExpression,
    pub(super) index: PlannedExpression,
    optional: bool,
}

/// Exact result and retryable diagnostic publication for one element read.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CheckedSourceElement {
    pub(super) type_: TypeId,
    pub(super) diagnostic: Option<CanonicalCheckerDiagnostic>,
}

/// Proves a read-only element-access AST and its existing cache shape before
/// recursive source planning begins.
pub(super) fn plan_direct_source_element_syntax(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<DirectSourceElementSyntax, SourceElementError> {
    plan_direct_source_element_syntax_worker(arena, store, node, None)
}

/// Proves an indexed assignment target owned by its exact ordinary assignment.
pub(super) fn plan_direct_source_element_write_syntax(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    assignment: NodeRef,
) -> Result<DirectSourceElementSyntax, SourceElementError> {
    plan_direct_source_element_syntax_worker(arena, store, node, Some(assignment))
}

fn plan_direct_source_element_syntax_worker(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    assignment: Option<NodeRef>,
) -> Result<DirectSourceElementSyntax, SourceElementError> {
    let Some(record) = arena.get(node.node) else {
        return Err(unsupported_access(node));
    };
    let NodeData::ElementAccessExpression(access) = &record.data else {
        return Err(unsupported_access(node));
    };
    if record.kind != SyntaxKind::ElementAccessExpression
        || record.flags.0 != 0
        || access.flow_node.is_some()
        || access.facts != 0
    {
        return Err(unsupported_access(node));
    }

    if let Some(parent) = record.parent
        && let Some(parent_record) = arena.get(parent)
        && let NodeData::CallExpression(call) = &parent_record.data
        && call.expression == node.node
    {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::MemberCall(NodeRef::new(node.arena, node.file, parent)),
        ));
    }
    if let Some(parent) = record.parent
        && let Some(parent_record) = arena.get(parent)
        && let NodeData::BinaryExpression(binary) = &parent_record.data
        && binary.left == node.node
        && let Some(operator) = arena.get(binary.operator_token)
        && operator.kind.is_assignment_operator()
    {
        let actual = NodeRef::new(node.arena, node.file, parent);
        if assignment != Some(actual) || operator.kind != SyntaxKind::EqualsToken {
            return Err(SourceElementError::Unsupported(
                SourceElementUnsupported::Write(node),
            ));
        }
    } else if assignment.is_some() {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::Write(node),
        ));
    }

    let receiver = NodeRef::new(node.arena, node.file, access.expression);
    let index = NodeRef::new(node.arena, node.file, access.argument_expression);
    let Some(receiver_record) = arena.get(receiver.node) else {
        return Err(unsupported_access(node));
    };
    let Some(index_record) = arena.get(index.node) else {
        return Err(unsupported_access(node));
    };
    if receiver_record.parent != Some(node.node) || index_record.parent != Some(node.node) {
        return Err(unsupported_access(node));
    }
    let optional = if let Some(token_id) = access.question_dot_token {
        let Some(token) = arena.get(token_id) else {
            return Err(unsupported_access(node));
        };
        if token.kind != SyntaxKind::QuestionDotToken
            || token.parent != Some(node.node)
            || token.flags.0 != 0
            || token.range.start < receiver_record.range.end
            || token.range.end > index_record.range.start
        {
            return Err(unsupported_access(node));
        }
        true
    } else {
        receiver_continues_optional_chain(arena, receiver_record)
    };

    if assignment.is_some() && optional {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::Write(node),
        ));
    }

    preflight_element_links(store, node)?;
    Ok(DirectSourceElementSyntax {
        node,
        receiver,
        index,
        optional,
    })
}

/// Joins proven syntax to the source planner's recursively validated children.
pub(super) fn finish_direct_source_element_plan(
    syntax: DirectSourceElementSyntax,
    receiver: PlannedExpression,
    index: PlannedExpression,
) -> Result<SourceElementPlan, SourceElementError> {
    if receiver.node != syntax.receiver {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::Receiver(syntax.receiver),
        ));
    }
    if index.node != syntax.index {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::Index(syntax.index),
        ));
    }
    Ok(SourceElementPlan {
        node: syntax.node,
        receiver,
        index,
        optional: syntax.optional,
    })
}

/// Checks one direct source read with the production global identities.
#[allow(clippy::too_many_arguments)]
pub(super) fn check_direct_source_element(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    index_type: TypeId,
) -> Result<CheckedSourceElement, SourceElementError> {
    check_direct_source_element_worker(
        store,
        host,
        Some(global_types),
        CanonicalArrayTargets::from_global_types(global_types),
        options,
        plan,
        receiver_type,
        index_type,
        false,
    )
}

/// Checks an authenticated indexed assignment without applying read-only
/// `noUncheckedIndexedAccess` widening to its assignment target.
#[allow(clippy::too_many_arguments)]
pub(super) fn check_direct_source_element_write(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    index_type: TypeId,
) -> Result<CheckedSourceElement, SourceElementError> {
    check_direct_source_element_worker(
        store,
        host,
        Some(global_types),
        CanonicalArrayTargets::from_global_types(global_types),
        options,
        plan,
        receiver_type,
        index_type,
        true,
    )
}

/// Checks one array binding against the numeric index declared by its real
/// global array target, without publishing expression-owned node links.
pub(super) fn check_array_binding_element(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    binding: NodeRef,
    receiver_type: TypeId,
) -> Result<CheckedSourceElement, SourceElementError> {
    let (name, index) = array_binding_name_and_index(store, host, binding)?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    let any = bootstrap.any_type;
    let error = bootstrap.error_type;
    if receiver_type == any || receiver_type == error {
        return Ok(CheckedSourceElement {
            type_: receiver_type,
            diagnostic: None,
        });
    }

    let array = store
        .canonical_array_reference(global_types, receiver_type)?
        .ok_or(SourceElementError::Unsupported(
            SourceElementUnsupported::Receiver(binding),
        ))?;
    let target = if array.readonly {
        global_types.readonly_array_type
    } else {
        global_types.array_type
    };
    if array_target_has_numeric_index(store, host, target, index)? {
        return Ok(CheckedSourceElement {
            type_: unchecked_index_read_type(
                store,
                Some(global_types),
                options,
                name,
                array.element_type,
            )?,
            diagnostic: None,
        });
    }

    let receiver = display_type(store, host, Some(global_types), options, receiver_type)?;
    Ok(CheckedSourceElement {
        type_: error,
        diagnostic: Some(CanonicalCheckerDiagnostic {
            node: Some(name),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(2339).ok_or(SourceElementError::MissingDiagnostic(2339))?,
                [index.to_string(), receiver],
            ),
            related_information: Vec::new(),
        }),
    })
}

fn array_binding_name_and_index(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    binding: NodeRef,
) -> Result<(NodeRef, usize), SourceElementError> {
    let invalid = || SourceElementError::InvalidCache(binding);
    let (_, bound) = host.source(binding).ok_or_else(invalid)?;
    let record = host.node(binding).ok_or_else(invalid)?;
    let NodeData::BindingElement(element) = &record.data else {
        return Err(unsupported_access(binding));
    };
    if !store.contains_node_ref(binding)
        || record.kind != SyntaxKind::BindingElement
        || record.flags.0 != 0
        || element.dot_dot_dot_token.is_some()
        || element.flow_node.is_some()
        || element.initializer.is_some()
        || element.local_symbol.is_some()
        || element.property_name.is_some()
        || element.symbol.is_some()
        || element.facts != 0
        || bound
            .symbol(binding)
            .is_none_or(|symbol| store.symbol(symbol).is_none())
    {
        return Err(unsupported_access(binding));
    }

    let pattern = record
        .parent
        .map(|parent| NodeRef::new(binding.arena, binding.file, parent))
        .ok_or_else(invalid)?;
    let pattern_record = host.node(pattern).ok_or_else(invalid)?;
    let NodeData::BindingPattern(data) = &pattern_record.data else {
        return Err(unsupported_access(binding));
    };
    let mut positions = data
        .elements
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(index, element)| (*element == binding.node).then_some(index));
    let index = positions.next().ok_or_else(invalid)?;
    if positions.next().is_some()
        || pattern_record.kind != SyntaxKind::ArrayBindingPattern
        || pattern_record.flags.0 != 0
        || data.elements.range != pattern_record.range
        || data.facts != 0
        || record.range.start < pattern_record.range.start
        || record.range.end > pattern_record.range.end
    {
        return Err(unsupported_access(binding));
    }
    for sibling in &data.elements.nodes {
        let sibling = NodeRef::new(pattern.arena, pattern.file, *sibling);
        let sibling_record = host.node(sibling).ok_or_else(invalid)?;
        if sibling_record.parent != Some(pattern.node)
            || sibling_record.flags.0 != 0
            || sibling_record.range.start < pattern_record.range.start
            || sibling_record.range.end > pattern_record.range.end
            || !store.contains_node_ref(sibling)
            || !bound.contains(sibling)
        {
            return Err(unsupported_access(binding));
        }
        match &sibling_record.data {
            NodeData::BindingElement(_) if sibling_record.kind == SyntaxKind::BindingElement => {}
            NodeData::OmittedExpression(_)
                if sibling_record.kind == SyntaxKind::OmittedExpression
                    && sibling_record.range.start == sibling_record.range.end
                    && bound.symbol(sibling).is_none()
                    && bound.local_symbol(sibling).is_none() => {}
            _ => return Err(unsupported_access(binding)),
        }
    }

    let name = element
        .name
        .map(|name| NodeRef::new(binding.arena, binding.file, name))
        .ok_or_else(|| unsupported_access(binding))?;
    let name_record = host.node(name).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported_access(binding));
    };
    if !store.contains_node_ref(name)
        || name_record.kind != SyntaxKind::Identifier
        || name_record.flags.0 != 0
        || name_record.parent != Some(binding.node)
        || name_record.range.start < record.range.start
        || name_record.range.end > record.range.end
        || identifier.flow_node.is_some()
        || identifier.text.is_empty()
    {
        return Err(unsupported_access(binding));
    }
    Ok((name, index))
}

fn array_target_has_numeric_index(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    target: TypeId,
    position: usize,
) -> Result<bool, SourceElementError> {
    let invalid = || SourceElementError::InvalidType(target);
    let unsupported =
        || SourceElementError::Unsupported(SourceElementUnsupported::IndexSignatureSurface(target));
    let record = store.type_payload(target).ok_or_else(invalid)?;
    let TypeData::Interface(interface) = record.data() else {
        return Err(invalid());
    };
    let owner = record.symbol().ok_or_else(invalid)?;
    let symbol = store.symbol(owner).ok_or_else(invalid)?;
    let declarations = symbol
        .declarations()
        .filter(|declarations| !declarations.is_empty())
        .ok_or_else(invalid)?;
    let members = symbol.members().ok_or_else(invalid)?;
    let table = store.symbol_table(members).ok_or_else(invalid)?;
    if record.flags() != TypeFlags::OBJECT
        || !record.object_flags().contains(ObjectFlags::INTERFACE)
        || store.get_merged_symbol(owner) != Some(owner)
        || !symbol.flags().contains(SymbolFlags::INTERFACE)
        || symbol.flags().without(
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT,
        ) != SymbolFlags::NONE
        || symbol.check_flags() != CheckFlags::NONE
        || symbol.exports().is_some()
        || symbol.export_symbol().is_some()
    {
        return Err(invalid());
    }

    let mut signature_declarations = Vec::new();
    let mut value_declarations = Vec::new();
    for declaration in declarations {
        let declaration_record = host.node(*declaration).ok_or_else(invalid)?;
        if let NodeData::VariableDeclaration(_) = &declaration_record.data {
            if declaration_record.kind != SyntaxKind::VariableDeclaration
                || !host.symbol_matches(store, *declaration, owner)
            {
                return Err(invalid());
            }
            value_declarations.push(*declaration);
            continue;
        }
        let NodeData::InterfaceDeclaration(data) = &declaration_record.data else {
            return Err(invalid());
        };
        if declaration_record.kind != SyntaxKind::InterfaceDeclaration
            || !host.symbol_matches(store, *declaration, owner)
            || data.type_parameters.as_ref().is_none_or(|parameters| {
                parameters.nodes.len() != 1 || parameters.has_trailing_comma
            })
        {
            return Err(invalid());
        }
        if data.heritage_clauses.is_some() {
            return Err(unsupported());
        }
        for member in &data.members.nodes {
            let member = NodeRef::new(declaration.arena, declaration.file, *member);
            let member_record = host.node(member).ok_or_else(invalid)?;
            if member_record.kind == SyntaxKind::IndexSignature {
                signature_declarations.push(member);
            }
        }
    }
    if symbol
        .flags()
        .contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
        == value_declarations.is_empty()
        || match symbol.value_declaration() {
            Some(declaration) => !value_declarations.contains(&declaration),
            None => !value_declarations.is_empty(),
        }
    {
        return Err(invalid());
    }

    if table.get_source(&position.to_string()).is_some() {
        return Err(unsupported());
    }

    let Some(index_symbol) = table.get(InternalSymbolName::Index.as_ref()) else {
        if !signature_declarations.is_empty()
            || interface.declared_index_infos.is_some()
            || interface.reference.object.structured.index_infos.is_some()
        {
            return Err(invalid());
        }
        return Ok(false);
    };
    validate_array_numeric_index(
        store,
        host,
        target,
        owner,
        index_symbol,
        &signature_declarations,
    )
}

fn validate_array_numeric_index(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    target: TypeId,
    owner: SemanticSymbolId,
    index_symbol: SemanticSymbolId,
    declarations: &[NodeRef],
) -> Result<bool, SourceElementError> {
    let invalid = || SourceElementError::InvalidType(target);
    let unsupported =
        || SourceElementError::Unsupported(SourceElementUnsupported::IndexSignatureSurface(target));
    let TypeData::Interface(interface) = store
        .type_payload(target)
        .map(TypeRecord::data)
        .ok_or_else(invalid)?
    else {
        return Err(invalid());
    };
    let table = store
        .symbol(owner)
        .and_then(ts_binder::semantic::Symbol::members)
        .and_then(|members| store.symbol_table(members))
        .ok_or_else(invalid)?;
    let index_record = store.symbol(index_symbol).ok_or_else(invalid)?;
    if store.get_merged_symbol(index_symbol) != Some(index_symbol)
        || index_record.flags() != SymbolFlags::SIGNATURE
        || index_record.check_flags() != CheckFlags::NONE
        || index_record.name() != InternalSymbolName::Index.as_ref()
        || index_record.declarations() != Some(declarations)
        || index_record.value_declaration().is_some()
        || index_record.members().is_some()
        || index_record.exports().is_some()
        || index_record
            .parent()
            .and_then(|parent| store.get_merged_symbol(parent))
            != Some(owner)
        || index_record.export_symbol().is_some()
    {
        return Err(invalid());
    }

    let parameter = interface
        .all_type_parameters
        .as_deref()
        .and_then(|parameters| parameters.first())
        .copied()
        .ok_or_else(invalid)?;
    let parameter_symbol = store
        .type_payload(parameter)
        .and_then(TypeRecord::symbol)
        .ok_or_else(invalid)?;
    let parameter_name = store
        .symbol(parameter_symbol)
        .and_then(|symbol| symbol.name().as_utf8())
        .ok_or_else(invalid)?;
    if table.get_source(parameter_name) != Some(parameter_symbol) {
        return Err(invalid());
    }

    for declaration in declarations.iter().copied() {
        if array_index_signature_matches_parameter(
            store,
            host,
            target,
            index_symbol,
            declaration,
            parameter_name,
        )? {
            return Ok(true);
        }
    }

    Err(unsupported())
}

fn array_index_signature_matches_parameter(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    target: TypeId,
    index_symbol: SemanticSymbolId,
    declaration: NodeRef,
    parameter_name: &str,
) -> Result<bool, SourceElementError> {
    let invalid = || SourceElementError::InvalidType(target);
    let unsupported =
        || SourceElementError::Unsupported(SourceElementUnsupported::IndexSignatureSurface(target));
    let declaration_record = host.node(declaration).ok_or_else(invalid)?;
    let NodeData::IndexSignatureDeclaration(signature) = &declaration_record.data else {
        return Err(invalid());
    };
    let [index_parameter] = signature.parameters.nodes.as_slice() else {
        return Err(unsupported());
    };
    if !host.symbol_matches(store, declaration, index_symbol)
        || signature.full_signature.is_some()
        || signature.next_container.is_some()
        || signature.symbol.is_some()
        || signature.type_parameters.is_some()
        || signature.parameters.has_trailing_comma
    {
        return Err(invalid());
    }
    let index_parameter = NodeRef::new(declaration.arena, declaration.file, *index_parameter);
    let parameter_record = host.node(index_parameter).ok_or_else(invalid)?;
    let NodeData::ParameterDeclaration(index_parameter_data) = &parameter_record.data else {
        return Err(invalid());
    };
    let Some(key_node) = index_parameter_data.type_ else {
        return Err(unsupported());
    };
    let key_node = NodeRef::new(index_parameter.arena, index_parameter.file, key_node);
    let key_record = host.node(key_node).ok_or_else(invalid)?;
    if parameter_record.kind != SyntaxKind::Parameter
        || parameter_record.parent != Some(declaration.node)
        || key_record.parent != Some(index_parameter.node)
    {
        return Err(invalid());
    }
    if key_record.kind != SyntaxKind::NumberKeyword {
        return Ok(false);
    }

    let value = NodeRef::new(declaration.arena, declaration.file, signature.type_);
    let value_record = host.node(value).ok_or_else(invalid)?;
    let NodeData::TypeReferenceNode(reference) = &value_record.data else {
        return Err(unsupported());
    };
    let name = NodeRef::new(value.arena, value.file, reference.type_name);
    let name_record = host.node(name).ok_or_else(invalid)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(unsupported());
    };
    if value_record.kind != SyntaxKind::TypeReference
        || value_record.parent != Some(declaration.node)
        || reference.type_arguments.is_some()
        || name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(value.node)
        || identifier.text != parameter_name
    {
        return Err(unsupported());
    }
    Ok(true)
}

/// Checks a computed object-binding index without using element-access
/// diagnostic policy or publishing expression caches owned by source checking.
#[allow(clippy::too_many_arguments)] // Keeps the authenticated binding and type identities explicit.
pub(super) fn check_computed_binding_element(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    binding: NodeRef,
    receiver_type: TypeId,
    index_type: TypeId,
) -> Result<CheckedSourceElement, SourceElementError> {
    check_computed_binding_element_worker(
        store,
        host,
        Some(global_types),
        options,
        binding,
        receiver_type,
        index_type,
    )
}

#[allow(clippy::too_many_arguments, clippy::too_many_lines)] // Preserve the indexed-access and recovery order.
fn check_computed_binding_element_worker(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    options: CanonicalCheckerOptions,
    binding: NodeRef,
    receiver_type: TypeId,
    index_type: TypeId,
) -> Result<CheckedSourceElement, SourceElementError> {
    let (index_node, allow_missing) = computed_binding_index(store, host, binding, index_type)?;
    let index = classify_index(store, index_type)?;
    let index_flags = store
        .type_payload(index_type)
        .ok_or(SourceElementError::InvalidType(index_type))?
        .flags();
    let receiver = store
        .type_payload(receiver_type)
        .ok_or(SourceElementError::InvalidType(receiver_type))?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    let any = bootstrap.any_type;
    let error = bootstrap.error_type;
    let undefined = bootstrap.undefined_type;
    let never = bootstrap.never_type;
    if index_flags.intersects(TypeFlags::ANY) {
        store.validate_union_constituent(index_type)?;
        if index_type != any && index_type != error {
            return Err(SourceElementError::Unsupported(
                SourceElementUnsupported::IndexType(index_type),
            ));
        }
    }
    if receiver_type == any || receiver_type == error {
        return Ok(CheckedSourceElement {
            type_: receiver_type,
            diagnostic: None,
        });
    }
    if receiver.flags() != TypeFlags::OBJECT {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::IndexSignatureSurface(receiver_type),
        ));
    }
    let object_flags = receiver.object_flags();
    if index_flags.intersects(TypeFlags::TEMPLATE_LITERAL | TypeFlags::STRING_MAPPING) {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::IndexType(index_type),
        ));
    }
    if matches!(index.shape, IndexShape::Literal { .. }) {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::IndexType(index_type),
        ));
    }

    if let Some(signatures) = resolved_index_signature_surface(store, receiver_type)? {
        let value = match index.shape {
            IndexShape::String => signatures.string,
            IndexShape::Number | IndexShape::Any => signatures.number.or(signatures.string),
            IndexShape::Invalid if index_type == never => signatures.number.or(signatures.string),
            IndexShape::Invalid => None,
            IndexShape::Literal { .. } => unreachable!("literal keys use property lookup"),
        };
        if let Some(value) = value {
            validate_computed_binding_index_annotations(
                store,
                host,
                global_types,
                options,
                receiver_type,
            )?;
            return Ok(CheckedSourceElement {
                type_: unchecked_index_read_type(store, global_types, options, binding, value)?,
                diagnostic: None,
            });
        }
    } else {
        // Authenticate the existing object graph before claiming it has no
        // matching index signature.
        store.resolved_own_property(receiver_type, "")?;
    }

    if index_type == never {
        return Ok(CheckedSourceElement {
            type_: never,
            diagnostic: None,
        });
    }
    // Binding defaults permit absent properties only on object-literal types.
    if allow_missing && object_flags.contains(ObjectFlags::OBJECT_LITERAL) {
        return Ok(CheckedSourceElement {
            type_: undefined,
            diagnostic: None,
        });
    }
    if object_flags.contains(ObjectFlags::JS_LITERAL) {
        return Ok(CheckedSourceElement {
            type_: any,
            diagnostic: None,
        });
    }

    let (code, arguments) = if matches!(index.shape, IndexShape::String | IndexShape::Number) {
        (
            2537,
            vec![
                display_type(store, host, global_types, options, receiver_type)?,
                display_type(store, host, global_types, options, index_type)?,
            ],
        )
    } else {
        (
            2538,
            vec![if host
                .node(index_node)
                .is_some_and(|node| node.kind == SyntaxKind::BigIntLiteral)
            {
                "bigint".to_owned()
            } else {
                display_type(store, host, global_types, options, index_type)?
            }],
        )
    };
    Ok(CheckedSourceElement {
        type_: if matches!(index.shape, IndexShape::Any) {
            index_type
        } else {
            error
        },
        diagnostic: Some(CanonicalCheckerDiagnostic {
            node: Some(index_node),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(code).ok_or(SourceElementError::MissingDiagnostic(code))?,
                arguments,
            ),
            related_information: Vec::new(),
        }),
    })
}

fn validate_computed_binding_index_annotations(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    options: CanonicalCheckerOptions,
    receiver: TypeId,
) -> Result<(), SourceElementError> {
    let invalid = || SourceElementError::InvalidType(receiver);
    let record = store.type_payload(receiver).ok_or_else(invalid)?;
    let Some(owner) = record.symbol() else {
        let indexes = record
            .data()
            .structured()
            .and_then(|structured| structured.index_infos.as_deref())
            .ok_or_else(invalid)?;
        if record.alias().is_some()
            || indexes.iter().any(|index| {
                store.index_info(*index).is_none_or(|info| {
                    info.declaration().is_some()
                        || info.index_symbol().is_some()
                        || !info.components().is_empty()
                })
            })
        {
            return Err(invalid());
        }
        return Ok(());
    };
    let Some([declaration]) = store
        .symbol(owner)
        .and_then(ts_binder::semantic::Symbol::declarations)
    else {
        return Err(invalid());
    };
    let declaration = *declaration;
    let alias = match record.alias() {
        Some(alias) => Some(
            store
                .type_alias(alias)
                .and_then(super::type_records::TypeAlias::symbol)
                .ok_or_else(invalid)?,
        ),
        None => None,
    };
    let plan = object_members::plan_type_literal(store, host, declaration, alias)
        .map_err(|_| invalid())?;
    if object_members::type_literal_state(store, &plan).map_err(|_| invalid())?
        != Some(PropertyObjectState::Resolved(receiver))
    {
        return Err(invalid());
    }
    let mut diagnostics = CanonicalCheckerDiagnostics::default();
    let query = match global_types {
        Some(global_types) => CanonicalTypeQuery::new_with_global_types(
            store,
            host,
            global_types,
            options,
            &mut diagnostics,
        )?,
        None => CanonicalTypeQuery::new(store, host, options, &mut diagnostics)?,
    };
    for (key, value) in plan.index_type_nodes() {
        query.preflight_type_from_type_node(key)?;
        query.preflight_type_from_type_node(value)?;
    }
    drop(query);
    let index_types = plan
        .index_type_nodes()
        .map(|(key, value)| {
            Ok((
                computed_binding_annotation_identity(store, host, key)?,
                computed_binding_annotation_identity(store, host, value)?,
            ))
        })
        .collect::<Result<Vec<_>, SourceElementError>>()?;
    object_members::validate_resolved_declared_member_types(store, &plan, &[], &index_types, &[])
        .map_err(|_| invalid())
}

fn computed_binding_annotation_identity(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    mut node: NodeRef,
) -> Result<TypeId, SourceElementError> {
    while let NodeData::ParenthesizedTypeNode(parenthesized) = &host
        .node(node)
        .ok_or(SourceElementError::InvalidCache(node))?
        .data
    {
        node = NodeRef::new(node.arena, node.file, parenthesized.type_);
    }
    let null_literal = match &host
        .node(node)
        .ok_or(SourceElementError::InvalidCache(node))?
        .data
    {
        NodeData::LiteralTypeNode(literal) => host
            .node(NodeRef::new(node.arena, node.file, literal.literal))
            .is_some_and(|literal| literal.kind == SyntaxKind::NullKeyword),
        _ => false,
    };
    cached_annotation_identity(store, node, null_literal)
        .ok_or(SourceElementError::InvalidCache(node))
}

#[allow(clippy::too_many_lines)] // Authenticate the binding, default, and key cache before access.
fn computed_binding_index(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    binding: NodeRef,
    index_type: TypeId,
) -> Result<(NodeRef, bool), SourceElementError> {
    let invalid = || SourceElementError::InvalidCache(binding);
    let (arena, bound) = host.source(binding).ok_or_else(invalid)?;
    let record = host.node(binding).ok_or_else(invalid)?;
    let NodeData::BindingElement(element) = &record.data else {
        return Err(unsupported_access(binding));
    };
    if !store.contains_node_ref(binding)
        || record.kind != SyntaxKind::BindingElement
        || record.flags.0 != 0
        || element.dot_dot_dot_token.is_some()
        || element.flow_node.is_some()
        || element.local_symbol.is_some()
        || element.symbol.is_some()
        || element.facts != 0
        || bound
            .symbol(binding)
            .is_none_or(|symbol| store.symbol(symbol).is_none())
    {
        return Err(unsupported_access(binding));
    }

    let parent = record
        .parent
        .map(|parent| NodeRef::new(binding.arena, binding.file, parent))
        .ok_or_else(invalid)?;
    let parent_record = host.node(parent).ok_or_else(invalid)?;
    let NodeData::BindingPattern(pattern) = &parent_record.data else {
        return Err(unsupported_access(binding));
    };
    if parent_record.kind != SyntaxKind::ObjectBindingPattern
        || parent_record.flags.0 != 0
        || pattern.facts != 0
        || pattern
            .elements
            .nodes
            .iter()
            .filter(|element| **element == binding.node)
            .count()
            != 1
        || record.range.start < parent_record.range.start
        || record.range.end > parent_record.range.end
    {
        return Err(unsupported_access(binding));
    }

    let property = element
        .property_name
        .map(|property| NodeRef::new(binding.arena, binding.file, property))
        .ok_or_else(|| unsupported_access(binding))?;
    let property_record = host.node(property).ok_or_else(invalid)?;
    let NodeData::ComputedPropertyName(computed) = &property_record.data else {
        return Err(unsupported_access(binding));
    };
    if property_record.kind != SyntaxKind::ComputedPropertyName
        || property_record.flags.0 != 0
        || property_record.parent != Some(binding.node)
        || computed.facts != 0
        || property_record.range.start < record.range.start
        || property_record.range.end > record.range.end
    {
        return Err(unsupported_access(binding));
    }

    let name = element
        .name
        .map(|name| NodeRef::new(binding.arena, binding.file, name))
        .ok_or_else(|| unsupported_access(binding))?;
    let name_record = host.node(name).ok_or_else(invalid)?;
    if name_record.kind != SyntaxKind::Identifier
        || !matches!(name_record.data, NodeData::Identifier(_))
        || name_record.parent != Some(binding.node)
        || name_record.range.start < property_record.range.end
        || name_record.range.end > record.range.end
    {
        return Err(unsupported_access(binding));
    }

    if let Some(initializer) = element.initializer {
        let initializer = NodeRef::new(binding.arena, binding.file, initializer);
        let initializer_record = host.node(initializer).ok_or_else(invalid)?;
        if store.source_node_kind(initializer) != Some(initializer_record.kind)
            || store.source_node_parent(initializer) != Some(SourceNodeParent::Parent(binding))
            || initializer_record.parent != Some(binding.node)
            || name_record.range.end > initializer_record.range.start
            || initializer_record.range.end != record.range.end
        {
            return Err(unsupported_access(binding));
        }
    }

    let index = NodeRef::new(binding.arena, binding.file, computed.expression);
    let index_record = host.node(index).ok_or_else(invalid)?;
    if !store.contains_node_ref(index)
        || !bound.contains(index)
        || arena.get(index.node).is_none()
        || index_record.flags.0 != 0
        || index_record.parent != Some(property.node)
        || index_record.range.start < property_record.range.start
        || index_record.range.end > property_record.range.end
    {
        return Err(unsupported_access(binding));
    }
    if store.type_node_links(index).is_some_and(|links| {
        links
            != &(TypeNodeLinks {
                resolved_type: links.resolved_type,
                ..TypeNodeLinks::default()
            })
            || links
                .resolved_type
                .is_some_and(|cached| cached != index_type)
    }) {
        return Err(SourceElementError::InvalidCache(index));
    }
    Ok((index, element.initializer.is_some()))
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
fn check_direct_source_element_with_array_targets(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    array_targets: CanonicalArrayTargets,
    options: CanonicalCheckerOptions,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    index_type: TypeId,
) -> Result<CheckedSourceElement, SourceElementError> {
    check_direct_source_element_worker(
        store,
        host,
        None,
        array_targets,
        options,
        plan,
        receiver_type,
        index_type,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
fn check_direct_source_element_worker(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    array_targets: CanonicalArrayTargets,
    options: CanonicalCheckerOptions,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    index_type: TypeId,
    write: bool,
) -> Result<CheckedSourceElement, SourceElementError> {
    if store.type_payload(receiver_type).is_none() {
        return Err(SourceElementError::InvalidType(receiver_type));
    }
    let indices = classify_indices(store, index_type)?;
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    let any = bootstrap.any_type;
    let error = bootstrap.error_type;
    let string = bootstrap.string_type;
    let undefined = bootstrap.undefined_type;
    let (receiver_type, propagate_undefined) = if plan.optional && receiver_type != any {
        optional_element_receiver(store, global_types, plan, receiver_type)?
    } else {
        (receiver_type, false)
    };

    let resolution = if invalid_const_enum_index(store, plan, receiver_type)? {
        ElementResolution::diagnostic(error, ElementDiagnostic::InvalidConstEnumIndex)
    } else {
        let mut resolutions = Vec::with_capacity(indices.len());
        for index in &indices {
            let resolution = resolve_element_index(
                store,
                global_types,
                array_targets,
                plan,
                receiver_type,
                index,
                any,
                error,
                string,
                undefined,
            )?;
            if indices.len() != 1 && resolution.diagnostic.is_some() {
                return Err(SourceElementError::Unsupported(
                    SourceElementUnsupported::IndexType(index_type),
                ));
            }
            resolutions.push(resolution);
        }
        if let [resolution] = resolutions.as_slice() {
            *resolution
        } else {
            let values = resolutions
                .iter()
                .map(|resolution| resolution.type_)
                .collect::<Vec<_>>();
            let type_ = if values.iter().all(|value| *value == values[0]) {
                values[0]
            } else if let Some(global_types) = global_types {
                store.expression_union_type_with_global_types(
                    global_types,
                    &values,
                    UnionReduction::Literal,
                )?
            } else {
                #[cfg(test)]
                {
                    store.expression_union_type(&values, UnionReduction::Literal)?
                }
                #[cfg(not(test))]
                {
                    return Err(SourceElementError::Unsupported(
                        SourceElementUnsupported::IndexType(index_type),
                    ));
                }
            };
            if resolutions
                .iter()
                .any(|resolution| resolution.from_index_signature)
            {
                ElementResolution::index_signature(type_)
            } else {
                ElementResolution::success(type_, None)
            }
        }
    };

    let type_ = if resolution.from_index_signature && !write {
        unchecked_index_read_type(store, global_types, options, plan.node, resolution.type_)?
    } else {
        resolution.type_
    };
    let type_ = if propagate_undefined && type_ != any && type_ != error && type_ != undefined {
        element_union_type(
            store,
            global_types,
            plan.node,
            &[type_, undefined],
            resolution.property,
        )?
    } else {
        type_
    };

    let diagnostic = prepare_element_diagnostic(
        store,
        host,
        global_types,
        options,
        plan,
        receiver_type,
        index_type,
        resolution.diagnostic,
    )?;
    publish_element_links(store, plan.node, resolution.property, type_)?;
    Ok(CheckedSourceElement { type_, diagnostic })
}

fn receiver_continues_optional_chain(arena: &NodeArena, receiver: &ts_ast::Node) -> bool {
    match &receiver.data {
        NodeData::PropertyAccessExpression(access) => {
            access.question_dot_token.is_some()
                || arena
                    .get(access.expression)
                    .is_some_and(|parent| receiver_continues_optional_chain(arena, parent))
        }
        NodeData::ElementAccessExpression(access) => {
            access.question_dot_token.is_some()
                || arena
                    .get(access.expression)
                    .is_some_and(|parent| receiver_continues_optional_chain(arena, parent))
        }
        _ => false,
    }
}

fn optional_element_receiver(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
) -> Result<(TypeId, bool), SourceElementError> {
    let strict = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?
        .options
        .strict_null_checks;
    if !strict {
        return Ok((receiver_type, false));
    }
    let Some(record) = store.type_payload(receiver_type) else {
        return Err(SourceElementError::InvalidType(receiver_type));
    };
    if !record.flags().intersects(TypeFlags::UNION) {
        if record.flags().intersects(TypeFlags::NULLABLE) {
            return Err(SourceElementError::Unsupported(
                SourceElementUnsupported::Receiver(plan.receiver.node),
            ));
        }
        return Ok((receiver_type, false));
    }
    let TypeData::Union(union) = record.data() else {
        return Err(SourceElementError::InvalidType(receiver_type));
    };
    let constituents = union.union.types.clone();
    let mut retained = Vec::with_capacity(constituents.len());
    for constituent in constituents.iter().copied() {
        let flags = store
            .type_payload(constituent)
            .map(TypeRecord::flags)
            .ok_or(SourceElementError::InvalidType(constituent))?;
        if !flags.intersects(TypeFlags::NULLABLE) {
            retained.push(constituent);
        }
    }
    if retained.len() == constituents.len() {
        return Ok((receiver_type, false));
    }
    let Some(first) = retained.first().copied() else {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::Receiver(plan.receiver.node),
        ));
    };
    let receiver = if retained.len() == 1 {
        first
    } else {
        element_union_type(store, global_types, plan.node, &retained, None)?
    };
    Ok((receiver, true))
}

#[allow(clippy::too_many_arguments)]
fn resolve_element_index(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    array_targets: CanonicalArrayTargets,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    index: &ClassifiedIndex,
    any: TypeId,
    error: TypeId,
    string: TypeId,
    undefined: TypeId,
) -> Result<ElementResolution, SourceElementError> {
    Ok(if receiver_type == error {
        ElementResolution::success(error, None)
    } else if let Some(enumeration) =
        resolve_enum_element(store, plan, receiver_type, index, error, string)?
    {
        enumeration
    } else if matches!(index.shape, IndexShape::Invalid) {
        ElementResolution::diagnostic(error, ElementDiagnostic::InvalidIndexType)
    } else if receiver_type == any {
        ElementResolution::success(any, None)
    } else if let Some(array) =
        store.canonical_array_reference_with_targets(array_targets, receiver_type)?
    {
        if index.is_number_applicable() {
            ElementResolution::index_signature(array.element_type)
        } else if index.is_string_or_number() {
            ElementResolution::diagnostic(error, ElementDiagnostic::NumberIndexRequired)
        } else {
            ElementResolution::diagnostic(error, ElementDiagnostic::InvalidIndexType)
        }
    } else if let Some(tuple) = resolve_tuple_element(store, receiver_type, index, undefined)? {
        tuple
    } else if is_string_receiver(store, receiver_type)? {
        if index.is_number_applicable() {
            ElementResolution::index_signature(string)
        } else if index.is_string_or_number() {
            ElementResolution::diagnostic(error, ElementDiagnostic::NumberIndexRequired)
        } else {
            ElementResolution::diagnostic(error, ElementDiagnostic::InvalidIndexType)
        }
    } else {
        resolve_object_element(store, global_types, plan, receiver_type, index, any, error)?
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum IndexShape {
    Any,
    String,
    Number,
    Literal { numeric_name: bool },
    Invalid,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ClassifiedIndex {
    shape: IndexShape,
    property_name: Option<String>,
}

impl ClassifiedIndex {
    fn is_number_applicable(&self) -> bool {
        matches!(
            self.shape,
            IndexShape::Any | IndexShape::Number | IndexShape::Literal { numeric_name: true }
        )
    }

    fn is_string_or_number(&self) -> bool {
        !matches!(self.shape, IndexShape::Invalid)
    }
}

fn classify_indices(
    store: &CanonicalTypeMapperStore,
    index_type: TypeId,
) -> Result<Vec<ClassifiedIndex>, SourceElementError> {
    let mut types = Vec::new();
    collect_index_types(store, index_type, &mut types, &mut HashSet::new())?;
    types
        .into_iter()
        .map(|type_| classify_index(store, type_))
        .collect()
}

fn collect_index_types(
    store: &CanonicalTypeMapperStore,
    index_type: TypeId,
    result: &mut Vec<TypeId>,
    visiting: &mut HashSet<TypeId>,
) -> Result<(), SourceElementError> {
    let record = store
        .type_payload(index_type)
        .ok_or(SourceElementError::InvalidType(index_type))?;
    if !record.flags().intersects(TypeFlags::UNION) {
        if matches!(record.data(), TypeData::Union(_)) {
            return Err(SourceElementError::InvalidType(index_type));
        }
        result.push(index_type);
        return Ok(());
    }
    let TypeData::Union(union) = record.data() else {
        return Err(SourceElementError::InvalidType(index_type));
    };
    if record.flags().intersects(TypeFlags::BOOLEAN) {
        result.push(index_type);
        return Ok(());
    }
    if union.union.types.is_empty() || !visiting.insert(index_type) {
        return Err(SourceElementError::InvalidType(index_type));
    }
    for constituent in &union.union.types {
        collect_index_types(store, *constituent, result, visiting)?;
    }
    visiting.remove(&index_type);
    Ok(())
}

fn classify_index(
    store: &CanonicalTypeMapperStore,
    index_type: TypeId,
) -> Result<ClassifiedIndex, SourceElementError> {
    let record = store
        .type_payload(index_type)
        .ok_or(SourceElementError::InvalidType(index_type))?;
    let flags = record.flags();
    if flags.intersects(TypeFlags::ENUM_LIKE) {
        if enums::canonical_enum_type_owner(store, index_type).is_none() {
            return Err(SourceElementError::Literal(
                LiteralTypeCacheError::InvalidCachedLiteral(index_type),
            ));
        }
    } else if flags.intersects(TypeFlags::FRESHABLE) {
        store.validate_union_constituent(index_type)?;
    }
    if flags == TypeFlags::ENUM {
        return Ok(ClassifiedIndex {
            shape: IndexShape::Number,
            property_name: None,
        });
    }
    if flags == TypeFlags::STRING {
        return Ok(ClassifiedIndex {
            shape: IndexShape::String,
            property_name: None,
        });
    }
    if flags == TypeFlags::NUMBER {
        return Ok(ClassifiedIndex {
            shape: IndexShape::Number,
            property_name: None,
        });
    }
    if flags == TypeFlags::ANY {
        return Ok(ClassifiedIndex {
            shape: IndexShape::Any,
            property_name: None,
        });
    }
    if flags.intersects(TypeFlags::BOOLEAN) {
        return Ok(ClassifiedIndex {
            shape: IndexShape::Invalid,
            property_name: None,
        });
    }
    if flags.intersects(
        TypeFlags::ES_SYMBOL
            | TypeFlags::UNIQUE_ES_SYMBOL
            | TypeFlags::UNION
            | TypeFlags::INTERSECTION
            | TypeFlags::TYPE_PARAMETER
            | TypeFlags::INDEX
            | TypeFlags::INDEXED_ACCESS
            | TypeFlags::CONDITIONAL
            | TypeFlags::SUBSTITUTION,
    ) {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::IndexType(index_type),
        ));
    }
    let TypeData::Literal(literal) = record.data() else {
        return Ok(ClassifiedIndex {
            shape: IndexShape::Invalid,
            property_name: None,
        });
    };
    let name = match &literal.value {
        LiteralValue::String(value) if flags.intersects(TypeFlags::STRING_LITERAL) => value.clone(),
        LiteralValue::Number(value) if flags.intersects(TypeFlags::NUMBER_LITERAL) => {
            value.to_string()
        }
        _ => {
            return Ok(ClassifiedIndex {
                shape: IndexShape::Invalid,
                property_name: None,
            });
        }
    };
    Ok(ClassifiedIndex {
        shape: IndexShape::Literal {
            numeric_name: is_numeric_literal_name(&name),
        },
        property_name: Some(name),
    })
}

fn is_numeric_literal_name(name: &str) -> bool {
    ts_jsnum::from_string(name).to_string() == name
}

fn is_string_receiver(
    store: &CanonicalTypeMapperStore,
    receiver_type: TypeId,
) -> Result<bool, SourceElementError> {
    let record = store
        .type_payload(receiver_type)
        .ok_or(SourceElementError::InvalidType(receiver_type))?;
    if record.flags().intersects(TypeFlags::STRING_LITERAL) {
        store.validate_union_constituent(receiver_type)?;
    }
    Ok(matches!(
        record.flags(),
        TypeFlags::STRING | TypeFlags::STRING_LITERAL
    ))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ElementDiagnostic {
    NumberIndexRequired,
    InvalidIndexType,
    InvalidConstEnumIndex,
    MissingLiteralProperty,
    MissingConstEnumProperty,
    MissingBroadIndex,
    MissingAnyIndex,
    NegativeTupleIndex,
    TupleIndexOutOfBounds { length: usize, index: usize },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ElementResolution {
    type_: TypeId,
    property: Option<SemanticSymbolId>,
    diagnostic: Option<ElementDiagnostic>,
    from_index_signature: bool,
}

impl ElementResolution {
    const fn success(type_: TypeId, property: Option<SemanticSymbolId>) -> Self {
        Self {
            type_,
            property,
            diagnostic: None,
            from_index_signature: false,
        }
    }

    const fn index_signature(type_: TypeId) -> Self {
        Self {
            type_,
            property: None,
            diagnostic: None,
            from_index_signature: true,
        }
    }

    const fn diagnostic(type_: TypeId, diagnostic: ElementDiagnostic) -> Self {
        Self {
            type_,
            property: None,
            diagnostic: Some(diagnostic),
            from_index_signature: false,
        }
    }
}

fn resolve_tuple_element(
    store: &CanonicalTypeMapperStore,
    receiver_type: TypeId,
    index: &ClassifiedIndex,
    undefined: TypeId,
) -> Result<Option<ElementResolution>, SourceElementError> {
    let Some(shape) = store
        .canonical_tuple_shape(receiver_type)
        .map_err(|_| SourceElementError::InvalidType(receiver_type))?
    else {
        return Ok(None);
    };
    let Some(name) = index.property_name.as_deref() else {
        return Ok(None);
    };
    if !matches!(index.shape, IndexShape::Literal { numeric_name: true }) {
        return Ok(None);
    }
    if name.starts_with('-') {
        return Ok(Some(ElementResolution::diagnostic(
            undefined,
            ElementDiagnostic::NegativeTupleIndex,
        )));
    }
    let Ok(position) = name.parse::<usize>() else {
        return Ok(None);
    };
    if let Some(element) = shape.element_types().get(position).copied() {
        return Ok(Some(ElementResolution::success(element, None)));
    }
    if shape
        .element_infos()
        .last()
        .is_some_and(|info| info.flags().contains(super::signatures::ElementFlags::REST))
        && let Some(element) = shape.element_types().last().copied()
    {
        return Ok(Some(ElementResolution::success(element, None)));
    }
    Ok(Some(ElementResolution::diagnostic(
        undefined,
        ElementDiagnostic::TupleIndexOutOfBounds {
            length: shape.element_types().len(),
            index: position,
        },
    )))
}

fn resolve_object_element(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    index: &ClassifiedIndex,
    any_type: TypeId,
    error_type: TypeId,
) -> Result<ElementResolution, SourceElementError> {
    if matches!(index.shape, IndexShape::Invalid) {
        return Ok(ElementResolution::diagnostic(
            error_type,
            ElementDiagnostic::InvalidIndexType,
        ));
    }

    if let Some(name) = index.property_name.as_deref() {
        if let Some(property) =
            resolve_javascript_expando_object_property(store, receiver_type, name)?
        {
            return Ok(property);
        }
        if store
            .type_payload(receiver_type)
            .is_some_and(|record| record.flags().intersects(TypeFlags::UNION))
        {
            let property = store
                .resolved_union_property(receiver_type, name)
                .map_err(|error| union_property_error(plan.node, receiver_type, error))?;
            return Ok(match property {
                Some(property) => {
                    ElementResolution::success(property.type_id(), Some(property.symbol()))
                }
                None => ElementResolution::diagnostic(
                    error_type,
                    ElementDiagnostic::MissingLiteralProperty,
                ),
            });
        }
        match store.resolved_own_property(receiver_type, name) {
            Ok(Some(property)) => {
                let type_ = optional_element_read_type(
                    store,
                    global_types,
                    plan.node,
                    property.symbol,
                    property.type_,
                    property.optional,
                )?;
                return Ok(ElementResolution::success(type_, Some(property.symbol)));
            }
            Ok(None) | Err(RelationUnavailable::StructuredIndexInfos(_)) => {}
            Err(error) => return Err(error.into()),
        }
    }

    if let Some(signatures) = resolved_index_signature_surface(store, receiver_type)? {
        let selected = if matches!(index.shape, IndexShape::Any) {
            signatures.string.or(signatures.number)
        } else if index.is_number_applicable() {
            signatures.number.or(signatures.string)
        } else {
            signatures.string
        };
        if let Some(value) = selected {
            return Ok(ElementResolution::index_signature(value));
        }
        return Ok(ElementResolution::diagnostic(
            error_type,
            if signatures.number.is_some() {
                ElementDiagnostic::NumberIndexRequired
            } else {
                ElementDiagnostic::MissingBroadIndex
            },
        ));
    }

    if matches!(index.shape, IndexShape::Any) {
        return Ok(ElementResolution::success(any_type, None));
    }

    // A broad key has no concrete property to query, but this missing-name
    // lookup still runs the exact own-property surface validator before a
    // diagnostic claims that the receiver has no index signature.
    if index.property_name.is_none() {
        let union_members = match store.type_payload(receiver_type).map(TypeRecord::data) {
            Some(TypeData::Union(union)) => Some(union.union.types.clone()),
            _ => None,
        };
        if let Some(union_members) = union_members {
            if union_members.is_empty() {
                return Err(SourceElementError::InvalidType(receiver_type));
            }
            for member in union_members {
                if resolved_index_signature_surface(store, member)?.is_some() {
                    return Err(SourceElementError::Unsupported(
                        SourceElementUnsupported::IndexSignatureSurface(receiver_type),
                    ));
                }
                store.resolved_own_property(member, "")?;
            }
        } else {
            store.resolved_own_property(receiver_type, "")?;
        }
    }
    Ok(ElementResolution::diagnostic(
        error_type,
        if index.property_name.is_some() {
            ElementDiagnostic::MissingLiteralProperty
        } else {
            ElementDiagnostic::MissingBroadIndex
        },
    ))
}

fn resolve_javascript_expando_object_property(
    store: &CanonicalTypeMapperStore,
    receiver_type: TypeId,
    name: &str,
) -> Result<Option<ElementResolution>, SourceElementError> {
    let Some(record) = store.type_payload(receiver_type) else {
        return Err(SourceElementError::InvalidType(receiver_type));
    };
    let Some(owner_symbol) = record.symbol() else {
        return Ok(None);
    };
    let Some(owner) = store.symbol(owner_symbol) else {
        return Err(SourceElementError::InvalidType(receiver_type));
    };
    if owner.flags() != SymbolFlags::OBJECT_LITERAL || owner.exports().is_none() {
        return Ok(None);
    }
    let TypeData::Object(object) = record.data() else {
        return Err(SourceElementError::InvalidType(receiver_type));
    };
    let Some(exports) = owner.exports() else {
        return Ok(None);
    };
    let table = store
        .symbol_table(exports)
        .ok_or(SourceElementError::InvalidType(receiver_type))?;
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || object.structured.members != Some(exports)
        || owner.members().is_some()
        || owner.parent().is_some()
        || owner.export_symbol().is_some()
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
    {
        return Err(SourceElementError::InvalidType(receiver_type));
    }
    let Some(property_symbol) = table.get_source(name) else {
        return Ok(None);
    };
    let property = store
        .symbol(property_symbol)
        .ok_or(SourceElementError::InvalidType(receiver_type))?;
    let links = store
        .value_symbol_links(property_symbol)
        .ok_or(SourceElementError::InvalidType(receiver_type))?;
    let Some(type_) = links.resolved_type else {
        return Err(SourceElementError::InvalidType(receiver_type));
    };
    if property.flags() != SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT
        || property.check_flags() != CheckFlags::NONE
        || property.parent() != Some(owner_symbol)
        || property.name().as_utf8() != Some(name)
        || property.members().is_some()
        || property.exports().is_some()
        || property.export_symbol().is_some()
        || store.get_merged_symbol(property_symbol) != Some(property_symbol)
        || object
            .structured
            .properties
            .as_deref()
            .is_none_or(|properties| !properties.contains(&property_symbol))
        || links
            != &(ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            })
        || store.type_payload(type_).is_none()
    {
        return Err(SourceElementError::InvalidType(receiver_type));
    }
    Ok(Some(ElementResolution::success(
        type_,
        Some(property_symbol),
    )))
}

fn resolve_enum_element(
    store: &CanonicalTypeMapperStore,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    index: &ClassifiedIndex,
    error_type: TypeId,
    string_type: TypeId,
) -> Result<Option<ElementResolution>, SourceElementError> {
    let Some(owner) = validated_enum_element_owner(store, plan, receiver_type)? else {
        return Ok(None);
    };
    let owner_record = store
        .symbol(owner)
        .ok_or(SourceElementError::InvalidCache(plan.node))?;
    if matches!(index.shape, IndexShape::Invalid) {
        return Ok(None);
    }
    let member = match (owner_record.exports(), index.property_name.as_deref()) {
        (Some(exports), Some(name)) => store
            .symbol_table(exports)
            .ok_or(SourceElementError::InvalidCache(plan.node))?
            .get_source(name),
        _ => None,
    };
    if let Some(member) = member {
        let name = index
            .property_name
            .as_deref()
            .ok_or(SourceElementError::InvalidCache(plan.node))?;
        let (resolved, type_) = enums::enum_value_member_type(store, receiver_type, name)
            .ok_or(SourceElementError::InvalidCache(plan.node))?;
        if resolved != member
            || store.value_symbol_links(member)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
        {
            return Err(SourceElementError::InvalidCache(plan.node));
        }
        return Ok(Some(ElementResolution::success(type_, Some(member))));
    }
    let has_numeric_index = enum_has_numeric_index(store, plan, receiver_type, owner)?;
    if has_numeric_index && index.is_number_applicable() {
        return Ok(Some(ElementResolution::success(string_type, None)));
    }
    Ok(Some(ElementResolution::diagnostic(
        error_type,
        if owner_record.flags() == SymbolFlags::CONST_ENUM {
            ElementDiagnostic::MissingConstEnumProperty
        } else if has_numeric_index {
            ElementDiagnostic::NumberIndexRequired
        } else if matches!(index.shape, IndexShape::Any) {
            ElementDiagnostic::MissingAnyIndex
        } else if index.property_name.is_some() {
            ElementDiagnostic::MissingLiteralProperty
        } else {
            ElementDiagnostic::MissingBroadIndex
        },
    )))
}

fn invalid_const_enum_index(
    store: &CanonicalTypeMapperStore,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
) -> Result<bool, SourceElementError> {
    if matches!(
        store.source_node_kind(plan.index.node),
        Some(SyntaxKind::StringLiteral | SyntaxKind::NoSubstitutionTemplateLiteral)
    ) {
        return Ok(false);
    }
    let Some(owner) = validated_enum_element_owner(store, plan, receiver_type)? else {
        return Ok(false);
    };
    Ok(store
        .symbol(owner)
        .ok_or(SourceElementError::InvalidCache(plan.node))?
        .flags()
        == SymbolFlags::CONST_ENUM)
}

fn validated_enum_element_owner(
    store: &CanonicalTypeMapperStore,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
) -> Result<Option<SemanticSymbolId>, SourceElementError> {
    let receiver = store
        .type_payload(receiver_type)
        .ok_or(SourceElementError::InvalidCache(plan.node))?;
    if receiver.flags() != TypeFlags::OBJECT {
        return Ok(None);
    }
    let Some(owner) = receiver.symbol() else {
        return Ok(None);
    };
    let owner_record = store
        .symbol(owner)
        .ok_or(SourceElementError::InvalidCache(plan.node))?;
    if !owner_record.flags().intersects(SymbolFlags::ENUM) {
        return Ok(None);
    }
    let TypeData::Object(value) = receiver.data() else {
        return Err(SourceElementError::InvalidCache(plan.node));
    };
    let [declaration] = owner_record.declarations().unwrap_or_default() else {
        return Err(SourceElementError::InvalidCache(plan.node));
    };
    let declared = store
        .declared_type_links(owner)
        .and_then(|links| links.declared_type)
        .ok_or(SourceElementError::InvalidCache(plan.node))?;
    let empty_enum = store.type_payload(declared).is_some_and(|declared| {
        declared.flags() == TypeFlags::ENUM && declared.symbol() == Some(owner)
    });
    if !matches!(
        owner_record.flags(),
        SymbolFlags::REGULAR_ENUM | SymbolFlags::CONST_ENUM
    ) || owner_record.check_flags() != CheckFlags::NONE
        || owner_record.value_declaration() != Some(*declaration)
        || owner_record.members().is_some()
        || owner_record.exports().is_some() == empty_enum
        || owner_record.export_symbol().is_some()
        || store.get_merged_symbol(owner) != Some(owner)
        || store.source_node_kind(*declaration) != Some(SyntaxKind::EnumDeclaration)
        || receiver.flags() != TypeFlags::OBJECT
        || receiver.object_flags() != ObjectFlags::ANONYMOUS
        || receiver.alias().is_some()
        || value.structured != StructuredTypeData::default()
        || value.target.is_some()
        || value.mapper.is_some()
        || value.instantiations != TypeCacheState::Unallocated
        || store.value_symbol_links(owner)
            != Some(&ValueSymbolLinks {
                resolved_type: Some(receiver_type),
                ..ValueSymbolLinks::default()
            })
        || enums::canonical_enum_type_owner(store, declared) != Some(owner)
    {
        return Err(SourceElementError::InvalidCache(plan.node));
    }
    if let Some(exports) = owner_record.exports()
        && store
            .symbol_table(exports)
            .ok_or(SourceElementError::InvalidCache(plan.node))?
            .is_empty()
    {
        return Err(SourceElementError::InvalidCache(plan.node));
    }
    Ok(Some(owner))
}

fn enum_has_numeric_index(
    store: &CanonicalTypeMapperStore,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    owner: SemanticSymbolId,
) -> Result<bool, SourceElementError> {
    let owner_record = store
        .symbol(owner)
        .ok_or(SourceElementError::InvalidCache(plan.node))?;
    let declared = store
        .declared_type_links(owner)
        .and_then(|links| links.declared_type)
        .ok_or(SourceElementError::InvalidCache(plan.node))?;
    if store.type_payload(declared).is_some_and(|declared| {
        declared.flags() == TypeFlags::ENUM && declared.symbol() == Some(owner)
    }) {
        return Ok(true);
    }
    let Some(exports) = owner_record.exports() else {
        return Ok(false);
    };
    let exports = store
        .symbol_table(exports)
        .ok_or(SourceElementError::InvalidCache(plan.node))?;
    for (name, member) in exports.iter() {
        let name = name
            .as_utf8()
            .ok_or(SourceElementError::InvalidCache(plan.node))?;
        let (resolved, type_) = enums::enum_value_member_type(store, receiver_type, name)
            .ok_or(SourceElementError::InvalidCache(plan.node))?;
        if resolved != member
            || store.value_symbol_links(member)
                != Some(&ValueSymbolLinks {
                    resolved_type: Some(type_),
                    ..ValueSymbolLinks::default()
                })
        {
            return Err(SourceElementError::InvalidCache(plan.node));
        }
        if store
            .type_payload(type_)
            .is_some_and(|record| record.flags().intersects(TypeFlags::NUMBER_LIKE))
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn unchecked_index_read_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    options: CanonicalCheckerOptions,
    node: NodeRef,
    type_: TypeId,
) -> Result<TypeId, SourceElementError> {
    if !options.no_unchecked_indexed_access {
        return Ok(type_);
    }
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    if !bootstrap.options.strict_null_checks
        || type_ == bootstrap.any_type
        || type_ == bootstrap.error_type
        || type_ == bootstrap.undefined_or_missing_type
    {
        return Ok(type_);
    }
    let undefined = bootstrap.undefined_or_missing_type;
    element_union_type(store, global_types, node, &[type_, undefined], None)
}

fn optional_element_read_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    node: NodeRef,
    property: SemanticSymbolId,
    type_: TypeId,
    optional: bool,
) -> Result<TypeId, SourceElementError> {
    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    if !optional || !bootstrap.options.strict_null_checks {
        return Ok(type_);
    }
    if global_types.is_none() && bootstrap.options.exact_optional_property_types {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::OptionalProperty { node, property },
        ));
    }
    let undefined = bootstrap.undefined_or_missing_type;
    element_union_type(
        store,
        global_types,
        node,
        &[type_, undefined],
        Some(property),
    )
}

fn element_union_type(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    node: NodeRef,
    types: &[TypeId],
    property: Option<SemanticSymbolId>,
) -> Result<TypeId, SourceElementError> {
    if let Some(global_types) = global_types {
        return store
            .expression_union_type_with_global_types(global_types, types, UnionReduction::Literal)
            .map_err(Into::into);
    }
    #[cfg(test)]
    {
        let _ = (node, property);
        store
            .expression_union_type(types, UnionReduction::Literal)
            .map_err(Into::into)
    }
    #[cfg(not(test))]
    {
        Err(SourceElementError::Unsupported(match property {
            Some(property) => SourceElementUnsupported::OptionalProperty { node, property },
            None => SourceElementUnsupported::Access(node),
        }))
    }
}

fn union_property_error(
    node: NodeRef,
    receiver_type: TypeId,
    error: UnionPropertyError,
) -> SourceElementError {
    match error {
        UnionPropertyError::UnsupportedUnion(_)
        | UnionPropertyError::UnsupportedConstituent(_)
        | UnionPropertyError::UnsupportedPropertyType(_)
        | UnionPropertyError::UnsupportedExactOptionalProperty(_) => {
            SourceElementError::Unsupported(SourceElementUnsupported::IndexSignatureSurface(
                receiver_type,
            ))
        }
        UnionPropertyError::InvalidUnion(_)
        | UnionPropertyError::InvalidProperty(_)
        | UnionPropertyError::InvalidCache(_)
        | UnionPropertyError::Capacity(_) => SourceElementError::InvalidCache(node),
        UnionPropertyError::Relation(error) => SourceElementError::Relation(error),
        UnionPropertyError::TypeCache(error) => SourceElementError::Literal(error),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ResolvedIndexSignatures {
    string: Option<TypeId>,
    number: Option<TypeId>,
}

fn resolved_index_signature_surface(
    store: &CanonicalTypeMapperStore,
    receiver_type: TypeId,
) -> Result<Option<ResolvedIndexSignatures>, SourceElementError> {
    let record = store
        .type_payload(receiver_type)
        .ok_or(SourceElementError::InvalidType(receiver_type))?;
    let TypeData::Object(object) = record.data() else {
        return Ok(None);
    };
    let Some(index_infos) = object.structured.index_infos.as_deref() else {
        return Ok(None);
    };
    let object_flags = record.object_flags();
    if index_infos.is_empty()
        || record.flags() != TypeFlags::OBJECT
        || object_flags & ObjectFlags::OBJECT_TYPE_KIND_MASK != ObjectFlags::ANONYMOUS
        || !object_flags.contains(ObjectFlags::MEMBERS_RESOLVED)
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
        || object
            .structured
            .properties
            .as_ref()
            .is_some_and(|items| !items.is_empty())
        || object.structured.signatures.is_some()
        || object.structured.call_signature_count != 0
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return Err(SourceElementError::Unsupported(
            SourceElementUnsupported::IndexSignatureSurface(receiver_type),
        ));
    }

    let bootstrap = store
        .intrinsic_bootstrap()
        .ok_or(RelationUnavailable::MissingBootstrap)?;
    let mut resolved = ResolvedIndexSignatures {
        string: None,
        number: None,
    };
    let mut seen = HashSet::new();
    let mut index_symbol = None;
    for id in index_infos {
        if !seen.insert(*id) {
            return Err(SourceElementError::Unsupported(
                SourceElementUnsupported::IndexSignatureSurface(receiver_type),
            ));
        }
        let info = store
            .index_info(*id)
            .ok_or(SourceElementError::Unsupported(
                SourceElementUnsupported::IndexSignatureSurface(receiver_type),
            ))?;
        if store.type_payload(info.value_type()).is_none() {
            return Err(SourceElementError::InvalidType(info.value_type()));
        }
        match info.key_type() {
            key if key == bootstrap.string_type && resolved.string.is_none() => {
                resolved.string = Some(info.value_type());
            }
            key if key == bootstrap.number_type && resolved.number.is_none() => {
                resolved.number = Some(info.value_type());
            }
            _ => {
                return Err(SourceElementError::Unsupported(
                    SourceElementUnsupported::IndexSignatureSurface(receiver_type),
                ));
            }
        }
        match (index_symbol, info.index_symbol()) {
            (None, symbol) => index_symbol = Some(symbol),
            (Some(expected), actual) if expected == actual => {}
            _ => {
                return Err(SourceElementError::Unsupported(
                    SourceElementUnsupported::IndexSignatureSurface(receiver_type),
                ));
            }
        }
    }

    match (object.structured.members, index_symbol.flatten()) {
        (None, None) => {}
        (Some(members), None)
            if valid_bound_declared_index_member(store, record.symbol(), members, index_infos) => {}
        (Some(members), Some(symbol)) => {
            let table = store
                .symbol_table(members)
                .ok_or(SourceElementError::Unsupported(
                    SourceElementUnsupported::IndexSignatureSurface(receiver_type),
                ))?;
            if table.len() != 1
                || table.get(InternalSymbolName::Index.as_ref()) != Some(symbol)
                || store.symbol(symbol).is_none()
            {
                return Err(SourceElementError::Unsupported(
                    SourceElementUnsupported::IndexSignatureSurface(receiver_type),
                ));
            }
        }
        _ => {
            return Err(SourceElementError::Unsupported(
                SourceElementUnsupported::IndexSignatureSurface(receiver_type),
            ));
        }
    }
    Ok(Some(resolved))
}

fn valid_bound_declared_index_member(
    store: &CanonicalTypeMapperStore,
    owner: Option<SemanticSymbolId>,
    members: SymbolTableId,
    index_infos: &[super::IndexInfoId],
) -> bool {
    let Some(owner) = owner else {
        return false;
    };
    let Some(owner_record) = store.symbol(owner) else {
        return false;
    };
    let Some([owner_declaration]) = owner_record.declarations() else {
        return false;
    };
    let Some(table) = store.symbol_table(members) else {
        return false;
    };
    let Some(symbol) = table.get(InternalSymbolName::Index.as_ref()) else {
        return false;
    };
    let Some(record) = store.symbol(symbol) else {
        return false;
    };
    let declarations = index_infos
        .iter()
        .map(|index| {
            let info = store.index_info(*index)?;
            let declaration = info.declaration()?;
            (info.index_symbol().is_none()
                && info.components().is_empty()
                && store.source_node_kind(declaration) == Some(SyntaxKind::IndexSignature))
            .then_some(declaration)
        })
        .collect::<Option<Vec<_>>>();
    table.len() == 1
        && store.get_merged_symbol(owner) == Some(owner)
        && owner_record.flags() == SymbolFlags::TYPE_LITERAL
        && owner_record.check_flags() == CheckFlags::NONE
        && owner_record.name() == InternalSymbolName::Type.as_ref()
        && owner_record.value_declaration().is_none()
        && owner_record.members() == Some(members)
        && owner_record.exports().is_none()
        && owner_record.parent().is_none()
        && owner_record.export_symbol().is_none()
        && store.source_node_kind(*owner_declaration) == Some(SyntaxKind::TypeLiteral)
        && store.get_merged_symbol(symbol) == Some(symbol)
        && record.flags() == SymbolFlags::SIGNATURE
        && record.check_flags() == CheckFlags::NONE
        && record.name() == InternalSymbolName::Index.as_ref()
        && declarations.as_deref().is_some_and(|declarations| {
            record.declarations() == Some(declarations)
                && declarations.iter().all(|declaration| {
                    store.source_node_parent(*declaration)
                        == Some(SourceNodeParent::Parent(*owner_declaration))
                })
        })
        && record.value_declaration().is_none()
        && record.members().is_none()
        && record.exports().is_none()
        && record.parent() == Some(owner)
        && record.export_symbol().is_none()
}

#[allow(clippy::too_many_arguments)]
fn prepare_element_diagnostic(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    options: CanonicalCheckerOptions,
    plan: &SourceElementPlan,
    receiver_type: TypeId,
    index_type: TypeId,
    kind: Option<ElementDiagnostic>,
) -> Result<Option<CanonicalCheckerDiagnostic>, SourceElementError> {
    let Some(kind) = kind else {
        return Ok(None);
    };
    if !options.no_implicit_any
        && !matches!(
            kind,
            ElementDiagnostic::InvalidIndexType
                | ElementDiagnostic::InvalidConstEnumIndex
                | ElementDiagnostic::MissingConstEnumProperty
                | ElementDiagnostic::NegativeTupleIndex
                | ElementDiagnostic::TupleIndexOutOfBounds { .. }
        )
    {
        return Ok(None);
    }
    let diagnostic = match kind {
        ElementDiagnostic::NumberIndexRequired => CanonicalCheckerDiagnostic {
            node: Some(plan.index.node),
            range_override: None,
            diagnostic: Diagnostic::new(
                message_by_code(7015).ok_or(SourceElementError::MissingDiagnostic(7015))?,
            ),
            related_information: Vec::new(),
        },
        ElementDiagnostic::InvalidIndexType => CanonicalCheckerDiagnostic {
            node: Some(plan.index.node),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(2538).ok_or(SourceElementError::MissingDiagnostic(2538))?,
                [display_type(
                    store,
                    host,
                    global_types,
                    options,
                    if store
                        .type_payload(index_type)
                        .is_some_and(|record| record.flags().intersects(TypeFlags::BIG_INT_LIKE))
                    {
                        store
                            .intrinsic_bootstrap()
                            .ok_or(RelationUnavailable::MissingBootstrap)?
                            .bigint_type
                    } else {
                        index_type
                    },
                )?],
            ),
            related_information: Vec::new(),
        },
        ElementDiagnostic::InvalidConstEnumIndex => CanonicalCheckerDiagnostic {
            node: Some(plan.index.node),
            range_override: None,
            diagnostic: Diagnostic::new(
                message_by_code(2476).ok_or(SourceElementError::MissingDiagnostic(2476))?,
            ),
            related_information: Vec::new(),
        },
        ElementDiagnostic::NegativeTupleIndex => CanonicalCheckerDiagnostic {
            node: Some(plan.index.node),
            range_override: None,
            diagnostic: Diagnostic::new(
                message_by_code(2514).ok_or(SourceElementError::MissingDiagnostic(2514))?,
            ),
            related_information: Vec::new(),
        },
        ElementDiagnostic::TupleIndexOutOfBounds { length, index } => CanonicalCheckerDiagnostic {
            node: Some(plan.index.node),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(2493).ok_or(SourceElementError::MissingDiagnostic(2493))?,
                [
                    display_type(store, host, global_types, options, receiver_type)?,
                    length.to_string(),
                    index.to_string(),
                ],
            ),
            related_information: Vec::new(),
        },
        ElementDiagnostic::MissingConstEnumProperty => {
            let property = classify_index(store, index_type)?
                .property_name
                .ok_or(SourceElementError::InvalidType(index_type))?;
            let receiver = display_type(store, host, global_types, options, receiver_type)?;
            CanonicalCheckerDiagnostic {
                node: Some(plan.index.node),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(2339).ok_or(SourceElementError::MissingDiagnostic(2339))?,
                    [property, receiver],
                ),
                related_information: Vec::new(),
            }
        }
        ElementDiagnostic::MissingAnyIndex => CanonicalCheckerDiagnostic {
            node: Some(plan.node),
            range_override: None,
            diagnostic: Diagnostic::with_arguments(
                message_by_code(7053).ok_or(SourceElementError::MissingDiagnostic(7053))?,
                [
                    display_type(store, host, global_types, options, index_type)?,
                    display_type(store, host, global_types, options, receiver_type)?,
                ],
            ),
            related_information: Vec::new(),
        },
        ElementDiagnostic::MissingLiteralProperty | ElementDiagnostic::MissingBroadIndex => {
            let index = display_type(store, host, global_types, options, index_type)?;
            let receiver = display_type(store, host, global_types, options, receiver_type)?;
            let detail = if kind == ElementDiagnostic::MissingLiteralProperty {
                let property = classify_index(store, index_type)?
                    .property_name
                    .ok_or(SourceElementError::InvalidType(index_type))?;
                Diagnostic::with_arguments(
                    message_by_code(2339).ok_or(SourceElementError::MissingDiagnostic(2339))?,
                    [property, receiver.clone()],
                )
            } else {
                Diagnostic::with_arguments(
                    message_by_code(7054).ok_or(SourceElementError::MissingDiagnostic(7054))?,
                    [index.clone(), receiver.clone()],
                )
            }
            .render()
            .expect("the pinned element diagnostic detail has complete arguments");
            CanonicalCheckerDiagnostic {
                node: Some(plan.node),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(7053).ok_or(SourceElementError::MissingDiagnostic(7053))?,
                    [index, receiver],
                )
                .with_details([format!("  {detail}")]),
                related_information: Vec::new(),
            }
        }
    };
    Ok(Some(diagnostic))
}

fn display_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: Option<&CanonicalGlobalTypes>,
    options: CanonicalCheckerOptions,
    type_: TypeId,
) -> Result<String, SourceElementError> {
    let mut flags = CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
    if options.no_error_truncation {
        flags |= CanonicalTypeFormatFlags::NO_TRUNCATION;
    }
    Ok(match global_types {
        Some(global_types) => type_to_string_with_host_global_types_and_flags(
            store,
            host,
            global_types,
            type_,
            flags,
        )?,
        None => type_to_string_with_host_and_flags(store, host, type_, flags)?,
    })
}

fn unsupported_access(node: NodeRef) -> SourceElementError {
    SourceElementError::Unsupported(SourceElementUnsupported::Access(node))
}

fn preflight_element_links(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<(), SourceElementError> {
    if let Some(links) = store.type_node_links(node) {
        let expected = TypeNodeLinks {
            resolved_type: links.resolved_type,
            ..TypeNodeLinks::default()
        };
        if links != &expected
            || links
                .resolved_type
                .is_some_and(|type_| store.type_payload(type_).is_none())
        {
            return Err(SourceElementError::InvalidCache(node));
        }
    }
    if let Some(links) = store.symbol_node_links(node)
        && links
            .resolved_symbol
            .is_some_and(|symbol| store.symbol(symbol).is_none())
    {
        return Err(SourceElementError::InvalidCache(node));
    }
    Ok(())
}

fn publish_element_links(
    store: &mut CanonicalTypeMapperStore,
    node: NodeRef,
    property: Option<SemanticSymbolId>,
    type_: TypeId,
) -> Result<(), SourceElementError> {
    let expected_type = TypeNodeLinks {
        resolved_type: Some(type_),
        ..TypeNodeLinks::default()
    };
    let expected_symbol = SymbolNodeLinks {
        resolved_symbol: property,
    };
    if store
        .type_node_links(node)
        .is_some_and(|links| links != &TypeNodeLinks::default() && links != &expected_type)
        || store
            .symbol_node_links(node)
            .is_some_and(|links| links != &SymbolNodeLinks::default() && links != &expected_symbol)
    {
        return Err(SourceElementError::InvalidCache(node));
    }
    if property.is_some() && !store.set_symbol_node_links(node, expected_symbol) {
        return Err(SourceElementError::InvalidCache(node));
    }
    if !store.set_type_node_links(node, expected_type) {
        return Err(SourceElementError::InvalidCache(node));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeArena};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts,
        CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolData, SymbolFlags,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, DeclaredTypeLinks, IntrinsicBootstrapOptions, ValueSymbolLinks,
        declared::type_list_key,
        global_types::create_type_from_generic_global_type,
        signatures::ElementFlags,
        source::{PlannedExpressionKind, PlannedIdentifierRead, PlannedIdentifierReadKind},
        tuple_types::CanonicalTupleTypeRequest,
    };

    fn parse_fixture(text: &str) -> ParseResult {
        let parsed = parse_source_file(text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        parsed
    }

    fn registered_store(parsed: &ParseResult, file: FileId) -> CanonicalTypeMapperStore {
        let mut store = CanonicalTypeMapperStore::new();
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            })
            .unwrap();
        store
    }

    fn empty_host() -> DeclaredTypeHost<'static> {
        DeclaredTypeHost::new(std::iter::empty::<(&NodeArena, &BoundFile)>()).unwrap()
    }

    fn element_access(parsed: &ParseResult, file: FileId) -> NodeRef {
        parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ElementAccessExpression)
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap()
    }

    fn alloc_symbol(
        store: &mut CanonicalTypeMapperStore,
        flags: SymbolFlags,
        name: &str,
    ) -> SemanticSymbolId {
        store
            .alloc_symbol(SymbolData::new(flags, EscapedName::source(name)))
            .unwrap()
    }

    fn identifier(node: NodeRef, symbol: SemanticSymbolId) -> PlannedExpression {
        PlannedExpression::new(
            node,
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: symbol,
                value_symbol: symbol,
                kind: PlannedIdentifierReadKind::Variable,
            }),
        )
    }

    fn source_plan(
        parsed: &ParseResult,
        file: FileId,
        store: &CanonicalTypeMapperStore,
        index: PlannedExpressionKind,
        receiver_symbol: SemanticSymbolId,
    ) -> SourceElementPlan {
        let access = element_access(parsed, file);
        let syntax = plan_direct_source_element_syntax(&parsed.arena, store, access).unwrap();
        finish_direct_source_element_plan(
            syntax,
            identifier(syntax.receiver(), receiver_symbol),
            PlannedExpression::new(syntax.index(), index),
        )
        .unwrap()
    }

    fn computed_binding_fixture(
        parsed: &ParseResult,
        file: FileId,
    ) -> (CanonicalTypeMapperStore, BoundFile, NodeRef, NodeRef) {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/computed-binding.ts\""),
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
        let binding = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::BindingElement).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let NodeData::BindingElement(element) = &parsed.arena.get(binding.node).unwrap().data
        else {
            unreachable!("the selected node is an object binding element")
        };
        let property = element.property_name.unwrap();
        let NodeData::ComputedPropertyName(computed) = &parsed.arena.get(property).unwrap().data
        else {
            unreachable!("the binding element has a computed property name")
        };
        let index = NodeRef::new(parsed.arena.id(), file, computed.expression);
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        (store, bound, binding, index)
    }

    fn array_binding_context<'arena>(
        globals: &'arena ParseResult,
        globals_file: FileId,
        source: &'arena ParseResult,
        source_file: FileId,
        options: CanonicalCheckerOptions,
    ) -> CanonicalCheckerContext<'arena> {
        let mut binder = CanonicalBinder::new();
        for (parsed, file, path) in [
            (globals, globals_file, "\"/project/globals.ts\""),
            (source, source_file, "\"/project/input.ts\""),
        ] {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(path),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            vec![(globals_file, &globals.arena), (source_file, &source.arena)],
            options,
        )
        .unwrap()
    }

    fn published_enum(
        parsed: &ParseResult,
        file: FileId,
    ) -> (
        CanonicalTypeMapperStore,
        BoundFile,
        enums::CanonicalEnumSemantics,
    ) {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/enum-element-access.ts\""),
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
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::EnumDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let owner = bound.symbol(declaration).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let enumeration = {
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            enums::get_enum_semantics(&mut store, &host, owner).unwrap()
        };
        (store, bound, enumeration)
    }

    fn enum_element_plan(
        parsed: &ParseResult,
        file: FileId,
        store: &CanonicalTypeMapperStore,
        owner: SemanticSymbolId,
        name: &str,
    ) -> SourceElementPlan {
        enum_index_plan(
            parsed,
            file,
            store,
            owner,
            PlannedExpressionKind::String(name.to_owned()),
        )
    }

    fn enum_index_plan(
        parsed: &ParseResult,
        file: FileId,
        store: &CanonicalTypeMapperStore,
        owner: SemanticSymbolId,
        index: PlannedExpressionKind,
    ) -> SourceElementPlan {
        let access = element_access(parsed, file);
        let syntax = plan_direct_source_element_syntax(&parsed.arena, store, access).unwrap();
        finish_direct_source_element_plan(
            syntax,
            PlannedExpression::new(
                syntax.receiver(),
                PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                    resolved_symbol: owner,
                    value_symbol: owner,
                    kind: PlannedIdentifierReadKind::DeclaredValue,
                }),
            ),
            PlannedExpression::new(syntax.index(), index),
        )
        .unwrap()
    }

    fn property_object(
        store: &mut CanonicalTypeMapperStore,
        name: &str,
        type_: TypeId,
        optional: bool,
    ) -> (TypeId, SemanticSymbolId) {
        let property = alloc_symbol(
            store,
            SymbolFlags::PROPERTY
                | if optional {
                    SymbolFlags::OPTIONAL
                } else {
                    SymbolFlags::NONE
                },
            name,
        );
        assert!(store.set_value_symbol_links(
            property,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        ));
        let members = store.alloc_symbol_table();
        assert_eq!(
            store.insert_symbol(members, EscapedName::source(name), property),
            Some(None)
        );
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            object,
            Some(members),
            Some(vec![property]),
            None,
            None,
            None,
        ));
        (object, property)
    }

    fn index_object(store: &mut CanonicalTypeMapperStore, key: TypeId, value: TypeId) -> TypeId {
        let index = store
            .alloc_index_info(key, value, false, None, Vec::new())
            .unwrap();
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            object,
            None,
            None,
            None,
            None,
            Some(vec![index]),
        ));
        object
    }

    fn canonical_array_target(store: &mut CanonicalTypeMapperStore) -> TypeId {
        let symbol = alloc_symbol(store, SymbolFlags::INTERFACE, "Array");
        let parameter_symbol = alloc_symbol(store, SymbolFlags::TYPE_PARAMETER, "T");
        let parameter = store.alloc_type_parameter(Some(parameter_symbol)).unwrap();
        assert!(store.set_declared_type_links(
            parameter_symbol,
            DeclaredTypeLinks {
                declared_type: Some(parameter),
                ..DeclaredTypeLinks::default()
            },
        ));
        let target = store
            .alloc_interface_type(ObjectFlags::INTERFACE, Some(symbol))
            .unwrap();
        let this_type = store.alloc_type_parameter(Some(symbol)).unwrap();
        assert!(store.initialize_interface_type_parameters(
            target,
            vec![parameter, this_type],
            0,
            this_type,
            type_list_key(&[parameter]),
        ));
        target
    }

    fn strict_options() -> CanonicalCheckerOptions {
        CanonicalCheckerOptions {
            no_implicit_any: true,
            ..CanonicalCheckerOptions::default()
        }
    }

    #[test]
    fn array_binding_without_numeric_index_reports_direct_ts2339_on_its_name() {
        const GLOBALS: &str = concat!(
            "interface Array<T> {}\n",
            "interface Boolean {}\n",
            "interface Function {}\n",
            "interface CallableFunction {}\n",
            "interface NewableFunction {}\n",
            "interface IArguments {}\n",
            "interface Number {}\n",
            "interface Object {}\n",
            "interface RegExp {}\n",
            "interface String {}\n",
        );
        const INPUT: &str = "declare var values: string[];\nvar [value] = values;";
        let globals = parse_fixture(GLOBALS);
        let source = parse_fixture(INPUT);
        let globals_file = FileId::new(650);
        let source_file = FileId::new(651);
        let mut context = array_binding_context(
            &globals,
            globals_file,
            &source,
            source_file,
            CanonicalCheckerOptions::default(),
        );
        context.check_source_file(globals_file).unwrap();
        let global_types = context.global_types().clone();
        let globals_bound = context.file(globals_file).unwrap().1.clone();
        let source_bound = context.file(source_file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([
            (&globals.arena, &globals_bound),
            (&source.arena, &source_bound),
        ])
        .unwrap();
        let (string, error) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.error_type)
        };
        let array = context
            .store_mut_for_test()
            .create_canonical_array_type(&global_types, string, false)
            .unwrap();
        let binding = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::BindingElement).then_some(NodeRef::new(
                    source.arena.id(),
                    source_file,
                    node,
                ))
            })
            .unwrap();
        let NodeData::BindingElement(element) = &source.arena.get(binding.node).unwrap().data
        else {
            panic!("expected the array binding element")
        };
        let name = NodeRef::new(source.arena.id(), source_file, element.name.unwrap());

        for no_implicit_any in [false, true] {
            let before = (
                context.store().type_len(),
                context.store().checker_link_allocated_lengths(),
            );
            let checked = check_array_binding_element(
                context.store_mut_for_test(),
                &host,
                &global_types,
                CanonicalCheckerOptions {
                    no_implicit_any,
                    no_unchecked_indexed_access: true,
                    ..CanonicalCheckerOptions::default()
                },
                binding,
                array,
            )
            .unwrap();
            assert_eq!(checked.type_, error);
            let diagnostic = checked.diagnostic.unwrap();
            assert_eq!(diagnostic.node, Some(name));
            assert_eq!(diagnostic.diagnostic.code(), 2339);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Property '0' does not exist on type 'string[]'."
            );
            let range = source.arena.get(name.node).unwrap().range;
            assert_eq!(
                &INPUT[range.start.get() as usize..range.end.get() as usize],
                "value"
            );
            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().checker_link_allocated_lengths(),
                ),
                before
            );
            assert!(context.store().type_node_links(name).is_none());
            assert!(context.store().symbol_node_links(name).is_none());
        }
    }

    #[test]
    fn array_binding_uses_real_numeric_indexes_and_applies_unchecked_access() {
        let globals = parse_fixture(concat!(
            "interface Array<T> { [index: number]: T; }\n",
            "interface Boolean {}\n",
            "interface Function {}\n",
            "interface IArguments {}\n",
            "interface Number {}\n",
            "interface Object {}\n",
            "interface RegExp {}\n",
            "interface String {}\n",
        ));
        let source = parse_fixture("declare var values: string[]; var [value] = values;");
        let globals_file = FileId::new(652);
        let source_file = FileId::new(653);
        let options = CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            no_unchecked_indexed_access: true,
            ..CanonicalCheckerOptions::default()
        };
        let mut context =
            array_binding_context(&globals, globals_file, &source, source_file, options);
        let global_types = context.global_types().clone();
        let globals_bound = context.file(globals_file).unwrap().1.clone();
        let source_bound = context.file(source_file).unwrap().1.clone();
        let host = DeclaredTypeHost::new([
            (&globals.arena, &globals_bound),
            (&source.arena, &source_bound),
        ])
        .unwrap();
        let (string, undefined) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.undefined_type)
        };
        let array = context
            .store_mut_for_test()
            .create_canonical_array_type(&global_types, string, false)
            .unwrap();
        let binding = source
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::BindingElement).then_some(NodeRef::new(
                    source.arena.id(),
                    source_file,
                    node,
                ))
            })
            .unwrap();

        let checked = check_array_binding_element(
            context.store_mut_for_test(),
            &host,
            &global_types,
            CanonicalCheckerOptions {
                no_unchecked_indexed_access: false,
                ..options
            },
            binding,
            array,
        )
        .unwrap();
        assert_eq!(checked.type_, string);
        assert!(checked.diagnostic.is_none());

        let checked = check_array_binding_element(
            context.store_mut_for_test(),
            &host,
            &global_types,
            options,
            binding,
            array,
        )
        .unwrap();
        let TypeData::Union(union) = context.store().type_payload(checked.type_).unwrap().data()
        else {
            panic!("unchecked numeric array bindings include undefined")
        };
        assert!(union.union.types.contains(&string));
        assert!(union.union.types.contains(&undefined));
        assert!(checked.diagnostic.is_none());
        assert!(context.store().type_node_links(binding).is_none());
    }

    #[test]
    fn computed_binding_broad_keys_emit_ts2537_without_no_implicit_any() {
        let source = "let foo2 = () => 'bar'; let { [foo2()]: bar3 } = {};";
        let parsed = parse_fixture(source);
        let file = FileId::new(640);
        let (mut store, bound, binding, index) = computed_binding_fixture(&parsed, file);
        let (string, error) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.error_type)
        };
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(object, None, None, None, None, None));
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();

        for no_implicit_any in [false, true] {
            let before = (
                store.type_len(),
                store.signature_len(),
                store.checker_link_allocated_lengths(),
            );
            let checked = check_computed_binding_element_worker(
                &mut store,
                &host,
                None,
                CanonicalCheckerOptions {
                    no_implicit_any,
                    ..CanonicalCheckerOptions::default()
                },
                binding,
                object,
                string,
            )
            .unwrap();

            assert_eq!(checked.type_, error);
            let diagnostic = checked.diagnostic.unwrap();
            assert_eq!(diagnostic.node, Some(index));
            assert_eq!(diagnostic.diagnostic.code(), 2537);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                "Type '{}' has no matching index signature for type 'string'."
            );
            let range = parsed.arena.get(index.node).unwrap().range;
            assert_eq!(
                &source[range.start.get() as usize..range.end.get() as usize],
                "foo2()"
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.signature_len(),
                    store.checker_link_allocated_lengths(),
                ),
                before
            );
        }
    }

    #[test]
    fn computed_binding_uses_matching_index_signatures_without_diagnostics() {
        let parsed = parse_fixture("let { [key()]: value } = {}; ");
        let file = FileId::new(641);
        let (mut store, bound, binding, _) = computed_binding_fixture(&parsed, file);
        let (string, number, any, error) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.any_type,
                bootstrap.error_type,
            )
        };
        let object = index_object(&mut store, string, number);
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();

        for index in [string, number, any, error] {
            assert_eq!(
                check_computed_binding_element_worker(
                    &mut store,
                    &host,
                    None,
                    CanonicalCheckerOptions::default(),
                    binding,
                    object,
                    index,
                ),
                Ok(CheckedSourceElement {
                    type_: number,
                    diagnostic: None,
                })
            );
        }
    }

    #[test]
    fn computed_binding_any_keys_prefer_applicable_number_index_signatures() {
        let parsed = parse_fixture("let { [key]: value } = {}; ");
        let file = FileId::new(10_401);
        let (mut store, bound, binding, _) = computed_binding_fixture(&parsed, file);
        let (string, number, any) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.any_type,
            )
        };
        let string_index = store
            .alloc_index_info(string, any, false, None, Vec::new())
            .unwrap();
        let number_index = store
            .alloc_index_info(number, number, false, None, Vec::new())
            .unwrap();
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(
            object,
            None,
            None,
            None,
            None,
            Some(vec![string_index, number_index]),
        ));
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();

        let checked = check_computed_binding_element_worker(
            &mut store,
            &host,
            None,
            CanonicalCheckerOptions::default(),
            binding,
            object,
            any,
        )
        .unwrap();

        assert_eq!(checked.type_, number);
        assert!(checked.diagnostic.is_none());
    }

    #[test]
    fn computed_binding_missing_indices_preserve_any_and_error_identity_without_writes() {
        let parsed = parse_fixture("let { [key]: value } = {}; ");
        let file = FileId::new(10_402);
        let (mut store, bound, binding, index) = computed_binding_fixture(&parsed, file);
        let (any, error, boolean, never) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.any_type,
                bootstrap.error_type,
                bootstrap.boolean_type,
                bootstrap.never_type,
            )
        };
        let object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, None)
            .unwrap();
        assert!(store.set_structured_type_members(object, None, None, None, None, None));
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let before = (
            store.type_len(),
            store.signature_len(),
            store.checker_link_allocated_lengths(),
        );

        for (key, expected_type, display) in [
            (any, any, Some("any")),
            (error, error, Some("any")),
            (boolean, error, Some("boolean")),
            (never, never, None),
        ] {
            let checked = check_computed_binding_element_worker(
                &mut store,
                &host,
                None,
                CanonicalCheckerOptions::default(),
                binding,
                object,
                key,
            )
            .unwrap();

            assert_eq!(checked.type_, expected_type);
            if let Some(display) = display {
                let diagnostic = checked.diagnostic.unwrap();
                assert_eq!(diagnostic.node, Some(index));
                assert_eq!(diagnostic.diagnostic.code(), 2538);
                assert_eq!(diagnostic.diagnostic.arguments, [display]);
            } else {
                assert!(checked.diagnostic.is_none());
            }
            assert_eq!(
                (
                    store.type_len(),
                    store.signature_len(),
                    store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn computed_binding_rejects_counterfeit_any_before_receiver_lookup() {
        let parsed = parse_fixture("let { [key]: value } = {}; ");
        let file = FileId::new(10_414);
        let (mut store, bound, binding, _) = computed_binding_fixture(&parsed, file);
        let (any, string, number, empty) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.any_type,
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.empty_object_type,
            )
        };
        let counterfeit = store.alloc_intrinsic_type(TypeFlags::ANY, "any").unwrap();
        let indexed = index_object(&mut store, string, number);
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let before = (
            store.type_len(),
            store.signature_len(),
            store.checker_link_allocated_lengths(),
        );

        for receiver in [any, empty, indexed] {
            assert_eq!(
                check_computed_binding_element_worker(
                    &mut store,
                    &host,
                    None,
                    CanonicalCheckerOptions::default(),
                    binding,
                    receiver,
                    counterfeit,
                ),
                Err(SourceElementError::Literal(
                    LiteralTypeCacheError::UnsupportedUnionConstituent(counterfeit),
                )),
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.signature_len(),
                    store.checker_link_allocated_lengths(),
                ),
                before,
            );
        }
    }

    #[test]
    fn computed_binding_rejects_poisoned_key_caches_before_diagnostics() {
        let parsed = parse_fixture("let { [key()]: value = 'fallback' } = {}; ");
        let file = FileId::new(642);
        let (mut store, bound, binding, index) = computed_binding_fixture(&parsed, file);
        let (string, number, receiver) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.empty_object_type,
            )
        };
        assert!(store.set_type_node_links(
            index,
            TypeNodeLinks {
                resolved_type: Some(number),
                ..TypeNodeLinks::default()
            },
        ));
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let before = (
            store.type_len(),
            store.signature_len(),
            store.checker_link_allocated_lengths(),
        );

        assert_eq!(
            check_computed_binding_element_worker(
                &mut store,
                &host,
                None,
                CanonicalCheckerOptions::default(),
                binding,
                receiver,
                string,
            ),
            Err(SourceElementError::InvalidCache(index))
        );
        assert_eq!(
            (
                store.type_len(),
                store.signature_len(),
                store.checker_link_allocated_lengths(),
            ),
            before
        );
    }

    #[test]
    fn bound_declared_index_member_rejects_cloned_nonowner_table() {
        let parsed = parse_fixture("type Table = { [key: string]: number };");
        let file = FileId::new(600);
        let mut store = registered_store(&parsed, file);
        let literal = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::TypeLiteral).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::IndexSignature).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let members = store.alloc_symbol_table();
        let owner = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::TYPE_LITERAL,
                EscapedName::internal(InternalSymbolName::Type),
            ))
            .unwrap();
        assert!(store.set_symbol_declarations(owner, Some(vec![literal]), None));
        assert!(store.set_symbol_relationships(owner, Some(members), None, None, None));
        let symbol = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::SIGNATURE,
                EscapedName::internal(InternalSymbolName::Index),
            ))
            .unwrap();
        assert!(store.set_symbol_declarations(symbol, Some(vec![declaration]), None));
        assert!(store.set_symbol_relationships(symbol, None, None, Some(owner), None));
        assert_eq!(
            store.insert_symbol(
                members,
                EscapedName::internal(InternalSymbolName::Index),
                symbol,
            ),
            Some(None)
        );
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let index = store
            .alloc_index_info(string, number, false, Some(declaration), Vec::new())
            .unwrap();
        assert!(valid_bound_declared_index_member(
            &store,
            Some(owner),
            members,
            &[index],
        ));

        let replacement = store.clone_symbol_table(members).unwrap();
        assert_eq!(
            store
                .symbol_table(replacement)
                .and_then(|table| table.get(InternalSymbolName::Index.as_ref())),
            Some(symbol)
        );
        assert!(!valid_bound_declared_index_member(
            &store,
            Some(owner),
            replacement,
            &[index],
        ));
    }

    #[test]
    fn enum_member_literals_classify_as_their_numeric_and_string_values() {
        let parsed = parse_fixture("enum Keys { Zero = 0, Label = 'name' }");
        let file = FileId::new(620);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/enum-element-keys.ts\""),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        let (symbols, files) = binder.finish().try_into_parts().unwrap();
        let bound = &files[&file];
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::EnumDeclaration).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        let owner = bound.symbol(declaration).unwrap();
        let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        let host = DeclaredTypeHost::new([(&parsed.arena, bound)]).unwrap();
        let enumeration = enums::get_enum_semantics(&mut store, &host, owner).unwrap();

        for (member, name, numeric_name) in [
            (&enumeration.members[0], "0", true),
            (&enumeration.members[1], "name", false),
        ] {
            let expected = ClassifiedIndex {
                shape: IndexShape::Literal { numeric_name },
                property_name: Some(name.to_owned()),
            };
            assert_eq!(
                classify_index(&store, member.regular_type),
                Ok(expected.clone())
            );
            assert_eq!(classify_index(&store, member.fresh_type), Ok(expected));
        }
    }

    #[test]
    fn enum_string_element_reads_publish_exact_member_links_cold_and_warm() {
        for (offset, declaration) in [(0, "enum"), (1, "const enum")] {
            let parsed = parse_fixture(&format!(
                "{declaration} Status {{ Ready = 1 }} const result = Status[\"Ready\"];"
            ));
            let file = FileId::new(621 + offset);
            let (mut store, bound, enumeration) = published_enum(&parsed, file);
            let member = &enumeration.members[0];
            let index = store.regular_string_literal_type("Ready".into()).unwrap();
            let plan = enum_element_plan(&parsed, file, &store, enumeration.symbol, "Ready");
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            let targets =
                CanonicalArrayTargets::for_single_target_validation(enumeration.value_type);

            for _ in 0..2 {
                assert_eq!(
                    check_direct_source_element_with_array_targets(
                        &mut store,
                        &host,
                        targets,
                        CanonicalCheckerOptions::default(),
                        &plan,
                        enumeration.value_type,
                        index,
                    ),
                    Ok(CheckedSourceElement {
                        type_: member.fresh_type,
                        diagnostic: None,
                    }),
                );
            }
            assert_eq!(
                store
                    .type_node_links(plan.node)
                    .and_then(|links| links.resolved_type),
                Some(member.fresh_type),
            );
            assert_eq!(
                store
                    .symbol_node_links(plan.node)
                    .and_then(|links| links.resolved_symbol),
                Some(member.symbol),
            );
        }
    }

    #[test]
    fn missing_const_enum_elements_issue_direct_ts2339_on_the_string_index() {
        for (offset, declaration, no_implicit_any, expected_code) in [
            (0, "const enum", false, Some(2339)),
            (1, "const enum", true, Some(2339)),
            (2, "enum", false, None),
            (3, "enum", true, Some(7015)),
        ] {
            let parsed = parse_fixture(&format!(
                "{declaration} Status {{ Ready }} const result = Status[\"Missing\"];"
            ));
            let file = FileId::new(623 + offset);
            let (mut store, bound, enumeration) = published_enum(&parsed, file);
            let index = store.regular_string_literal_type("Missing".into()).unwrap();
            let plan = enum_element_plan(&parsed, file, &store, enumeration.symbol, "Missing");
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            let options = CanonicalCheckerOptions {
                no_implicit_any,
                ..CanonicalCheckerOptions::default()
            };
            let checked = check_direct_source_element_with_array_targets(
                &mut store,
                &host,
                CanonicalArrayTargets::for_single_target_validation(enumeration.value_type),
                options,
                &plan,
                enumeration.value_type,
                index,
            )
            .unwrap();

            assert_eq!(
                checked
                    .diagnostic
                    .as_ref()
                    .map(|diagnostic| diagnostic.diagnostic.code()),
                expected_code,
            );
            if let Some(diagnostic) = checked.diagnostic {
                assert_eq!(diagnostic.node, Some(plan.index.node));
                if expected_code == Some(2339) {
                    assert_eq!(
                        diagnostic.diagnostic.render().unwrap(),
                        "Property 'Missing' does not exist on type 'typeof Status'.",
                    );
                } else if expected_code == Some(7015) {
                    assert_eq!(
                        diagnostic.diagnostic.render().unwrap(),
                        "Element implicitly has an 'any' type because index expression is not of type 'number'.",
                    );
                }
            }
            assert_eq!(
                checked.type_,
                store.intrinsic_bootstrap().unwrap().error_type,
            );
            assert!(store.symbol_node_links(plan.node).is_none());
        }
    }

    #[test]
    fn dynamic_const_enum_indices_report_ts2476_on_the_complete_index() {
        #[derive(Clone, Copy)]
        enum Index {
            Number,
            KnownString,
            BroadString,
            LiteralUnion,
        }

        for (offset, source, index_kind) in [
            (
                0,
                "const enum Status { Ready = 1 } const result = Status[0];",
                Index::Number,
            ),
            (
                1,
                "const enum Status { Ready = 1 } const key = 'Ready'; const result = Status[key];",
                Index::KnownString,
            ),
            (
                2,
                "const enum Status { Ready = 1 } let key: string = 'Ready'; const result = Status[key];",
                Index::BroadString,
            ),
            (
                3,
                "const enum Status { Ready = 1, Done = 2 } let key: 'Ready' | 'Done'; const result = Status[key];",
                Index::LiteralUnion,
            ),
        ] {
            let parsed = parse_fixture(source);
            let file = FileId::new(630 + offset);
            let (mut store, bound, enumeration) = published_enum(&parsed, file);
            let (expression, index) = match index_kind {
                Index::Number => {
                    let value = ts_jsnum::Number::new(0.0);
                    (
                        PlannedExpressionKind::Number {
                            value,
                            unary_operand: None,
                        },
                        store.regular_number_literal_type(value).unwrap(),
                    )
                }
                Index::KnownString | Index::BroadString | Index::LiteralUnion => {
                    let key = bound
                        .locals(bound.source_file())
                        .and_then(|locals| store.symbol_table(locals))
                        .and_then(|locals| locals.get_source("key"))
                        .unwrap();
                    let type_ = match index_kind {
                        Index::KnownString => {
                            store.regular_string_literal_type("Ready".into()).unwrap()
                        }
                        Index::BroadString => store.intrinsic_bootstrap().unwrap().string_type,
                        Index::LiteralUnion => {
                            let ready = store.regular_string_literal_type("Ready".into()).unwrap();
                            let done = store.regular_string_literal_type("Done".into()).unwrap();
                            store
                                .expression_union_type(&[ready, done], UnionReduction::Literal)
                                .unwrap()
                        }
                        Index::Number => unreachable!("numeric indices use a literal expression"),
                    };
                    (
                        PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                            resolved_symbol: key,
                            value_symbol: key,
                            kind: PlannedIdentifierReadKind::Variable,
                        }),
                        type_,
                    )
                }
            };
            let plan = enum_index_plan(&parsed, file, &store, enumeration.symbol, expression);
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            let targets =
                CanonicalArrayTargets::for_single_target_validation(enumeration.value_type);

            for _ in 0..2 {
                let checked = check_direct_source_element_with_array_targets(
                    &mut store,
                    &host,
                    targets,
                    CanonicalCheckerOptions::default(),
                    &plan,
                    enumeration.value_type,
                    index,
                )
                .unwrap();
                assert_eq!(
                    checked.type_,
                    store.intrinsic_bootstrap().unwrap().error_type,
                );
                let diagnostic = checked.diagnostic.unwrap();
                assert_eq!(diagnostic.node, Some(plan.index.node));
                assert_eq!(diagnostic.diagnostic.code(), 2476);
                assert_eq!(
                    diagnostic.diagnostic.render().unwrap(),
                    "A const enum member can only be accessed using a string literal.",
                );
            }
            assert!(store.symbol_node_links(plan.node).is_none());
        }
    }

    #[test]
    fn quoted_numeric_enum_indices_follow_the_numeric_index_signature() {
        for (offset, declaration, initializer, name, expected_code) in [
            (0, "const enum", "1", "1", None),
            (1, "const enum", "1", "NaN", None),
            (2, "const enum", "1", "01", Some(2339)),
            (3, "enum", "1", "1", None),
            (4, "enum", "1", "NaN", None),
            (5, "enum", "1", "01", Some(7015)),
            (6, "const enum", "'ready'", "1", Some(2339)),
            (7, "enum", "'ready'", "1", Some(7053)),
        ] {
            let parsed = parse_fixture(&format!(
                "{declaration} Status {{ Ready = {initializer} }} const result = Status[\"{name}\"];"
            ));
            let file = FileId::new(638 + offset);
            let (mut store, bound, enumeration) = published_enum(&parsed, file);
            let index = store.regular_string_literal_type(name.into()).unwrap();
            let plan = enum_element_plan(&parsed, file, &store, enumeration.symbol, name);
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let expected_type = if expected_code.is_some() {
                bootstrap.error_type
            } else {
                bootstrap.string_type
            };

            for _ in 0..2 {
                let checked = check_direct_source_element_with_array_targets(
                    &mut store,
                    &host,
                    CanonicalArrayTargets::for_single_target_validation(enumeration.value_type),
                    strict_options(),
                    &plan,
                    enumeration.value_type,
                    index,
                )
                .unwrap();

                assert_eq!(checked.type_, expected_type);
                assert_eq!(
                    checked
                        .diagnostic
                        .as_ref()
                        .map(|diagnostic| diagnostic.diagnostic.code()),
                    expected_code,
                );
                if let Some(diagnostic) = checked.diagnostic {
                    let expected_node = if expected_code == Some(7053) {
                        plan.node
                    } else {
                        plan.index.node
                    };
                    assert_eq!(diagnostic.node, Some(expected_node));
                }
            }
            assert!(store.symbol_node_links(plan.node).is_none());
        }
    }

    #[test]
    fn regular_numeric_enum_reverse_indices_return_string_cold_and_warm() {
        #[derive(Clone, Copy)]
        enum Index {
            Number,
            NumericMember,
            ComputedMember,
        }

        for (offset, source, index_kind) in [
            (
                0,
                "enum Status { Ready = 1, Done = 2 } const result = Status[0];",
                Index::Number,
            ),
            (
                1,
                "enum Status { Ready = 1, Done = 2 } const value = Status.Ready; const result = Status[value];",
                Index::NumericMember,
            ),
            (
                2,
                "declare function compute(): number; enum Status { Ready = compute() } const value = Status.Ready; const result = Status[value];",
                Index::ComputedMember,
            ),
        ] {
            let parsed = parse_fixture(source);
            let file = FileId::new(633 + offset);
            let (mut store, bound, enumeration) = published_enum(&parsed, file);
            let (expression, index) = match index_kind {
                Index::Number => {
                    let value = ts_jsnum::Number::new(0.0);
                    (
                        PlannedExpressionKind::Number {
                            value,
                            unary_operand: None,
                        },
                        store.regular_number_literal_type(value).unwrap(),
                    )
                }
                Index::NumericMember | Index::ComputedMember => {
                    let value = bound
                        .locals(bound.source_file())
                        .and_then(|locals| store.symbol_table(locals))
                        .and_then(|locals| locals.get_source("value"))
                        .unwrap();
                    (
                        PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                            resolved_symbol: value,
                            value_symbol: value,
                            kind: PlannedIdentifierReadKind::Variable,
                        }),
                        enumeration.members[0].fresh_type,
                    )
                }
            };
            let plan = enum_index_plan(&parsed, file, &store, enumeration.symbol, expression);
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
            let string = store.intrinsic_bootstrap().unwrap().string_type;
            let targets =
                CanonicalArrayTargets::for_single_target_validation(enumeration.value_type);

            for _ in 0..2 {
                assert_eq!(
                    check_direct_source_element_with_array_targets(
                        &mut store,
                        &host,
                        targets,
                        CanonicalCheckerOptions::default(),
                        &plan,
                        enumeration.value_type,
                        index,
                    ),
                    Ok(CheckedSourceElement {
                        type_: string,
                        diagnostic: None,
                    }),
                );
            }
            assert_eq!(
                store
                    .type_node_links(plan.node)
                    .and_then(|links| links.resolved_type),
                Some(string),
            );
            assert!(store.symbol_node_links(plan.node).is_none());
        }
    }

    #[test]
    fn regular_enum_variable_string_keys_preserve_the_fresh_member_identity() {
        let parsed = parse_fixture(
            "enum Status { Ready = 1 } const key = 'Ready'; const result = Status[key];",
        );
        let file = FileId::new(636);
        let (mut store, bound, enumeration) = published_enum(&parsed, file);
        let key = bound
            .locals(bound.source_file())
            .and_then(|locals| store.symbol_table(locals))
            .and_then(|locals| locals.get_source("key"))
            .unwrap();
        let regular = store.regular_string_literal_type("Ready".into()).unwrap();
        let index = store.fresh_type_of_literal_type(regular).unwrap();
        let plan = enum_index_plan(
            &parsed,
            file,
            &store,
            enumeration.symbol,
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: key,
                value_symbol: key,
                kind: PlannedIdentifierReadKind::Variable,
            }),
        );
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let member = &enumeration.members[0];

        assert_eq!(
            check_direct_source_element_with_array_targets(
                &mut store,
                &host,
                CanonicalArrayTargets::for_single_target_validation(enumeration.value_type),
                CanonicalCheckerOptions::default(),
                &plan,
                enumeration.value_type,
                index,
            ),
            Ok(CheckedSourceElement {
                type_: member.fresh_type,
                diagnostic: None,
            }),
        );
        assert_eq!(
            store
                .symbol_node_links(plan.node)
                .and_then(|links| links.resolved_symbol),
            Some(member.symbol),
        );
    }

    #[test]
    fn string_only_regular_enums_do_not_gain_numeric_reverse_indices() {
        let parsed = parse_fixture("enum Status { Ready = 'ready' } const result = Status[0];");
        let file = FileId::new(637);
        let (mut store, bound, enumeration) = published_enum(&parsed, file);
        let value = ts_jsnum::Number::new(0.0);
        let index = store.regular_number_literal_type(value).unwrap();
        let plan = enum_index_plan(
            &parsed,
            file,
            &store,
            enumeration.symbol,
            PlannedExpressionKind::Number {
                value,
                unary_operand: None,
            },
        );
        let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();
        let checked = check_direct_source_element_with_array_targets(
            &mut store,
            &host,
            CanonicalArrayTargets::for_single_target_validation(enumeration.value_type),
            strict_options(),
            &plan,
            enumeration.value_type,
            index,
        )
        .unwrap();

        assert_eq!(
            checked.type_,
            store.intrinsic_bootstrap().unwrap().error_type,
        );
        assert_eq!(checked.diagnostic.unwrap().diagnostic.code(), 7053);
        assert!(store.symbol_node_links(plan.node).is_none());
    }

    #[test]
    fn any_enum_indices_follow_numeric_signatures_and_const_enum_restrictions() {
        for (offset, declaration, initializer, expected_code) in [
            (0, "enum", "1", None),
            (1, "enum", "'ready'", Some(7053)),
            (2, "const enum", "1", Some(2476)),
        ] {
            let parsed = parse_fixture(&format!(
                "{declaration} Status {{ Ready = {initializer} }} let key: any; const result = Status[key];"
            ));
            let file = FileId::new(646 + offset);
            let (mut store, bound, enumeration) = published_enum(&parsed, file);
            let key = bound
                .locals(bound.source_file())
                .and_then(|locals| store.symbol_table(locals))
                .and_then(|locals| locals.get_source("key"))
                .unwrap();
            let plan = enum_index_plan(
                &parsed,
                file,
                &store,
                enumeration.symbol,
                PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                    resolved_symbol: key,
                    value_symbol: key,
                    kind: PlannedIdentifierReadKind::Variable,
                }),
            );
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let index = bootstrap.any_type;
            let expected_type = if expected_code.is_some() {
                bootstrap.error_type
            } else {
                bootstrap.string_type
            };
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();

            let checked = check_direct_source_element_with_array_targets(
                &mut store,
                &host,
                CanonicalArrayTargets::for_single_target_validation(enumeration.value_type),
                strict_options(),
                &plan,
                enumeration.value_type,
                index,
            )
            .unwrap();

            assert_eq!(checked.type_, expected_type);
            assert_eq!(
                checked
                    .diagnostic
                    .as_ref()
                    .map(|diagnostic| diagnostic.diagnostic.code()),
                expected_code,
            );
            if let Some(diagnostic) = checked.diagnostic {
                let expected_node = if expected_code == Some(2476) {
                    plan.index.node
                } else {
                    plan.node
                };
                assert_eq!(diagnostic.node, Some(expected_node));
                if expected_code == Some(7053) {
                    assert_eq!(
                        diagnostic.diagnostic.render().unwrap(),
                        "Element implicitly has an 'any' type because expression of type 'any' can't be used to index type 'typeof Status'.",
                    );
                }
            }
            assert!(store.symbol_node_links(plan.node).is_none());
        }
    }

    #[test]
    fn poisoned_enum_element_owner_exports_and_member_links_fail_closed() {
        #[derive(Clone, Copy)]
        enum Poison {
            OwnerValue,
            Exports,
            MemberValue,
        }

        for (offset, poison) in [Poison::OwnerValue, Poison::Exports, Poison::MemberValue]
            .into_iter()
            .enumerate()
        {
            let parsed =
                parse_fixture("const enum Status { Ready = 1 } const result = Status[\"Ready\"];");
            let file = FileId::new(627 + u32::try_from(offset).unwrap());
            let (mut store, bound, enumeration) = published_enum(&parsed, file);
            let member = &enumeration.members[0];
            let index = store.regular_string_literal_type("Ready".into()).unwrap();
            let plan = enum_element_plan(&parsed, file, &store, enumeration.symbol, "Ready");
            let error = store.intrinsic_bootstrap().unwrap().error_type;
            match poison {
                Poison::OwnerValue => assert!(store.set_value_symbol_links(
                    enumeration.symbol,
                    ValueSymbolLinks {
                        resolved_type: Some(error),
                        ..ValueSymbolLinks::default()
                    },
                )),
                Poison::Exports => {
                    let exports = store.alloc_symbol_table();
                    assert!(store.set_symbol_relationships(
                        enumeration.symbol,
                        None,
                        Some(exports),
                        None,
                        None,
                    ));
                }
                Poison::MemberValue => assert!(store.set_value_symbol_links(
                    member.symbol,
                    ValueSymbolLinks {
                        resolved_type: Some(error),
                        ..ValueSymbolLinks::default()
                    },
                )),
            }
            let host = DeclaredTypeHost::new([(&parsed.arena, &bound)]).unwrap();

            assert_eq!(
                check_direct_source_element_with_array_targets(
                    &mut store,
                    &host,
                    CanonicalArrayTargets::for_single_target_validation(enumeration.value_type),
                    CanonicalCheckerOptions::default(),
                    &plan,
                    enumeration.value_type,
                    index,
                ),
                Err(SourceElementError::InvalidCache(plan.node)),
            );
            assert!(store.type_node_links(plan.node).is_none());
            assert!(store.symbol_node_links(plan.node).is_none());
        }
    }

    #[test]
    fn literal_property_read_publishes_exact_symbol_and_type_cold_and_warm() {
        let parsed = parse_fixture("const result = object[\"known\"];");
        let file = FileId::new(601);
        let mut store = registered_store(&parsed, file);
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let index = store.regular_string_literal_type("known".into()).unwrap();
        let (object, property) = property_object(&mut store, "known", number, false);
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "object");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::String("known".into()),
            receiver_symbol,
        );
        let targets = CanonicalArrayTargets::for_single_target_validation(object);
        let host = empty_host();

        for _ in 0..2 {
            assert_eq!(
                check_direct_source_element_with_array_targets(
                    &mut store,
                    &host,
                    targets,
                    strict_options(),
                    &plan,
                    object,
                    index,
                ),
                Ok(CheckedSourceElement {
                    type_: number,
                    diagnostic: None,
                })
            );
        }
        assert_eq!(
            store
                .type_node_links(plan.node)
                .and_then(|links| links.resolved_type),
            Some(number)
        );
        assert_eq!(
            store
                .symbol_node_links(plan.node)
                .and_then(|links| links.resolved_symbol),
            Some(property)
        );
    }

    #[test]
    fn optional_literal_property_reads_include_undefined_under_strict_null_checks() {
        let parsed = parse_fixture("const result = object[\"value\"];");
        let file = FileId::new(614);
        let mut store = registered_store(&parsed, file);
        let (string, undefined) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.undefined_or_missing_type)
        };
        let index = store.regular_string_literal_type("value".into()).unwrap();
        let (object, property) = property_object(&mut store, "value", string, true);
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "object");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::String("value".into()),
            receiver_symbol,
        );

        let checked = check_direct_source_element_with_array_targets(
            &mut store,
            &empty_host(),
            CanonicalArrayTargets::for_single_target_validation(object),
            strict_options(),
            &plan,
            object,
            index,
        )
        .unwrap();
        let TypeData::Union(union) = store.type_payload(checked.type_).unwrap().data() else {
            panic!("strict optional property access must produce a union")
        };
        assert!(union.union.types.contains(&string));
        assert!(union.union.types.contains(&undefined));
        assert_eq!(
            store
                .symbol_node_links(plan.node)
                .and_then(|links| links.resolved_symbol),
            Some(property),
        );
    }

    #[test]
    fn optional_element_chains_remove_nullish_receivers_and_restore_undefined() {
        let parsed = parse_fixture("const result = object?.[\"value\"];");
        let file = FileId::new(615);
        let mut store = registered_store(&parsed, file);
        let (string, undefined) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.undefined_type)
        };
        let index = store.regular_string_literal_type("value".into()).unwrap();
        let (object, property) = property_object(&mut store, "value", string, false);
        let nullable = store
            .alloc_union_type(ObjectFlags::NONE, vec![undefined, object])
            .unwrap();
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "object");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::String("value".into()),
            receiver_symbol,
        );

        let checked = check_direct_source_element_with_array_targets(
            &mut store,
            &empty_host(),
            CanonicalArrayTargets::for_single_target_validation(object),
            strict_options(),
            &plan,
            nullable,
            index,
        )
        .unwrap();
        let TypeData::Union(union) = store.type_payload(checked.type_).unwrap().data() else {
            panic!("optional element access must preserve undefined")
        };
        assert!(union.union.types.contains(&string));
        assert!(union.union.types.contains(&undefined));
        assert_eq!(
            store
                .symbol_node_links(plan.node)
                .and_then(|links| links.resolved_symbol),
            Some(property),
        );
    }

    #[test]
    fn array_number_reads_return_the_element_and_wrong_strings_emit_ts7015() {
        let parsed = parse_fixture("const first = array[0];");
        let file = FileId::new(602);
        let mut store = registered_store(&parsed, file);
        let (number, string) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let zero = store
            .regular_number_literal_type(ts_jsnum::Number::new(0.0))
            .unwrap();
        let target = canonical_array_target(&mut store);
        let array =
            create_type_from_generic_global_type(&mut store, target, number, ObjectFlags::NONE)
                .unwrap();
        let receiver_symbol = alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "array");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::Number {
                value: ts_jsnum::Number::new(0.0),
                unary_operand: None,
            },
            receiver_symbol,
        );
        let host = empty_host();
        let targets = CanonicalArrayTargets::for_test(target, target);
        assert_eq!(
            check_direct_source_element_with_array_targets(
                &mut store,
                &host,
                targets,
                strict_options(),
                &plan,
                array,
                zero,
            ),
            Ok(CheckedSourceElement {
                type_: number,
                diagnostic: None,
            })
        );

        let wrong_parsed = parse_fixture("const wrong = array[\"wrong\"];");
        let wrong_file = FileId::new(603);
        assert!(
            store
                .register_source_file(&wrong_parsed.arena, wrong_parsed.source_file, wrong_file,)
                .is_some()
        );
        let wrong = store.regular_string_literal_type("wrong".into()).unwrap();
        let wrong_plan = source_plan(
            &wrong_parsed,
            wrong_file,
            &store,
            PlannedExpressionKind::String("wrong".into()),
            receiver_symbol,
        );
        let checked = check_direct_source_element_with_array_targets(
            &mut store,
            &host,
            targets,
            strict_options(),
            &wrong_plan,
            array,
            wrong,
        )
        .unwrap();
        assert_eq!(
            checked.type_,
            store.intrinsic_bootstrap().unwrap().error_type
        );
        let diagnostic = checked.diagnostic.unwrap();
        assert_eq!(diagnostic.node, Some(wrong_plan.index.node));
        assert_eq!(diagnostic.diagnostic.code(), 7015);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Element implicitly has an 'any' type because index expression is not of type 'number'."
        );
        assert_eq!(string, store.intrinsic_bootstrap().unwrap().string_type);
    }

    #[test]
    fn fixed_tuple_indices_return_the_exact_positional_element() {
        let parsed = parse_fixture("const result = tuple[1];");
        let file = FileId::new(612);
        let mut store = registered_store(&parsed, file);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let elements = [string, number];
        let infos = [
            store
                .create_tuple_element_info(ElementFlags::REQUIRED, None)
                .unwrap(),
            store
                .create_tuple_element_info(ElementFlags::REQUIRED, None)
                .unwrap(),
        ];
        let tuple = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&elements, &infos, false))
            .unwrap();
        let array_target = canonical_array_target(&mut store);
        let receiver_symbol = alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "tuple");
        let one = store
            .regular_number_literal_type(ts_jsnum::Number::new(1.0))
            .unwrap();
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::Number {
                value: ts_jsnum::Number::new(1.0),
                unary_operand: None,
            },
            receiver_symbol,
        );

        for no_unchecked_indexed_access in [false, true] {
            assert_eq!(
                check_direct_source_element_with_array_targets(
                    &mut store,
                    &empty_host(),
                    CanonicalArrayTargets::for_test(array_target, array_target),
                    CanonicalCheckerOptions {
                        no_unchecked_indexed_access,
                        ..strict_options()
                    },
                    &plan,
                    tuple,
                    one,
                ),
                Ok(CheckedSourceElement {
                    type_: number,
                    diagnostic: None,
                }),
            );
        }
    }

    #[test]
    fn fixed_tuple_out_of_bounds_indices_emit_ts2493_without_no_implicit_any() {
        for (file_id, source, nonempty, index, expected) in [
            (
                613,
                "const result = tuple[0];",
                false,
                0_u32,
                "Tuple type '[]' of length '0' has no element at index '0'.",
            ),
            (
                616,
                "const result = tuple[2];",
                true,
                2_u32,
                "Tuple type '[string]' of length '1' has no element at index '2'.",
            ),
        ] {
            let parsed = parse_fixture(source);
            let file = FileId::new(file_id);
            let mut store = registered_store(&parsed, file);
            let (string, undefined) = {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                (bootstrap.string_type, bootstrap.undefined_type)
            };
            let tuple = if nonempty {
                let info = store
                    .create_tuple_element_info(ElementFlags::REQUIRED, None)
                    .unwrap();
                store
                    .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                        &[string],
                        &[info],
                        false,
                    ))
                    .unwrap()
            } else {
                store.create_canonical_empty_tuple_type().unwrap()
            };
            let array_target = canonical_array_target(&mut store);
            let receiver_symbol =
                alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "tuple");
            let value = ts_jsnum::Number::new(f64::from(index));
            let index_type = store.regular_number_literal_type(value).unwrap();
            let plan = source_plan(
                &parsed,
                file,
                &store,
                PlannedExpressionKind::Number {
                    value,
                    unary_operand: None,
                },
                receiver_symbol,
            );

            let checked = check_direct_source_element_with_array_targets(
                &mut store,
                &empty_host(),
                CanonicalArrayTargets::for_test(array_target, array_target),
                CanonicalCheckerOptions::default(),
                &plan,
                tuple,
                index_type,
            )
            .unwrap();
            assert_eq!(checked.type_, undefined);
            let diagnostic = checked.diagnostic.unwrap();
            assert_eq!(diagnostic.node, Some(plan.index.node));
            assert_eq!(diagnostic.diagnostic.code(), 2493);
            assert_eq!(diagnostic.diagnostic.render().unwrap(), expected);
        }
    }

    #[test]
    fn missing_literal_and_broad_object_keys_emit_exact_ts7053_chains() {
        for (offset, source, literal_name, expected_index, expected_detail) in [
            (
                0,
                "const result = object[\"missing\"];",
                Some("missing"),
                "\"missing\"",
                "  Property 'missing' does not exist on type '{ known: number; }'.",
            ),
            (
                1,
                "const result = object[key];",
                None,
                "string",
                "  No index signature with a parameter of type 'string' was found on type '{ known: number; }'.",
            ),
        ] {
            let parsed = parse_fixture(source);
            let file = FileId::new(604 + offset);
            let mut store = registered_store(&parsed, file);
            let (number, string) = {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                (bootstrap.number_type, bootstrap.string_type)
            };
            let (object, _) = property_object(&mut store, "known", number, false);
            let receiver_symbol =
                alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "object");
            let index_type = if offset == 0 {
                store.regular_string_literal_type("missing".into()).unwrap()
            } else {
                string
            };
            let index_kind = if let Some(literal_name) = literal_name {
                PlannedExpressionKind::String(literal_name.into())
            } else {
                let key_symbol =
                    alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "key");
                PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                    resolved_symbol: key_symbol,
                    value_symbol: key_symbol,
                    kind: PlannedIdentifierReadKind::Variable,
                })
            };
            let plan = source_plan(&parsed, file, &store, index_kind, receiver_symbol);
            let host = empty_host();
            let checked = check_direct_source_element_with_array_targets(
                &mut store,
                &host,
                CanonicalArrayTargets::for_single_target_validation(object),
                strict_options(),
                &plan,
                object,
                index_type,
            )
            .unwrap();
            let diagnostic = checked.diagnostic.unwrap();
            assert_eq!(diagnostic.node, Some(plan.node));
            assert_eq!(diagnostic.diagnostic.code(), 7053);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                format!(
                    "Element implicitly has an 'any' type because expression of type '{expected_index}' can't be used to index type '{{ known: number; }}'.\n{expected_detail}"
                )
            );
        }
    }

    #[test]
    fn broad_keys_on_object_unions_emit_ts7053_for_the_complete_union() {
        let parsed = parse_fixture(concat!(
            "declare const key: string; ",
            "declare const object: ",
            "{ id: '00' } | { id: '01' } | { id: '02' }; ",
            "const result = object[key];",
        ));
        let file = FileId::new(617);
        let access = element_access(&parsed, file);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/union-element-access.ts\""),
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
            vec![(file, &parsed.arena)],
            strict_options(),
        )
        .unwrap();
        let expected_receiver = "{ id: \"00\"; } | { id: \"01\"; } | { id: \"02\"; }";

        for index in 0..2 {
            if index == 0 {
                context.check_source_file(file).unwrap();
            } else {
                context.recheck_source_file(file).unwrap();
            }
            let [diagnostic] = context.diagnostics().as_slice() else {
                panic!("expected one broad-key object-union diagnostic");
            };
            assert_eq!(diagnostic.node, Some(access));
            assert_eq!(diagnostic.diagnostic.code(), 7053);
            assert_eq!(
                diagnostic.diagnostic.render().unwrap(),
                format!(
                    "Element implicitly has an 'any' type because expression of type 'string' can't be used to index type '{expected_receiver}'.\n  No index signature with a parameter of type 'string' was found on type '{expected_receiver}'."
                )
            );
        }
        assert_eq!(
            context
                .store()
                .type_node_links(access)
                .and_then(|links| links.resolved_type),
            Some(context.store().intrinsic_bootstrap().unwrap().error_type),
        );
        assert!(context.store().symbol_node_links(access).is_none());
    }

    #[test]
    fn broad_keys_keep_union_index_signatures_as_an_explicit_boundary() {
        let parsed = parse_fixture("const result = object[key];");
        let file = FileId::new(618);
        let mut store = registered_store(&parsed, file);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let (object, _) = property_object(&mut store, "id", number, false);
        let dictionary = index_object(&mut store, string, number);
        let mut members = vec![object, dictionary];
        members.sort();
        let union = store.alloc_union_type(ObjectFlags::NONE, members).unwrap();
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "object");
        let key_symbol = alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "key");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: key_symbol,
                value_symbol: key_symbol,
                kind: PlannedIdentifierReadKind::Variable,
            }),
            receiver_symbol,
        );

        assert_eq!(
            check_direct_source_element_with_array_targets(
                &mut store,
                &empty_host(),
                CanonicalArrayTargets::for_single_target_validation(union),
                strict_options(),
                &plan,
                union,
                string,
            ),
            Err(SourceElementError::Unsupported(
                SourceElementUnsupported::IndexSignatureSurface(union),
            )),
        );
        assert!(store.type_node_links(plan.node).is_none());
        assert!(store.symbol_node_links(plan.node).is_none());
    }

    #[test]
    fn string_and_number_index_signatures_follow_pinned_applicability() {
        let parsed = parse_fixture("const result = dictionary[key];");
        let file = FileId::new(606);
        let mut store = registered_store(&parsed, file);
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let string_dictionary = index_object(&mut store, string, number);
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "dictionary");
        let key_symbol = alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "key");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: key_symbol,
                value_symbol: key_symbol,
                kind: PlannedIdentifierReadKind::Variable,
            }),
            receiver_symbol,
        );
        let host = empty_host();
        assert_eq!(
            check_direct_source_element_with_array_targets(
                &mut store,
                &host,
                CanonicalArrayTargets::for_single_target_validation(string_dictionary),
                strict_options(),
                &plan,
                string_dictionary,
                string,
            ),
            Ok(CheckedSourceElement {
                type_: number,
                diagnostic: None,
            })
        );

        let number_parsed = parse_fixture("const result = dictionary[\"0\"];");
        let number_file = FileId::new(607);
        assert!(
            store
                .register_source_file(&number_parsed.arena, number_parsed.source_file, number_file,)
                .is_some()
        );
        let number_dictionary = index_object(&mut store, number, string);
        let zero = store.regular_string_literal_type("0".into()).unwrap();
        let number_plan = source_plan(
            &number_parsed,
            number_file,
            &store,
            PlannedExpressionKind::String("0".into()),
            receiver_symbol,
        );
        assert_eq!(
            check_direct_source_element_with_array_targets(
                &mut store,
                &host,
                CanonicalArrayTargets::for_single_target_validation(number_dictionary),
                strict_options(),
                &number_plan,
                number_dictionary,
                zero,
            ),
            Ok(CheckedSourceElement {
                type_: string,
                diagnostic: None,
            })
        );
    }

    #[test]
    fn unchecked_index_signature_reads_include_undefined_without_changing_known_properties() {
        let parsed = parse_fixture("const result = dictionary[key];");
        let file = FileId::new(654);
        let mut store = registered_store(&parsed, file);
        let (string, number, undefined) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.undefined_type,
            )
        };
        let dictionary = index_object(&mut store, string, number);
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "dictionary");
        let key_symbol = alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "key");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: key_symbol,
                value_symbol: key_symbol,
                kind: PlannedIdentifierReadKind::Variable,
            }),
            receiver_symbol,
        );
        let checked = check_direct_source_element_with_array_targets(
            &mut store,
            &empty_host(),
            CanonicalArrayTargets::for_single_target_validation(dictionary),
            CanonicalCheckerOptions {
                no_unchecked_indexed_access: true,
                ..strict_options()
            },
            &plan,
            dictionary,
            string,
        )
        .unwrap();
        let TypeData::Union(union) = store.type_payload(checked.type_).unwrap().data() else {
            panic!("unchecked index signatures include undefined")
        };
        assert!(union.union.types.contains(&number));
        assert!(union.union.types.contains(&undefined));
        assert!(checked.diagnostic.is_none());

        let property_parsed = parse_fixture("const result = object[\"known\"];");
        let property_file = FileId::new(655);
        let mut property_store = registered_store(&property_parsed, property_file);
        let property_number = property_store.intrinsic_bootstrap().unwrap().number_type;
        let (object, property) =
            property_object(&mut property_store, "known", property_number, false);
        let receiver_symbol = alloc_symbol(
            &mut property_store,
            SymbolFlags::BLOCK_SCOPED_VARIABLE,
            "object",
        );
        let key = property_store
            .regular_string_literal_type("known".into())
            .unwrap();
        let plan = source_plan(
            &property_parsed,
            property_file,
            &property_store,
            PlannedExpressionKind::String("known".into()),
            receiver_symbol,
        );
        let checked = check_direct_source_element_with_array_targets(
            &mut property_store,
            &empty_host(),
            CanonicalArrayTargets::for_single_target_validation(object),
            CanonicalCheckerOptions {
                no_unchecked_indexed_access: true,
                ..strict_options()
            },
            &plan,
            object,
            key,
        )
        .unwrap();
        assert_eq!(checked.type_, property_number);
        assert_eq!(
            property_store
                .symbol_node_links(plan.node)
                .and_then(|links| links.resolved_symbol),
            Some(property)
        );
        assert!(checked.diagnostic.is_none());
    }

    #[test]
    fn unchecked_array_index_reads_include_undefined() {
        let parsed = parse_fixture("const first = array[0];");
        let file = FileId::new(656);
        let mut store = registered_store(&parsed, file);
        let (string, undefined) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.undefined_type)
        };
        let zero = store
            .regular_number_literal_type(ts_jsnum::Number::new(0.0))
            .unwrap();
        let target = canonical_array_target(&mut store);
        let array =
            create_type_from_generic_global_type(&mut store, target, string, ObjectFlags::NONE)
                .unwrap();
        let receiver_symbol = alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "array");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::Number {
                value: ts_jsnum::Number::new(0.0),
                unary_operand: None,
            },
            receiver_symbol,
        );

        let checked = check_direct_source_element_with_array_targets(
            &mut store,
            &empty_host(),
            CanonicalArrayTargets::for_test(target, target),
            CanonicalCheckerOptions {
                no_unchecked_indexed_access: true,
                ..strict_options()
            },
            &plan,
            array,
            zero,
        )
        .unwrap();
        let TypeData::Union(union) = store.type_payload(checked.type_).unwrap().data() else {
            panic!("unchecked array indices include undefined")
        };
        assert!(union.union.types.contains(&string));
        assert!(union.union.types.contains(&undefined));
        assert!(checked.diagnostic.is_none());
    }

    #[test]
    fn invalid_boolean_index_emits_ts2538_even_without_no_implicit_any() {
        let parsed = parse_fixture("const result = object[true];");
        let file = FileId::new(608);
        let mut store = registered_store(&parsed, file);
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let true_type = store.intrinsic_bootstrap().unwrap().true_type;
        let (object, _) = property_object(&mut store, "known", number, false);
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "object");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::Boolean(true),
            receiver_symbol,
        );
        let checked = check_direct_source_element_with_array_targets(
            &mut store,
            &empty_host(),
            CanonicalArrayTargets::for_single_target_validation(object),
            CanonicalCheckerOptions::default(),
            &plan,
            object,
            true_type,
        )
        .unwrap();
        let diagnostic = checked.diagnostic.unwrap();
        assert_eq!(diagnostic.node, Some(plan.index.node));
        assert_eq!(diagnostic.diagnostic.code(), 2538);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'true' cannot be used as an index type."
        );
    }

    #[test]
    fn bigint_literal_indices_report_the_widened_bigint_name() {
        let parsed = parse_fixture("const result = object[1n];");
        let file = FileId::new(6_608);
        let mut store = registered_store(&parsed, file);
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let value = ts_jsnum::PseudoBigInt::parse_valid("1n");
        let bigint = store.regular_bigint_literal_type(value.clone()).unwrap();
        let (object, _) = property_object(&mut store, "known", number, false);
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "object");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::BigInt {
                value,
                unary_operand: None,
            },
            receiver_symbol,
        );

        let checked = check_direct_source_element_with_array_targets(
            &mut store,
            &empty_host(),
            CanonicalArrayTargets::for_single_target_validation(object),
            CanonicalCheckerOptions::default(),
            &plan,
            object,
            bigint,
        )
        .unwrap();
        let diagnostic = checked.diagnostic.unwrap();
        assert_eq!(diagnostic.node, Some(plan.index.node));
        assert_eq!(diagnostic.diagnostic.code(), 2538);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'bigint' cannot be used as an index type."
        );
    }

    #[test]
    fn existing_error_receivers_skip_index_diagnostics_and_preserve_error_type() {
        let parsed = parse_fixture("const result = missing[true];");
        let file = FileId::new(619);
        let mut store = registered_store(&parsed, file);
        let (error, boolean) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.error_type, bootstrap.true_type)
        };
        let receiver_symbol =
            alloc_symbol(&mut store, SymbolFlags::BLOCK_SCOPED_VARIABLE, "missing");
        let plan = source_plan(
            &parsed,
            file,
            &store,
            PlannedExpressionKind::Boolean(true),
            receiver_symbol,
        );

        assert_eq!(
            check_direct_source_element_with_array_targets(
                &mut store,
                &empty_host(),
                CanonicalArrayTargets::for_single_target_validation(error),
                strict_options(),
                &plan,
                error,
                boolean,
            ),
            Ok(CheckedSourceElement {
                type_: error,
                diagnostic: None,
            }),
        );
        assert_eq!(
            store
                .type_node_links(plan.node)
                .and_then(|links| links.resolved_type),
            Some(error),
        );
        assert!(store.symbol_node_links(plan.node).is_none());
    }

    #[test]
    fn member_calls_and_poisoned_links_fail_closed() {
        let call = parse_fixture("const result = object[\"known\"]();");
        let call_file = FileId::new(610);
        let call_access = element_access(&call, call_file);
        let call_store = registered_store(&call, call_file);
        assert!(matches!(
            plan_direct_source_element_syntax(&call.arena, &call_store, call_access),
            Err(SourceElementError::Unsupported(
                SourceElementUnsupported::MemberCall(_)
            ))
        ));

        let poisoned = parse_fixture("const result = object[\"known\"];");
        let poisoned_file = FileId::new(611);
        let poisoned_access = element_access(&poisoned, poisoned_file);
        let mut poisoned_store = registered_store(&poisoned, poisoned_file);
        assert!(poisoned_store.set_type_node_links(
            poisoned_access,
            TypeNodeLinks {
                outer_type_parameters: Some(Vec::new()),
                ..TypeNodeLinks::default()
            },
        ));
        assert_eq!(
            plan_direct_source_element_syntax(&poisoned.arena, &poisoned_store, poisoned_access,),
            Err(SourceElementError::InvalidCache(poisoned_access))
        );
    }

    #[test]
    fn indexed_assignment_syntax_requires_its_exact_ordinary_assignment_owner() {
        let parsed = parse_fixture("array[0] = 1;");
        let file = FileId::new(616);
        let access = element_access(&parsed, file);
        let assignment = NodeRef::new(
            parsed.arena.id(),
            file,
            parsed.arena.get(access.node).unwrap().parent.unwrap(),
        );
        let store = registered_store(&parsed, file);

        assert!(matches!(
            plan_direct_source_element_syntax(&parsed.arena, &store, access),
            Err(SourceElementError::Unsupported(
                SourceElementUnsupported::Write(node)
            )) if node == access
        ));
        let syntax =
            plan_direct_source_element_write_syntax(&parsed.arena, &store, access, assignment)
                .unwrap();
        assert_eq!(syntax.node, access);
        assert_eq!(
            parsed.arena.get(syntax.index.node).unwrap().kind,
            SyntaxKind::NumericLiteral
        );

        assert!(matches!(
            plan_direct_source_element_write_syntax(&parsed.arena, &store, access, access),
            Err(SourceElementError::Unsupported(
                SourceElementUnsupported::Write(node)
            )) if node == access
        ));
    }
}
