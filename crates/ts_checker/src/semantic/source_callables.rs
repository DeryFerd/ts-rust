//! Exact annotated callable values owned by source function symbols.
//!
//! This provider deliberately stops before statement/expression dispatch and
//! function-body semantics. It proves one retained `FunctionDeclaration` or
//! `ArrowFunction` and its binder-owned FUNCTION symbol, publishes the callable
//! shell/signature/parameter types, and validates the resulting store shape.
//! Source values never borrow `FunctionType` `TypeNode` or `__call` provenance.

use std::collections::HashSet;

use ts_ast::{ModifierList, NodeData, NodeList, NodeRef, SyntaxKind};
use ts_binder::{CheckFlags, InternalSymbolName, SemanticSymbolId, SymbolFlags};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore, DeclaredTypeError, DeclaredTypeHost,
    SignatureId, TypeId,
    array_types::CanonicalArrayTargets,
    bootstrap::{LiteralTypeCacheError, PreparedTypeQueryTypes},
    callables::{ValidatedSingleCallParameterDisplay, ValidatedSingleCallSignatureDisplay},
    declared::{
        cached_ordinary_type_parameter_owner, execute_type_parameter,
        explicit_type_parameter_symbols, preflight_node,
    },
    functions::{StoredFunctionTypeValidation, validate_stored_function_type},
    links::{
        DecoratorSignatureState, EffectsSignatureState, ResolvedSignatureState, SignatureLinks,
        SymbolNodeLinks, TypeNodeLinks, ValueSymbolLinks,
    },
    signatures::{Signature, SignatureFlags},
    store::{SourceCallableProvenance, SourceNodeParent},
    type_records::{ConstrainedTypeData, StructuredTypeData, TypeCacheState, TypeData, TypeRecord},
    types::{ObjectFlags, TypeFlags},
};

pub(super) use super::store::SourceCallableFamily;

const NODE_FLAG_JSDOC: u32 = 1 << 22;

/// One exact identifier parameter and its annotation identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceCallableParameterPlan {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) type_node: NodeRef,
    identity_node: NodeRef,
    null_literal_identity: bool,
    pub(super) optional: bool,
}

/// One exact declared type-parameter identity owned by a source signature.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SourceCallableTypeParameterPlan {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
}

/// Binder/syntax proof retained across source-callable publication.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SourceCallablePlan {
    pub(super) family: SourceCallableFamily,
    pub(super) declaration: NodeRef,
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) owner_parent: Option<SemanticSymbolId>,
    pub(super) export_local: Option<SemanticSymbolId>,
    pub(super) type_parameters: Vec<SourceCallableTypeParameterPlan>,
    pub(super) parameters: Vec<SourceCallableParameterPlan>,
    pub(super) return_type: NodeRef,
    return_identity_node: NodeRef,
    return_null_literal_identity: bool,
    pub(super) body: NodeRef,
    pub(super) flags: SignatureFlags,
    pub(super) min_argument_count: i32,
    pub(super) array_targets: Option<CanonicalArrayTargets>,
}

/// Source syntax families intentionally deferred beyond the exact first cut.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallableUnsupported {
    GenericSignature(NodeRef),
    Async(NodeRef),
    Generator(NodeRef),
    Modifiers(NodeRef),
    OverloadDeclaration(NodeRef),
    ThisParameter(NodeRef),
    RestParameter(NodeRef),
    InitializedParameter(NodeRef),
    DestructuredParameter(NodeRef),
    ParameterModifiers(NodeRef),
    MissingParameterType(NodeRef),
    MissingReturnType(NodeRef),
    TypePredicate(NodeRef),
    RequiredAfterOptional(NodeRef),
}

/// Malformed AST, binder provenance, or semantic cache state.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallableInvariant {
    InvalidSyntax(NodeRef),
    InvalidOwnerSymbol(NodeRef),
    InvalidExportRoute(NodeRef),
    InvalidParameter(NodeRef),
    InvalidParameterSymbol(NodeRef),
    InvalidTypeCache(NodeRef),
    InvalidSignatureCache(NodeRef),
    InvalidParameterCache(NodeRef),
    Capacity(NodeRef),
    Publication(NodeRef),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallableError {
    Unsupported(SourceCallableUnsupported),
    Invariant(SourceCallableInvariant),
    DeclaredType(DeclaredTypeError),
    LiteralCache(LiteralTypeCacheError),
}

impl SourceCallableError {
    pub(super) const fn node(self) -> Option<NodeRef> {
        match self {
            Self::Unsupported(reason) => Some(match reason {
                SourceCallableUnsupported::GenericSignature(node)
                | SourceCallableUnsupported::Async(node)
                | SourceCallableUnsupported::Generator(node)
                | SourceCallableUnsupported::Modifiers(node)
                | SourceCallableUnsupported::OverloadDeclaration(node)
                | SourceCallableUnsupported::ThisParameter(node)
                | SourceCallableUnsupported::RestParameter(node)
                | SourceCallableUnsupported::InitializedParameter(node)
                | SourceCallableUnsupported::DestructuredParameter(node)
                | SourceCallableUnsupported::ParameterModifiers(node)
                | SourceCallableUnsupported::MissingParameterType(node)
                | SourceCallableUnsupported::MissingReturnType(node)
                | SourceCallableUnsupported::TypePredicate(node)
                | SourceCallableUnsupported::RequiredAfterOptional(node) => node,
            }),
            Self::Invariant(reason) => Some(match reason {
                SourceCallableInvariant::InvalidSyntax(node)
                | SourceCallableInvariant::InvalidOwnerSymbol(node)
                | SourceCallableInvariant::InvalidExportRoute(node)
                | SourceCallableInvariant::InvalidParameter(node)
                | SourceCallableInvariant::InvalidParameterSymbol(node)
                | SourceCallableInvariant::InvalidTypeCache(node)
                | SourceCallableInvariant::InvalidSignatureCache(node)
                | SourceCallableInvariant::InvalidParameterCache(node)
                | SourceCallableInvariant::Capacity(node)
                | SourceCallableInvariant::Publication(node) => node,
            }),
            Self::DeclaredType(_) | Self::LiteralCache(_) => None,
        }
    }
}

impl From<DeclaredTypeError> for SourceCallableError {
    fn from(error: DeclaredTypeError) -> Self {
        Self::DeclaredType(error)
    }
}

impl From<LiteralTypeCacheError> for SourceCallableError {
    fn from(error: LiteralTypeCacheError) -> Self {
        Self::LiteralCache(error)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallableState {
    Cold,
    ActiveBarrier {
        type_: TypeId,
        signature: SignatureId,
    },
    ActiveParameters {
        type_: TypeId,
        signature: SignatureId,
    },
    Resolved {
        type_: TypeId,
        signature: SignatureId,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct PendingSourceCallable {
    pub(super) type_: TypeId,
    pub(super) signature: SignatureId,
}

#[derive(Clone, Debug)]
pub(super) struct PendingSourceCallableParameterTypes {
    pub(super) plan: SourceCallablePlan,
    pub(super) base_types: Vec<TypeId>,
}

/// One already-resolved parameter of a contextually typed source arrow.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ContextualSourceCallableParameter {
    pub(super) declaration: NodeRef,
    pub(super) symbol: SemanticSymbolId,
    pub(super) type_: TypeId,
}

/// Fully prepared semantic values for the bounded inferred contextual arrow.
///
/// Syntax and contextual-origin planning happen before this boundary. Every
/// `TypeId` here is final, so publication never fabricates an annotation node
/// or conflates the variable's contextual target with the arrow expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PreparedContextualSourceCallable {
    pub(super) declaration: NodeRef,
    pub(super) owner_symbol: SemanticSymbolId,
    pub(super) variable_symbol: SemanticSymbolId,
    pub(super) contextual_target: TypeId,
    pub(super) parameters: Vec<ContextualSourceCallableParameter>,
    pub(super) flags: SignatureFlags,
    pub(super) min_argument_count: i32,
    pub(super) return_type: TypeId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum StoredSourceCallableValidation {
    NotSourceCallable,
    Pending,
    Valid(Vec<TypeId>),
    Malformed,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallableDisplayError {
    Unsupported(SourceCallableUnsupported),
    Pending,
    Malformed,
}

struct SourceSyntaxView<'a> {
    family: SourceCallableFamily,
    parameters: &'a NodeList,
    modifiers: Option<&'a ModifierList>,
    type_parameters: Option<&'a NodeList>,
    return_type: Option<ts_ast::NodeId>,
    body: Option<ts_ast::NodeId>,
    asterisk_token: Option<ts_ast::NodeId>,
    name: Option<ts_ast::NodeId>,
    equals_greater_than_token: Option<ts_ast::NodeId>,
    invalid_parser_cache: bool,
}

/// Plans one exact source callable without publishing semantic records.
pub(super) fn plan_source_callable(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner_symbol: SemanticSymbolId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<SourceCallablePlan, SourceCallableError> {
    let record = preflight_node(store, host, declaration)?;
    let view = match &record.data {
        NodeData::FunctionDeclaration(function)
            if record.kind == SyntaxKind::FunctionDeclaration =>
        {
            SourceSyntaxView {
                family: SourceCallableFamily::FunctionDeclaration,
                parameters: &function.parameters,
                modifiers: function.modifiers.as_ref(),
                type_parameters: function.type_parameters.as_ref(),
                return_type: function.type_,
                body: function.body,
                asterisk_token: function.asterisk_token,
                name: function.name,
                equals_greater_than_token: None,
                invalid_parser_cache: function.full_signature.is_some()
                    || function.next_container.is_some()
                    || function.symbol.is_some()
                    || function.local_symbol.is_some()
                    || function.flow_node.is_some()
                    || function.end_flow_node.is_some()
                    || function.return_flow_node.is_some(),
            }
        }
        NodeData::ArrowFunction(function) if record.kind == SyntaxKind::ArrowFunction => {
            SourceSyntaxView {
                family: SourceCallableFamily::ArrowFunction,
                parameters: &function.parameters,
                modifiers: function.modifiers.as_ref(),
                type_parameters: function.type_parameters.as_ref(),
                return_type: function.type_,
                body: Some(function.body),
                asterisk_token: function.asterisk_token,
                name: None,
                equals_greater_than_token: Some(function.equals_greater_than_token),
                invalid_parser_cache: function.full_signature.is_some()
                    || function.next_container.is_some()
                    || function.symbol.is_some()
                    || function.flow_node.is_some()
                    || function.end_flow_node.is_some(),
            }
        }
        _ => {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(
                declaration,
            )));
        }
    };
    if record.flags.0 & NODE_FLAG_JSDOC != 0
        || view.invalid_parser_cache
        || view.parameters.range.start < record.range.start
        || view.parameters.range.end > record.range.end
        || view.parameters.has_trailing_comma
    {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(
            declaration,
        )));
    }
    let type_parameters = plan_exact_source_type_parameters(
        store,
        host,
        declaration,
        view.family,
        view.type_parameters,
        view.parameters,
    )?;
    if let Some(asterisk) = view.asterisk_token {
        let asterisk = NodeRef::new(declaration.arena, declaration.file, asterisk);
        preflight_child(store, host, declaration, asterisk)?;
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::Generator(asterisk),
        ));
    }
    validate_modifiers(store, host, declaration, record.range, &view)?;

    let bound = host
        .bound_file(declaration)
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidOwnerSymbol(declaration)))?;
    if bound.symbol(declaration) != Some(owner_symbol)
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
    {
        return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
            declaration,
        )));
    }
    let owner = store
        .symbol(owner_symbol)
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidOwnerSymbol(declaration)))?;
    if owner.flags() != SymbolFlags::FUNCTION
        || owner.check_flags() != CheckFlags::NONE
        || owner.declarations() != Some(&[declaration])
        || owner.value_declaration() != Some(declaration)
        || owner.members().is_some()
        || owner.exports().is_some()
        || owner.export_symbol().is_some()
    {
        return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
            declaration,
        )));
    }
    let export_local = bound.local_symbol(declaration);
    validate_owner_name_and_export_route(
        store,
        host,
        declaration,
        owner_symbol,
        owner,
        export_local,
        &view,
    )?;

    let mut parameters = Vec::with_capacity(view.parameters.nodes.len());
    let mut previous_end = view.parameters.range.start;
    let mut optional_seen = false;
    let mut min_argument_count = 0usize;
    let mut flags = SignatureFlags::NONE;
    for parameter_id in &view.parameters.nodes {
        let parameter = NodeRef::new(declaration.arena, declaration.file, *parameter_id);
        if parameters
            .iter()
            .any(|planned: &SourceCallableParameterPlan| planned.declaration == parameter)
        {
            return Err(invariant(SourceCallableInvariant::InvalidParameter(
                parameter,
            )));
        }
        let parameter_record = preflight_node(store, host, parameter)?;
        let NodeData::ParameterDeclaration(data) = &parameter_record.data else {
            return Err(invariant(SourceCallableInvariant::InvalidParameter(
                parameter,
            )));
        };
        if parameter_record.kind != SyntaxKind::Parameter
            || parameter_record.parent != Some(declaration.node)
            || parameter_record.flags.0 & NODE_FLAG_JSDOC != 0
            || parameter_record.range.start < previous_end
            || parameter_record.range.start < view.parameters.range.start
            || parameter_record.range.end > view.parameters.range.end
            || data.symbol.is_some()
            || data.facts != 0
        {
            return Err(invariant(SourceCallableInvariant::InvalidParameter(
                parameter,
            )));
        }
        previous_end = parameter_record.range.end;
        if data.dot_dot_dot_token.is_some() {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::RestParameter(parameter),
            ));
        }
        if data.initializer.is_some() {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::InitializedParameter(parameter),
            ));
        }
        if data.modifiers.is_some() {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::ParameterModifiers(parameter),
            ));
        }
        let name = NodeRef::new(declaration.arena, declaration.file, data.name);
        let name_record = preflight_node(store, host, name)?;
        let NodeData::Identifier(identifier) = &name_record.data else {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::DestructuredParameter(parameter),
            ));
        };
        if name_record.kind != SyntaxKind::Identifier
            || name_record.parent != Some(parameter.node)
            || name_record.range.start < parameter_record.range.start
            || name_record.range.end > parameter_record.range.end
        {
            return Err(invariant(SourceCallableInvariant::InvalidParameter(
                parameter,
            )));
        }
        if identifier.text == "this" {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::ThisParameter(parameter),
            ));
        }
        let Some(type_id) = data.type_ else {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::MissingParameterType(parameter),
            ));
        };
        let type_node = NodeRef::new(declaration.arena, declaration.file, type_id);
        let type_record = preflight_node(store, host, type_node)?;
        if type_record.parent != Some(parameter.node)
            || type_record.range.start < name_record.range.end
            || type_record.range.end > parameter_record.range.end
        {
            return Err(invariant(SourceCallableInvariant::InvalidParameter(
                parameter,
            )));
        }
        let optional = validate_optional_token(
            store,
            host,
            parameter,
            data.question_token,
            name_record.range.end,
            type_record.range.start,
        )?;
        if optional {
            optional_seen = true;
        } else if optional_seen {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::RequiredAfterOptional(parameter),
            ));
        } else {
            min_argument_count = parameters.len() + 1;
        }
        let raw_symbol = bound
            .symbol(parameter)
            .ok_or_else(|| invariant(SourceCallableInvariant::InvalidParameterSymbol(parameter)))?;
        let symbol = store
            .get_merged_symbol(raw_symbol)
            .ok_or_else(|| invariant(SourceCallableInvariant::InvalidParameterSymbol(parameter)))?;
        let symbol_record = store
            .symbol(symbol)
            .ok_or_else(|| invariant(SourceCallableInvariant::InvalidParameterSymbol(parameter)))?;
        if symbol != raw_symbol
            || symbol_record.flags() != SymbolFlags::FUNCTION_SCOPED_VARIABLE
            || symbol_record.check_flags() != CheckFlags::NONE
            || symbol_record.name().as_bytes() != identifier.text.as_bytes()
            || symbol_record.declarations() != Some(&[parameter])
            || symbol_record.value_declaration() != Some(parameter)
            || symbol_record.members().is_some()
            || symbol_record.exports().is_some()
            || symbol_record.parent().is_some()
            || symbol_record.export_symbol().is_some()
        {
            return Err(invariant(SourceCallableInvariant::InvalidParameterSymbol(
                parameter,
            )));
        }
        let identity_node = peel_parenthesized_type(store, host, type_node)?;
        if type_record.kind == SyntaxKind::LiteralType {
            flags |= SignatureFlags::HAS_LITERAL_TYPES;
        }
        parameters.push(SourceCallableParameterPlan {
            declaration: parameter,
            symbol,
            type_node,
            identity_node,
            null_literal_identity: is_null_literal_type(store, host, identity_node)?,
            optional,
        });
    }

    let Some(return_id) = view.return_type else {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::MissingReturnType(declaration),
        ));
    };
    let return_type = NodeRef::new(declaration.arena, declaration.file, return_id);
    let return_record = preflight_node(store, host, return_type)?;
    if return_record.parent != Some(declaration.node)
        || return_record.range.start < view.parameters.range.end
        || return_record.range.end > record.range.end
    {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(
            declaration,
        )));
    }
    let return_identity_node = peel_parenthesized_type(store, host, return_type)?;
    if preflight_node(store, host, return_identity_node)?.kind == SyntaxKind::TypePredicate {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::TypePredicate(return_type),
        ));
    }
    let Some(body_id) = view.body else {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::OverloadDeclaration(declaration),
        ));
    };
    let body = NodeRef::new(declaration.arena, declaration.file, body_id);
    let body_record = preflight_node(store, host, body)?;
    if body_record.parent != Some(declaration.node)
        || body_record.range.start < return_record.range.end
        || body_record.range.end > record.range.end
        || view.family == SourceCallableFamily::FunctionDeclaration
            && body_record.kind != SyntaxKind::Block
    {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(
            declaration,
        )));
    }
    if let Some(token_id) = view.equals_greater_than_token {
        let token = NodeRef::new(declaration.arena, declaration.file, token_id);
        let token_record = preflight_node(store, host, token)?;
        if token_record.kind != SyntaxKind::EqualsGreaterThanToken
            || token_record.parent != Some(declaration.node)
            || token_record.range.start < return_record.range.end
            || token_record.range.end > body_record.range.start
        {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(
                declaration,
            )));
        }
    }
    let min_argument_count = i32::try_from(min_argument_count)
        .map_err(|_| invariant(SourceCallableInvariant::Capacity(declaration)))?;
    let plan = SourceCallablePlan {
        family: view.family,
        declaration,
        owner_symbol,
        owner_parent: owner.parent(),
        export_local,
        type_parameters,
        parameters,
        return_type,
        return_identity_node,
        return_null_literal_identity: is_null_literal_type(store, host, return_identity_node)?,
        body,
        flags,
        min_argument_count,
        array_targets,
    };
    validate_exact_generic_annotation_shape(store, host, &plan)?;
    source_callable_state(store, &plan, true)?;
    Ok(plan)
}

fn plan_exact_source_type_parameters(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    family: SourceCallableFamily,
    type_parameters: Option<&NodeList>,
    parameters: &NodeList,
) -> Result<Vec<SourceCallableTypeParameterPlan>, SourceCallableError> {
    let Some(type_parameters) = type_parameters else {
        return Ok(Vec::new());
    };
    if family != SourceCallableFamily::FunctionDeclaration
        || type_parameters.has_trailing_comma
        || type_parameters.nodes.len() != 1
        || type_parameters.range.start < preflight_node(store, host, declaration)?.range.start
        || type_parameters.range.end > parameters.range.start
    {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::GenericSignature(declaration),
        ));
    }

    let type_parameter = NodeRef::new(
        declaration.arena,
        declaration.file,
        type_parameters.nodes[0],
    );
    let record = preflight_node(store, host, type_parameter)?;
    let NodeData::TypeParameterDeclaration(data) = &record.data else {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(
            type_parameter,
        )));
    };
    if record.kind != SyntaxKind::TypeParameter
        || record.parent != Some(declaration.node)
        || record.flags.0 & NODE_FLAG_JSDOC != 0
        || record.range.start < type_parameters.range.start
        || record.range.end > type_parameters.range.end
        || data.constraint.is_some()
        || data.default_type.is_some()
        || data.expression.is_some()
        || data.modifiers.is_some()
    {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::GenericSignature(type_parameter),
        ));
    }
    if data.symbol.is_some() {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(
            type_parameter,
        )));
    }
    let name = NodeRef::new(type_parameter.arena, type_parameter.file, data.name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(identifier) = &name_record.data else {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(name)));
    };
    if name_record.kind != SyntaxKind::Identifier
        || name_record.parent != Some(type_parameter.node)
        || name_record.flags.0 != 0
        || name_record.range.start < record.range.start
        || name_record.range.end > record.range.end
        || identifier.text.is_empty()
        || identifier.flow_node.is_some()
    {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(name)));
    }

    let symbols = explicit_type_parameter_symbols(
        store,
        host,
        declaration,
        Some(type_parameters),
        &mut HashSet::new(),
    )?;
    let [symbol] = symbols.as_slice() else {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::GenericSignature(type_parameter),
        ));
    };
    let symbol_record = store
        .symbol(*symbol)
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidOwnerSymbol(type_parameter)))?;
    if symbol_record.flags() != SymbolFlags::TYPE_PARAMETER
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.declarations() != Some(&[type_parameter])
        || symbol_record.value_declaration().is_some()
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent().is_some()
        || symbol_record.export_symbol().is_some()
    {
        return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
            type_parameter,
        )));
    }
    Ok(vec![SourceCallableTypeParameterPlan {
        declaration: type_parameter,
        symbol: *symbol,
    }])
}

fn validate_exact_generic_annotation_shape(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceCallablePlan,
) -> Result<(), SourceCallableError> {
    let [] = plan.type_parameters.as_slice() else {
        let [type_parameter] = plan.type_parameters.as_slice() else {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::GenericSignature(plan.declaration),
            ));
        };
        let [parameter] = plan.parameters.as_slice() else {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::GenericSignature(plan.declaration),
            ));
        };
        if parameter.optional
            || !is_naked_source_type_parameter_annotation(
                store,
                host,
                parameter.identity_node,
                type_parameter,
            )?
            || !is_naked_source_type_parameter_annotation(
                store,
                host,
                plan.return_identity_node,
                type_parameter,
            )?
        {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::GenericSignature(plan.declaration),
            ));
        }
        return Ok(());
    };
    Ok(())
}

fn is_naked_source_type_parameter_annotation(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    annotation: NodeRef,
    type_parameter: &SourceCallableTypeParameterPlan,
) -> Result<bool, SourceCallableError> {
    let annotation_record = preflight_node(store, host, annotation)?;
    let NodeData::TypeReferenceNode(reference) = &annotation_record.data else {
        return Ok(false);
    };
    if annotation_record.kind != SyntaxKind::TypeReference || reference.type_arguments.is_some() {
        return Ok(false);
    }
    let name = NodeRef::new(annotation.arena, annotation.file, reference.type_name);
    let name_record = preflight_node(store, host, name)?;
    let NodeData::Identifier(name_identifier) = &name_record.data else {
        return Ok(false);
    };
    let type_parameter_record = preflight_node(store, host, type_parameter.declaration)?;
    let NodeData::TypeParameterDeclaration(type_parameter_data) = &type_parameter_record.data
    else {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(
            type_parameter.declaration,
        )));
    };
    let declaration_name = NodeRef::new(
        type_parameter.declaration.arena,
        type_parameter.declaration.file,
        type_parameter_data.name,
    );
    let declaration_name_record = preflight_node(store, host, declaration_name)?;
    let NodeData::Identifier(declaration_identifier) = &declaration_name_record.data else {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(
            declaration_name,
        )));
    };
    let exact_syntax = name_record.kind == SyntaxKind::Identifier
        && name_record.parent == Some(annotation.node)
        && name_record.flags.0 == 0
        && name_identifier.flow_node.is_none()
        && name_identifier.text == declaration_identifier.text;
    if exact_syntax {
        validate_source_type_parameter_annotation_links(store, annotation, type_parameter)?;
    }
    Ok(exact_syntax)
}

/// A naked source `T` annotation is either untouched or has the complete
/// symbol/type pair produced by a canonical type-reference query. Accepting a
/// lone warm side would let the generic callable fast path trust a type cache
/// that was never proven to belong to its declared type parameter.
fn validate_source_type_parameter_annotation_links(
    store: &CanonicalTypeMapperStore,
    annotation: NodeRef,
    type_parameter: &SourceCallableTypeParameterPlan,
) -> Result<(), SourceCallableError> {
    let symbol_links = store.symbol_node_links(annotation);
    let type_links = store.type_node_links(annotation);
    let symbol_cold = symbol_links.is_none_or(|links| links == &SymbolNodeLinks::default());
    let type_cold = type_links.is_none_or(|links| links == &TypeNodeLinks::default());
    if symbol_cold && type_cold {
        return Ok(());
    }

    let declared_type = store
        .declared_type_links(type_parameter.symbol)
        .and_then(|links| links.declared_type)
        .filter(|declared_type| {
            cached_ordinary_type_parameter_owner(store, *declared_type)
                == Some(type_parameter.symbol)
        });
    let fully_warm = declared_type.is_some_and(|declared_type| {
        source_type_parameter_annotation_links_are_fully_warm(
            store,
            annotation,
            type_parameter.symbol,
            declared_type,
        )
    });
    if !fully_warm {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            annotation,
        )));
    }
    Ok(())
}

fn source_type_parameter_annotation_links_are_fully_warm(
    store: &CanonicalTypeMapperStore,
    annotation: NodeRef,
    symbol: SemanticSymbolId,
    declared_type: TypeId,
) -> bool {
    store.symbol_node_links(annotation)
        == Some(&SymbolNodeLinks {
            resolved_symbol: Some(symbol),
        })
        && store.type_node_links(annotation)
            == Some(&TypeNodeLinks {
                resolved_type: Some(declared_type),
                outer_type_parameters: None,
            })
}

fn validate_modifiers(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    declaration_range: ts_core::TextRange,
    view: &SourceSyntaxView<'_>,
) -> Result<(), SourceCallableError> {
    let Some(modifiers) = view.modifiers else {
        return Ok(());
    };
    for modifier_id in &modifiers.list.nodes {
        let modifier = NodeRef::new(declaration.arena, declaration.file, *modifier_id);
        let record = preflight_node(store, host, modifier)?;
        if record.kind == SyntaxKind::AsyncKeyword {
            return Err(SourceCallableError::Unsupported(
                SourceCallableUnsupported::Async(modifier),
            ));
        }
    }
    let [modifier_id] = modifiers.list.nodes.as_slice() else {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::Modifiers(declaration),
        ));
    };
    let modifier = NodeRef::new(declaration.arena, declaration.file, *modifier_id);
    let modifier_record = preflight_node(store, host, modifier)?;
    if view.family != SourceCallableFamily::FunctionDeclaration
        || modifiers.flags.0 != 0
        || modifiers.list.has_trailing_comma
        || modifiers.list.range.start != declaration_range.start
        || modifier_record.kind != SyntaxKind::ExportKeyword
        || !matches!(modifier_record.data, NodeData::Token(_))
        || modifier_record.flags.0 != 0
        || modifier_record.parent != Some(declaration.node)
        || modifier_record.range.start != declaration_range.start
        || modifier_record.range.end > modifiers.list.range.end
    {
        return Err(SourceCallableError::Unsupported(
            SourceCallableUnsupported::Modifiers(modifier),
        ));
    }
    Ok(())
}

fn validate_owner_name_and_export_route(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    declaration: NodeRef,
    owner_symbol: SemanticSymbolId,
    owner: &ts_binder::semantic::Symbol,
    local_symbol: Option<SemanticSymbolId>,
    view: &SourceSyntaxView<'_>,
) -> Result<(), SourceCallableError> {
    match view.family {
        SourceCallableFamily::ArrowFunction => {
            if view.name.is_some()
                || owner.name() != InternalSymbolName::Function.as_ref()
                || owner.parent().is_some()
                || local_symbol.is_some()
            {
                return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
                    declaration,
                )));
            }
        }
        SourceCallableFamily::FunctionDeclaration => {
            let bound = host.bound_file(declaration).ok_or_else(|| {
                invariant(SourceCallableInvariant::InvalidExportRoute(declaration))
            })?;
            let Some(name_id) = view.name else {
                return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
                    declaration,
                )));
            };
            let name = NodeRef::new(declaration.arena, declaration.file, name_id);
            let name_record = preflight_node(store, host, name)?;
            let NodeData::Identifier(identifier) = &name_record.data else {
                return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
                    declaration,
                )));
            };
            if name_record.kind != SyntaxKind::Identifier
                || name_record.parent != Some(declaration.node)
                || owner.name().as_bytes() != identifier.text.as_bytes()
            {
                return Err(invariant(SourceCallableInvariant::InvalidOwnerSymbol(
                    declaration,
                )));
            }
            match local_symbol {
                None if view.modifiers.is_none() && owner.parent().is_none() => {}
                Some(local) if view.modifiers.is_some() => {
                    let raw_source_owner = bound.symbol(bound.source_file()).ok_or_else(|| {
                        invariant(SourceCallableInvariant::InvalidExportRoute(declaration))
                    })?;
                    let source_owner =
                        store.get_merged_symbol(raw_source_owner).ok_or_else(|| {
                            invariant(SourceCallableInvariant::InvalidExportRoute(declaration))
                        })?;
                    let local_record = store.symbol(local).ok_or_else(|| {
                        invariant(SourceCallableInvariant::InvalidExportRoute(declaration))
                    })?;
                    if source_owner != raw_source_owner
                        || owner.parent() != Some(source_owner)
                        || store.get_merged_symbol(source_owner) != Some(source_owner)
                        || store.get_merged_symbol(local) != Some(local)
                        || local_record.flags() != SymbolFlags::EXPORT_VALUE
                        || local_record.check_flags() != CheckFlags::NONE
                        || local_record.name().as_bytes() != identifier.text.as_bytes()
                        || local_record.declarations() != Some(&[declaration])
                        || local_record.value_declaration().is_some()
                        || local_record.members().is_some()
                        || local_record.exports().is_some()
                        || local_record.parent().is_some()
                        || local_record.export_symbol() != Some(owner_symbol)
                    {
                        return Err(invariant(SourceCallableInvariant::InvalidExportRoute(
                            declaration,
                        )));
                    }
                }
                _ => {
                    return Err(invariant(SourceCallableInvariant::InvalidExportRoute(
                        declaration,
                    )));
                }
            }
        }
    }
    Ok(())
}

fn validate_optional_token(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    parameter: NodeRef,
    question_token: Option<ts_ast::NodeId>,
    name_end: ts_core::TextPos,
    type_start: ts_core::TextPos,
) -> Result<bool, SourceCallableError> {
    let Some(question_id) = question_token else {
        return Ok(false);
    };
    let question = NodeRef::new(parameter.arena, parameter.file, question_id);
    let record = preflight_node(store, host, question)?;
    if record.kind != SyntaxKind::QuestionToken
        || record.parent != Some(parameter.node)
        || record.range.start < name_end
        || record.range.end > type_start
    {
        return Err(invariant(SourceCallableInvariant::InvalidParameter(
            parameter,
        )));
    }
    Ok(true)
}

fn preflight_child(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    parent: NodeRef,
    child: NodeRef,
) -> Result<(), SourceCallableError> {
    if preflight_node(store, host, child)?.parent != Some(parent.node) {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(parent)));
    }
    Ok(())
}

/// Validates the cold, barrier, parameter, or resolved state for one plan.
pub(super) fn source_callable_state(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    allow_active_barrier: bool,
) -> Result<SourceCallableState, SourceCallableError> {
    let owner_links = store.value_symbol_links(plan.owner_symbol);
    let Some(type_) = owner_links.and_then(|links| links.resolved_type) else {
        if owner_links.is_some_and(|links| links != &ValueSymbolLinks::default())
            || !default_signature_links(store, plan.declaration)
            || plan
                .parameters
                .iter()
                .any(|parameter| !default_parameter_links(store, parameter.symbol))
            || store
                .source_callable_type_for_owner(plan.owner_symbol)
                .is_some()
            || store
                .source_callable_type_for_declaration(plan.declaration)
                .is_some()
        {
            return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
                plan.declaration,
            )));
        }
        return Ok(SourceCallableState::Cold);
    };
    if owner_links
        != Some(&ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        })
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            plan.declaration,
        )));
    }
    let record = store
        .type_payload(type_)
        .ok_or_else(|| invariant(SourceCallableInvariant::InvalidTypeCache(plan.declaration)))?;
    let TypeData::Object(object) = record.data() else {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            plan.declaration,
        )));
    };
    let signature = exact_signature_link(store, plan.declaration)?;
    let expected_provenance = SourceCallableProvenance {
        family: plan.family,
        declaration: plan.declaration,
        owner_symbol: plan.owner_symbol,
        owner_parent: plan.owner_parent,
        export_local: plan.export_local,
        signature,
        contextual_target: None,
        contextual_variable: None,
    };
    if record.flags() != TypeFlags::OBJECT
        || record.symbol() != Some(plan.owner_symbol)
        || record.alias().is_some()
        || store.source_callable_provenance(type_) != Some(expected_provenance)
        || store.source_callable_type_for_owner(plan.owner_symbol) != Some(type_)
        || store.source_callable_type_for_signature(signature) != Some(type_)
        || store.source_callable_type_for_declaration(plan.declaration) != Some(type_)
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            plan.declaration,
        )));
    }
    validate_signature(store, plan, signature)?;
    let resolved_return_type = store
        .signature(signature)
        .expect("the source signature was validated")
        .resolved_return_type();
    let published_parameter_types = store.callable_signature_parameter_types(signature);
    let is_barrier = record.object_flags()
        == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        && object.structured == StructuredTypeData::default();
    if is_barrier {
        if !allow_active_barrier
            || resolved_return_type.is_some()
            || published_parameter_types.is_some()
            || plan
                .parameters
                .iter()
                .any(|parameter| !default_parameter_links(store, parameter.symbol))
        {
            return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
                plan.declaration,
            )));
        }
        return Ok(SourceCallableState::ActiveBarrier { type_, signature });
    }
    let structured = &object.structured;
    if record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || structured.constrained != ConstrainedTypeData::default()
        || structured.members.is_some()
        || structured.properties.is_some()
        || structured.signatures.as_deref() != Some(&[signature])
        || structured.call_signature_count != 1
        || structured.index_infos.is_some()
        || structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            plan.declaration,
        )));
    }
    if !plan.parameters.is_empty()
        && plan
            .parameters
            .iter()
            .all(|parameter| default_parameter_links(store, parameter.symbol))
    {
        if !allow_active_barrier
            || resolved_return_type.is_some()
            || published_parameter_types.is_some()
        {
            return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
                plan.declaration,
            )));
        }
        return Ok(SourceCallableState::ActiveParameters { type_, signature });
    }
    let Some(published_parameter_types) = published_parameter_types else {
        return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
            plan.declaration,
        )));
    };
    if published_parameter_types.len() != plan.parameters.len() {
        return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
            plan.declaration,
        )));
    }
    for (parameter, expected) in plan.parameters.iter().zip(published_parameter_types) {
        validate_parameter_links(store, plan, parameter, *expected)?;
    }
    validate_cached_return_type(store, plan, signature)?;
    Ok(SourceCallableState::Resolved { type_, signature })
}

/// Reserves every source-callable record before hoisted construction starts.
pub(super) fn reserve_source_callable_capacities(
    store: &mut CanonicalTypeMapperStore,
    plans: &[&SourceCallablePlan],
) -> Result<(usize, usize), SourceCallableError> {
    let Some(first) = plans.first() else {
        return Ok((0, 0));
    };
    let strict = store
        .intrinsic_bootstrap()
        .ok_or_else(|| invariant(SourceCallableInvariant::Capacity(first.declaration)))?
        .options
        .strict_null_checks;
    let mut cold = 0usize;
    let mut cold_type_parameters = HashSet::new();
    let mut optional_parameter_unions = 0usize;
    for plan in plans {
        let state = source_callable_state(store, plan, true)?;
        if state == SourceCallableState::Cold {
            cold = cold
                .checked_add(1)
                .ok_or_else(|| invariant(SourceCallableInvariant::Capacity(plan.declaration)))?;
            for type_parameter in &plan.type_parameters {
                if store
                    .declared_type_links(type_parameter.symbol)
                    .and_then(|links| links.declared_type)
                    .is_none()
                {
                    cold_type_parameters.insert(type_parameter.symbol);
                }
            }
        }
        if strict
            && matches!(
                state,
                SourceCallableState::Cold
                    | SourceCallableState::ActiveBarrier { .. }
                    | SourceCallableState::ActiveParameters { .. }
            )
        {
            optional_parameter_unions = optional_parameter_unions
                .checked_add(
                    plan.parameters
                        .iter()
                        .filter(|parameter| parameter.optional)
                        .count(),
                )
                .ok_or_else(|| invariant(SourceCallableInvariant::Capacity(plan.declaration)))?;
        }
    }
    if !store.try_reserve_signatures(cold)
        || !store.try_reserve_source_callable_provenance(cold)
        || !store.try_reserve_function_signature_return_annotations(cold)
        || !store.try_reserve_callable_signature_parameter_types(plans.len())
    {
        return Err(invariant(SourceCallableInvariant::Capacity(
            first.declaration,
        )));
    }
    let source_type_allocations = cold
        .checked_add(cold_type_parameters.len())
        .ok_or_else(|| invariant(SourceCallableInvariant::Capacity(first.declaration)))?;
    Ok((source_type_allocations, optional_parameter_unions))
}

/// Publishes or validates one fully prepared contextually typed arrow.
///
/// Unlike annotated source callables, this path has no synthetic type-node
/// annotations to resolve lazily. The contextual target, final parameter
/// value types, and inferred `void` return are all known before the first
/// write, and the arrow expression receives an identity distinct from the
/// variable's retained target type.
pub(super) fn publish_contextual_source_callable(
    store: &mut CanonicalTypeMapperStore,
    prepared: &PreparedContextualSourceCallable,
) -> Result<TypeId, SourceCallableError> {
    if let Some(existing) = store.source_callable_type_for_owner(prepared.owner_symbol) {
        let provenance = store.source_callable_provenance(existing);
        let signature = provenance.and_then(|provenance| store.signature(provenance.signature));
        let parameter_types = provenance
            .and_then(|provenance| store.callable_signature_parameter_types(provenance.signature));
        let expected_symbols = prepared
            .parameters
            .iter()
            .map(|parameter| parameter.symbol)
            .collect::<Vec<_>>();
        let expected_types = prepared
            .parameters
            .iter()
            .map(|parameter| parameter.type_)
            .collect::<Vec<_>>();
        if matches!(
            validate_stored_source_callable(store, existing),
            StoredSourceCallableValidation::Valid(_)
        ) && provenance.is_some_and(|provenance| {
            provenance.family == SourceCallableFamily::ArrowFunction
                && provenance.declaration == prepared.declaration
                && provenance.owner_symbol == prepared.owner_symbol
                && provenance.owner_parent.is_none()
                && provenance.export_local.is_none()
                && provenance.contextual_target == Some(prepared.contextual_target)
                && provenance.contextual_variable == Some(prepared.variable_symbol)
        }) && signature.is_some_and(|signature| {
            signature.flags() == prepared.flags
                && signature.parameters() == expected_symbols
                && signature.min_argument_count() == prepared.min_argument_count
                && signature.resolved_return_type() == Some(prepared.return_type)
        }) && parameter_types == Some(expected_types.as_slice())
        {
            return Ok(existing);
        }
        return Err(invariant(SourceCallableInvariant::InvalidTypeCache(
            prepared.declaration,
        )));
    }

    let parameter_count = prepared.parameters.len();
    let minimum = usize::try_from(prepared.min_argument_count).ok();
    let allowed_flags = SignatureFlags::HAS_REST_PARAMETER;
    let owner = store.symbol(prepared.owner_symbol);
    let owner_valid = owner.is_some_and(|owner| {
        owner.flags() == SymbolFlags::FUNCTION
            && owner.check_flags() == CheckFlags::NONE
            && owner.name() == InternalSymbolName::Function.as_ref()
            && owner.declarations() == Some(&[prepared.declaration])
            && owner.value_declaration() == Some(prepared.declaration)
            && owner.members().is_none()
            && owner.exports().is_none()
            && owner.parent().is_none()
            && owner.export_symbol().is_none()
            && store.get_merged_symbol(prepared.owner_symbol) == Some(prepared.owner_symbol)
            && default_parameter_links(store, prepared.owner_symbol)
    });
    let parameters_valid = prepared
        .parameters
        .iter()
        .enumerate()
        .all(|(index, parameter)| {
            !prepared.parameters[..index]
                .iter()
                .any(|previous| previous.symbol == parameter.symbol)
                && parameter.symbol != prepared.owner_symbol
                && store.type_payload(parameter.type_).is_some()
                && store.symbol(parameter.symbol).is_some_and(|symbol| {
                    symbol.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE
                        && symbol.check_flags() == CheckFlags::NONE
                        && symbol.declarations() == Some(&[parameter.declaration])
                        && symbol.value_declaration() == Some(parameter.declaration)
                        && symbol.members().is_none()
                        && symbol.exports().is_none()
                        && symbol.parent().is_none()
                        && symbol.export_symbol().is_none()
                        && store.get_merged_symbol(parameter.symbol) == Some(parameter.symbol)
                })
                && default_parameter_links(store, parameter.symbol)
        });
    let signature_links_cold = store
        .signature_links(prepared.declaration)
        .is_none_or(|links| links == &SignatureLinks::default());
    if !owner_valid
        || !parameters_valid
        || prepared.flags.bits() & !allowed_flags.bits() != 0
        || minimum.is_none_or(|minimum| minimum > parameter_count)
        || store.type_payload(prepared.contextual_target).is_none()
        || store.type_payload(prepared.return_type).is_none()
        || store
            .source_callable_type_for_declaration(prepared.declaration)
            .is_some()
        || !signature_links_cold
    {
        return Err(invariant(SourceCallableInvariant::Publication(
            prepared.declaration,
        )));
    }
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return Err(invariant(SourceCallableInvariant::Publication(
            prepared.declaration,
        )));
    };
    if prepared.return_type != bootstrap.void_type
        || !store.try_reserve_types(1)
        || !store.try_reserve_signatures(1)
        || !store.try_reserve_source_callable_provenance(1)
        || !store.try_reserve_callable_signature_parameter_types(1)
    {
        return Err(invariant(SourceCallableInvariant::Capacity(
            prepared.declaration,
        )));
    }

    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(prepared.owner_symbol))
        .ok_or_else(|| invariant(SourceCallableInvariant::Publication(prepared.declaration)))?;
    let parameter_symbols = prepared
        .parameters
        .iter()
        .map(|parameter| parameter.symbol)
        .collect::<Vec<_>>();
    let parameter_types = prepared
        .parameters
        .iter()
        .map(|parameter| parameter.type_)
        .collect::<Vec<_>>();
    let signature = store
        .alloc_signature(
            prepared.flags,
            Some(prepared.declaration),
            Vec::new(),
            None,
            parameter_symbols,
            Some(prepared.return_type),
            None,
            prepared.min_argument_count,
        )
        .ok_or_else(|| invariant(SourceCallableInvariant::Publication(prepared.declaration)))?;
    assert!(store.set_source_callable_provenance(
        type_,
        SourceCallableProvenance {
            family: SourceCallableFamily::ArrowFunction,
            declaration: prepared.declaration,
            owner_symbol: prepared.owner_symbol,
            owner_parent: None,
            export_local: None,
            signature,
            contextual_target: Some(prepared.contextual_target),
            contextual_variable: Some(prepared.variable_symbol),
        },
    ));
    assert!(store.set_value_symbol_links(
        prepared.owner_symbol,
        ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        },
    ));
    assert!(store.set_structured_type_members(
        type_,
        None,
        None,
        Some(vec![signature]),
        None,
        None,
    ));
    assert!(store.set_signature_links(
        prepared.declaration,
        SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(signature),
            ..SignatureLinks::default()
        },
    ));
    assert!(
        store.set_callable_signature_parameter_types_batch(vec![(signature, parameter_types,)])
    );
    for parameter in &prepared.parameters {
        assert!(store.set_value_symbol_links(
            parameter.symbol,
            ValueSymbolLinks {
                resolved_type: Some(parameter.type_),
                ..ValueSymbolLinks::default()
            },
        ));
    }
    if !matches!(
        validate_stored_source_callable(store, type_),
        StoredSourceCallableValidation::Valid(_)
    ) {
        return Err(invariant(SourceCallableInvariant::Publication(
            prepared.declaration,
        )));
    }
    Ok(type_)
}

/// Publishes the recursive owner cache and structured empty-member barrier.
pub(super) fn begin_source_callable(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
) -> Result<Result<PendingSourceCallable, TypeId>, SourceCallableError> {
    match source_callable_state(store, plan, true)? {
        SourceCallableState::Resolved { type_, .. } => return Ok(Err(type_)),
        SourceCallableState::Cold => {}
        SourceCallableState::ActiveBarrier { type_, signature }
        | SourceCallableState::ActiveParameters { type_, signature } => {
            return Ok(Ok(PendingSourceCallable { type_, signature }));
        }
    }
    let type_parameters = plan
        .type_parameters
        .iter()
        .map(|type_parameter| execute_type_parameter(store, type_parameter.symbol))
        .collect::<Vec<_>>();
    let type_ = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(plan.owner_symbol))
        .ok_or_else(|| invariant(SourceCallableInvariant::Publication(plan.declaration)))?;
    let signature = store
        .alloc_signature(
            plan.flags,
            Some(plan.declaration),
            type_parameters,
            None,
            plan.parameters
                .iter()
                .map(|parameter| parameter.symbol)
                .collect(),
            None,
            None,
            plan.min_argument_count,
        )
        .ok_or_else(|| invariant(SourceCallableInvariant::Publication(plan.declaration)))?;
    let provenance = store.set_source_callable_provenance(
        type_,
        SourceCallableProvenance {
            family: plan.family,
            declaration: plan.declaration,
            owner_symbol: plan.owner_symbol,
            owner_parent: plan.owner_parent,
            export_local: plan.export_local,
            signature,
            contextual_target: None,
            contextual_variable: None,
        },
    );
    assert!(
        provenance,
        "source callable provenance was prevalidated and reserved"
    );
    let return_annotation = store.set_function_signature_return_annotation(
        signature,
        plan.return_identity_node,
        plan.return_null_literal_identity,
    );
    assert!(
        return_annotation,
        "source callable return annotation was prevalidated and reserved"
    );
    if !store.set_value_symbol_links(
        plan.owner_symbol,
        ValueSymbolLinks {
            resolved_type: Some(type_),
            ..ValueSymbolLinks::default()
        },
    ) || !store.set_structured_type_members(type_, None, None, None, None, None)
        || !store.set_signature_links(
            plan.declaration,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(signature),
                ..SignatureLinks::default()
            },
        )
    {
        return Err(invariant(SourceCallableInvariant::Publication(
            plan.declaration,
        )));
    }
    Ok(Ok(PendingSourceCallable { type_, signature }))
}

/// Installs the exact source-function call surface: nil members/properties and
/// one direct call signature.
pub(super) fn finalize_source_callable_structure(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    pending: PendingSourceCallable,
) -> Result<(), SourceCallableError> {
    match source_callable_state(store, plan, true)? {
        SourceCallableState::ActiveBarrier { type_, signature }
            if type_ == pending.type_ && signature == pending.signature => {}
        SourceCallableState::ActiveParameters { type_, signature }
            if type_ == pending.type_ && signature == pending.signature =>
        {
            return Ok(());
        }
        _ => {
            return Err(invariant(SourceCallableInvariant::Publication(
                plan.declaration,
            )));
        }
    }
    if !store.set_structured_type_members(
        pending.type_,
        None,
        None,
        Some(vec![pending.signature]),
        None,
        None,
    ) {
        return Err(invariant(SourceCallableInvariant::Publication(
            plan.declaration,
        )));
    }
    if plan.parameters.is_empty() {
        let published = store
            .set_callable_signature_parameter_types_batch(vec![(pending.signature, Vec::new())]);
        assert!(
            published,
            "zero-parameter source callable provenance was prevalidated and reserved"
        );
    }
    Ok(())
}

/// Atomically publishes all parameter value types for a prevalidated batch.
pub(super) fn publish_source_callable_parameter_types(
    store: &mut CanonicalTypeMapperStore,
    global_types: Option<&CanonicalGlobalTypes>,
    pending: &[PendingSourceCallableParameterTypes],
    prepared: &mut PreparedTypeQueryTypes,
) -> Result<(), SourceCallableError> {
    let Some(first) = pending.first() else {
        return Ok(());
    };
    let strict = store
        .intrinsic_bootstrap()
        .ok_or_else(|| invariant(SourceCallableInvariant::Publication(first.plan.declaration)))?
        .options
        .strict_null_checks;
    let undefined = store
        .intrinsic_bootstrap()
        .expect("bootstrap was checked above")
        .undefined_type;
    let parameter_count = pending.iter().try_fold(0usize, |count, callable| {
        count
            .checked_add(callable.plan.parameters.len())
            .ok_or_else(|| invariant(SourceCallableInvariant::Capacity(callable.plan.declaration)))
    })?;
    for callable in pending {
        if callable.base_types.len() != callable.plan.parameters.len()
            || !matches!(
                source_callable_state(store, &callable.plan, true)?,
                SourceCallableState::ActiveParameters { .. }
            )
        {
            return Err(invariant(SourceCallableInvariant::Publication(
                callable.plan.declaration,
            )));
        }
        for (parameter, base) in callable.plan.parameters.iter().zip(&callable.base_types) {
            if store.type_payload(*base).is_none()
                || !default_parameter_links(store, parameter.symbol)
            {
                return Err(invariant(SourceCallableInvariant::Publication(
                    parameter.declaration,
                )));
            }
            let cached = cached_annotation_identity(
                store,
                parameter.identity_node,
                parameter.null_literal_identity,
            )
            .ok_or_else(|| {
                invariant(SourceCallableInvariant::InvalidParameterCache(
                    parameter.declaration,
                ))
            })?;
            if cached != *base
                || store
                    .validate_cached_array_capability_prepared(*base, global_types, prepared)
                    .is_err()
            {
                return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
                    parameter.declaration,
                )));
            }
        }
    }
    let mut resolved = Vec::with_capacity(parameter_count);
    let mut expected_parameter_types = Vec::with_capacity(pending.len());
    for callable in pending {
        let signature = exact_signature_link(store, callable.plan.declaration)?;
        let mut callable_parameter_types = Vec::with_capacity(callable.plan.parameters.len());
        for (parameter, base) in callable.plan.parameters.iter().zip(&callable.base_types) {
            let type_ = if strict && parameter.optional {
                let already_contains_undefined = *base == undefined
                    || store.type_payload(*base).is_some_and(|record| {
                        matches!(
                            record.data(),
                            TypeData::Union(union) if union.union.types.contains(&undefined)
                        )
                    });
                if already_contains_undefined {
                    *base
                } else {
                    match global_types {
                        Some(global_types) => store.literal_union_type_prepared_with_global_types(
                            global_types,
                            &[*base, undefined],
                            None,
                            prepared,
                        )?,
                        None => store.literal_union_type_prepared(
                            &[*base, undefined],
                            None,
                            prepared,
                        )?,
                    }
                }
            } else {
                *base
            };
            if store
                .validate_cached_array_capability_prepared(type_, global_types, prepared)
                .is_err()
            {
                return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
                    parameter.declaration,
                )));
            }
            resolved.push((parameter.symbol, type_));
            callable_parameter_types.push(type_);
        }
        expected_parameter_types.push((signature, callable_parameter_types));
    }
    let provenance = store.set_callable_signature_parameter_types_batch(expected_parameter_types);
    assert!(
        provenance,
        "prevalidated source parameter provenance publication is infallible"
    );
    for (symbol, type_) in resolved {
        let published = store.set_value_symbol_links(
            symbol,
            ValueSymbolLinks {
                resolved_type: Some(type_),
                ..ValueSymbolLinks::default()
            },
        );
        assert!(
            published,
            "prevalidated source callable parameter publication is infallible"
        );
    }
    for callable in pending {
        let state = source_callable_state(store, &callable.plan, false);
        assert!(
            matches!(state, Ok(SourceCallableState::Resolved { .. })),
            "prevalidated source callable batch must publish resolved caches"
        );
        let Ok(SourceCallableState::Resolved { type_, .. }) = state else {
            unreachable!()
        };
        let capability = match callable.plan.array_targets {
            Some(targets) => {
                store.validate_cached_array_capability_with_array_targets(targets, type_)
            }
            None => store.validate_cached_array_capability(type_),
        };
        assert!(
            capability.is_ok(),
            "source callable edges were prevalidated under the same capability"
        );
    }
    Ok(())
}

pub(super) fn validate_source_callable_signature_identity(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
) -> Result<(), SourceCallableError> {
    let matches = match source_callable_state(store, plan, true)? {
        SourceCallableState::ActiveBarrier {
            signature: cached, ..
        }
        | SourceCallableState::ActiveParameters {
            signature: cached, ..
        }
        | SourceCallableState::Resolved {
            signature: cached, ..
        } => cached == signature,
        SourceCallableState::Cold => false,
    };
    if !matches {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    Ok(())
}

pub(super) fn validate_lazy_source_callable_return(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
) -> Result<Option<TypeId>, SourceCallableError> {
    match source_callable_state(store, plan, false)? {
        SourceCallableState::Resolved {
            signature: cached, ..
        } if cached == signature => {}
        _ => {
            return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
                plan.declaration,
            )));
        }
    }
    Ok(store
        .signature(signature)
        .expect("the source callable cache was validated")
        .resolved_return_type())
}

pub(super) fn publish_lazy_source_callable_return(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
    return_type: TypeId,
) -> Result<TypeId, SourceCallableError> {
    let annotation = cached_annotation_identity(
        store,
        plan.return_identity_node,
        plan.return_null_literal_identity,
    );
    if store.type_payload(return_type).is_none()
        || store.signature_has_circular_return_type(signature)
        || validate_lazy_source_callable_return(store, plan, signature)?.is_some()
        || annotation != Some(return_type)
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    let published = store.set_signature_resolved_return_type(signature, Some(return_type));
    assert!(published, "lazy source return publication was prevalidated");
    validate_cached_return_type(store, plan, signature)?;
    Ok(return_type)
}

pub(super) fn publish_circular_lazy_source_callable_return(
    store: &mut CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
    annotation_type: TypeId,
) -> Result<TypeId, SourceCallableError> {
    let Some(bootstrap) = store.intrinsic_bootstrap() else {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    };
    let any_type = bootstrap.any_type;
    let annotation = cached_annotation_identity(
        store,
        plan.return_identity_node,
        plan.return_null_literal_identity,
    );
    if store.type_payload(annotation_type).is_none()
        || store.signature_has_circular_return_type(signature)
        || validate_lazy_source_callable_return(store, plan, signature)?.is_some()
        || annotation != Some(annotation_type)
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    let published =
        store.set_function_signature_circular_return_type(signature, any_type, annotation_type);
    assert!(
        published,
        "circular lazy source return publication was prevalidated"
    );
    validate_cached_return_type(store, plan, signature)?;
    Ok(any_type)
}

pub(super) fn source_callable_display_projection(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    type_: TypeId,
    array_targets: Option<CanonicalArrayTargets>,
) -> Result<ValidatedSingleCallSignatureDisplay, SourceCallableDisplayError> {
    let provenance = store
        .source_callable_provenance(type_)
        .ok_or(SourceCallableDisplayError::Malformed)?;
    if provenance.contextual_target.is_some() {
        if !matches!(
            validate_stored_source_callable(store, type_),
            StoredSourceCallableValidation::Valid(_)
        ) {
            return Err(SourceCallableDisplayError::Malformed);
        }
        let signature = store
            .signature(provenance.signature)
            .ok_or(SourceCallableDisplayError::Malformed)?;
        let expected_types = store
            .callable_signature_parameter_types(provenance.signature)
            .ok_or(SourceCallableDisplayError::Malformed)?;
        if expected_types.len() != signature.parameters().len() {
            return Err(SourceCallableDisplayError::Malformed);
        }
        let mut parameters = Vec::with_capacity(signature.parameters().len());
        for (parameter, value_type) in signature.parameters().iter().zip(expected_types) {
            let declaration = store
                .symbol(*parameter)
                .and_then(ts_binder::semantic::Symbol::value_declaration)
                .ok_or(SourceCallableDisplayError::Malformed)?;
            let parameter_node = host
                .node(declaration)
                .ok_or(SourceCallableDisplayError::Malformed)?;
            let NodeData::ParameterDeclaration(parameter_data) = &parameter_node.data else {
                return Err(SourceCallableDisplayError::Malformed);
            };
            if parameter_data.dot_dot_dot_token.is_some() {
                store
                    .validate_canonical_empty_tuple_type(*value_type)
                    .map_err(|_| SourceCallableDisplayError::Malformed)?;
                continue;
            }
            let name = NodeRef::new(declaration.arena, declaration.file, parameter_data.name);
            let name_node = host
                .node(name)
                .ok_or(SourceCallableDisplayError::Malformed)?;
            let NodeData::Identifier(identifier) = &name_node.data else {
                return Err(SourceCallableDisplayError::Malformed);
            };
            parameters.push(ValidatedSingleCallParameterDisplay {
                name: identifier.text.clone(),
                value_type: *value_type,
                optional: parameter_data.question_token.is_some(),
            });
        }
        return Ok(ValidatedSingleCallSignatureDisplay {
            owner: type_,
            parameters,
            return_type: signature.resolved_return_type(),
        });
    }
    let plan = plan_source_callable(
        store,
        host,
        provenance.declaration,
        provenance.owner_symbol,
        array_targets,
    )
    .map_err(source_callable_display_error)?;
    if !plan.type_parameters.is_empty() {
        return Err(SourceCallableDisplayError::Unsupported(
            SourceCallableUnsupported::GenericSignature(plan.declaration),
        ));
    }
    let signature =
        match source_callable_state(store, &plan, true).map_err(source_callable_display_error)? {
            SourceCallableState::Resolved {
                type_: resolved,
                signature,
            } if resolved == type_ && signature == provenance.signature => signature,
            SourceCallableState::ActiveBarrier { .. }
            | SourceCallableState::ActiveParameters { .. } => {
                return Err(SourceCallableDisplayError::Pending);
            }
            SourceCallableState::Cold | SourceCallableState::Resolved { .. } => {
                return Err(SourceCallableDisplayError::Malformed);
            }
        };
    let return_type = store
        .signature(signature)
        .ok_or(SourceCallableDisplayError::Malformed)?
        .resolved_return_type();
    let mut parameters = Vec::with_capacity(plan.parameters.len());
    for parameter in &plan.parameters {
        let value_type = store
            .value_symbol_links(parameter.symbol)
            .and_then(|links| links.resolved_type)
            .ok_or(SourceCallableDisplayError::Malformed)?;
        let parameter_node = host
            .node(parameter.declaration)
            .ok_or(SourceCallableDisplayError::Malformed)?;
        let NodeData::ParameterDeclaration(parameter_data) = &parameter_node.data else {
            return Err(SourceCallableDisplayError::Malformed);
        };
        let name = NodeRef::new(
            parameter.declaration.arena,
            parameter.declaration.file,
            parameter_data.name,
        );
        let name_node = host
            .node(name)
            .ok_or(SourceCallableDisplayError::Malformed)?;
        let NodeData::Identifier(identifier) = &name_node.data else {
            return Err(SourceCallableDisplayError::Malformed);
        };
        parameters.push(ValidatedSingleCallParameterDisplay {
            name: identifier.text.clone(),
            value_type,
            optional: parameter.optional,
        });
    }
    Ok(ValidatedSingleCallSignatureDisplay {
        owner: type_,
        parameters,
        return_type,
    })
}

const fn source_callable_display_error(error: SourceCallableError) -> SourceCallableDisplayError {
    match error {
        SourceCallableError::Unsupported(reason) => SourceCallableDisplayError::Unsupported(reason),
        SourceCallableError::Invariant(_)
        | SourceCallableError::DeclaredType(_)
        | SourceCallableError::LiteralCache(_) => SourceCallableDisplayError::Malformed,
    }
}

/// Validates a source callable using only retained store state.
pub(super) fn validate_stored_source_callable(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> StoredSourceCallableValidation {
    let provenance = store.source_callable_provenance(type_);
    let not_source = || {
        if provenance.is_some() {
            StoredSourceCallableValidation::Malformed
        } else {
            StoredSourceCallableValidation::NotSourceCallable
        }
    };
    let Some(record) = store.type_payload(type_) else {
        return not_source();
    };
    let Some(owner_symbol) = record.symbol() else {
        return not_source();
    };
    let Some(owner) = store.symbol(owner_symbol) else {
        return not_source();
    };
    let Some(declaration) = owner
        .declarations()
        .and_then(|declarations| (declarations.len() == 1).then_some(declarations[0]))
    else {
        return not_source();
    };
    let Some(family) = source_family_for_kind(store.source_node_kind(declaration)) else {
        return not_source();
    };
    let Some(provenance) = provenance else {
        return StoredSourceCallableValidation::Malformed;
    };
    if provenance
        != (SourceCallableProvenance {
            family,
            declaration,
            owner_symbol,
            owner_parent: provenance.owner_parent,
            export_local: provenance.export_local,
            signature: provenance.signature,
            contextual_target: provenance.contextual_target,
            contextual_variable: provenance.contextual_variable,
        })
        || store.source_callable_type_for_owner(owner_symbol) != Some(type_)
        || store.source_callable_type_for_signature(provenance.signature) != Some(type_)
        || store.source_callable_type_for_declaration(declaration) != Some(type_)
    {
        return StoredSourceCallableValidation::Malformed;
    }
    let Some(signature) = store.signature_links(declaration).and_then(|links| {
        (links.effects_signature == EffectsSignatureState::Unresolved
            && links.decorator_signature == DecoratorSignatureState::Unresolved)
            .then_some(links.resolved_signature)
    }) else {
        return StoredSourceCallableValidation::Malformed;
    };
    let ResolvedSignatureState::Resolved(signature) = signature else {
        return StoredSourceCallableValidation::Malformed;
    };
    if signature != provenance.signature {
        return StoredSourceCallableValidation::Malformed;
    }
    let Some(signature_record) = store.signature(signature) else {
        return StoredSourceCallableValidation::Malformed;
    };
    let contextual = provenance
        .contextual_target
        .zip(provenance.contextual_variable);
    let Some(TypeData::Object(object)) = store.type_payload(type_).map(TypeRecord::data) else {
        return StoredSourceCallableValidation::Malformed;
    };
    let expected_parameter_types = store.callable_signature_parameter_types(signature);
    let Some(type_parameter_edges) = valid_stored_source_type_parameters(
        store,
        declaration,
        family,
        contextual.is_some(),
        signature_record.type_parameters(),
    ) else {
        return StoredSourceCallableValidation::Malformed;
    };
    let generic_type_parameter = type_parameter_edges.first().copied();
    let mut edges =
        Vec::with_capacity(signature_record.parameters().len() + type_parameter_edges.len() + 2);
    edges.extend(type_parameter_edges);
    let mut default_parameter_count = 0usize;
    let parameters_valid =
        signature_record
            .parameters()
            .iter()
            .enumerate()
            .all(|(index, parameter)| {
                let Some(parameter_record) = store.symbol(*parameter) else {
                    return false;
                };
                let Some(parameter_declaration) = parameter_record
                    .declarations()
                    .and_then(|declarations| (declarations.len() == 1).then_some(declarations[0]))
                else {
                    return false;
                };
                let links_valid = match store.value_symbol_links(*parameter) {
                    None => {
                        default_parameter_count += 1;
                        true
                    }
                    Some(links) if links == &ValueSymbolLinks::default() => {
                        default_parameter_count += 1;
                        true
                    }
                    Some(links) if links.resolved_type.is_some() => {
                        let resolved = links.resolved_type.expect("the branch checked the type");
                        let valid = links
                            == &(ValueSymbolLinks {
                                resolved_type: Some(resolved),
                                ..ValueSymbolLinks::default()
                            })
                            && expected_parameter_types
                                .and_then(|types| types.get(index))
                                .copied()
                                == Some(resolved);
                        if valid {
                            edges.push(resolved);
                        }
                        valid
                    }
                    Some(_) => false,
                };
                parameter_record.flags() == SymbolFlags::FUNCTION_SCOPED_VARIABLE
                    && parameter_record.check_flags() == CheckFlags::NONE
                    && parameter_record.value_declaration() == Some(parameter_declaration)
                    && parameter_record.members().is_none()
                    && parameter_record.exports().is_none()
                    && parameter_record.parent().is_none()
                    && parameter_record.export_symbol().is_none()
                    && store.get_merged_symbol(*parameter) == Some(*parameter)
                    && store.source_node_kind(parameter_declaration) == Some(SyntaxKind::Parameter)
                    && store.source_node_parent(parameter_declaration)
                        == Some(SourceNodeParent::Parent(declaration))
                    && links_valid
            });
    let parameters_unique = signature_record
        .parameters()
        .iter()
        .enumerate()
        .all(|(index, parameter)| !signature_record.parameters()[..index].contains(parameter));
    let owner_links = ValueSymbolLinks {
        resolved_type: Some(type_),
        ..ValueSymbolLinks::default()
    };
    if record.flags() != TypeFlags::OBJECT
        || record.object_flags() != ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
        || record.alias().is_some()
        || owner.flags() != SymbolFlags::FUNCTION
        || owner.check_flags() != CheckFlags::NONE
        || owner.value_declaration() != Some(declaration)
        || owner.members().is_some()
        || owner.exports().is_some()
        || owner.export_symbol().is_some()
        || owner.parent() != provenance.owner_parent
        || family == SourceCallableFamily::ArrowFunction
            && (owner.name() != InternalSymbolName::Function.as_ref()
                || provenance.owner_parent.is_some()
                || provenance.export_local.is_some())
        || family == SourceCallableFamily::FunctionDeclaration
            && !valid_stored_function_export_route(
                store,
                owner_symbol,
                owner,
                declaration,
                provenance,
            )
        || store.get_merged_symbol(owner_symbol) != Some(owner_symbol)
        || store.value_symbol_links(owner_symbol) != Some(&owner_links)
        || signature_record.flags().bits()
            & !(if contextual.is_some() {
                SignatureFlags::HAS_REST_PARAMETER
            } else {
                SignatureFlags::HAS_LITERAL_TYPES
            })
            .bits()
            != 0
        || signature_record.min_argument_count() < 0
        || usize::try_from(signature_record.min_argument_count()).map_or(true, |minimum| {
            minimum > signature_record.parameters().len()
        })
        || signature_record.resolved_min_argument_count() != -1
        || signature_record.declaration() != Some(declaration)
        || signature_record.this_parameter().is_some()
        || signature_record.resolved_type_predicate().is_some()
        || signature_record.target().is_some()
        || signature_record.mapper().is_some()
        || signature_record.isolated_signature_type().is_some()
        || signature_record.composite().is_some()
        || !valid_stored_generic_source_signature(
            signature_record,
            expected_parameter_types,
            generic_type_parameter,
        )
        || !parameters_valid
        || default_parameter_count != 0
            && default_parameter_count != signature_record.parameters().len()
        || !parameters_unique
        || contextual.is_some() && default_parameter_count != 0
        || object.structured.constrained != ConstrainedTypeData::default()
        || object.target.is_some()
        || object.mapper.is_some()
        || object.instantiations != TypeCacheState::Unallocated
    {
        return StoredSourceCallableValidation::Malformed;
    }
    if object.structured == StructuredTypeData::default() {
        return if default_parameter_count == signature_record.parameters().len()
            && expected_parameter_types.is_none()
            && signature_record.resolved_return_type().is_none()
            && !store.signature_has_circular_return_type(signature)
        {
            StoredSourceCallableValidation::Pending
        } else {
            StoredSourceCallableValidation::Malformed
        };
    }
    if object.structured.members.is_some()
        || object.structured.properties.is_some()
        || object.structured.signatures.as_deref() != Some(&[signature])
        || object.structured.call_signature_count != 1
        || object.structured.index_infos.is_some()
        || object
            .structured
            .object_type_without_abstract_construct_signatures
            .is_some()
    {
        return StoredSourceCallableValidation::Malformed;
    }
    if default_parameter_count != 0 {
        if expected_parameter_types.is_some()
            || signature_record.resolved_return_type().is_some()
            || store.signature_has_circular_return_type(signature)
        {
            return StoredSourceCallableValidation::Malformed;
        }
        return StoredSourceCallableValidation::Pending;
    }
    if expected_parameter_types
        .is_none_or(|types| types.len() != signature_record.parameters().len())
    {
        return StoredSourceCallableValidation::Malformed;
    }
    if let Some((target, variable)) = contextual {
        let variable_valid = store.symbol(variable).is_some_and(|symbol| {
            symbol.flags() == SymbolFlags::BLOCK_SCOPED_VARIABLE
                && symbol.check_flags() == CheckFlags::NONE
                && symbol.members().is_none()
                && symbol.exports().is_none()
                && symbol.parent().is_none()
                && symbol.export_symbol().is_none()
                && store.get_merged_symbol(variable) == Some(variable)
        });
        let return_type = signature_record.resolved_return_type();
        let return_valid = store.intrinsic_bootstrap().is_some_and(|bootstrap| {
            return_type == Some(bootstrap.void_type)
                && store
                    .function_signature_return_annotation(signature)
                    .is_none()
                && !store.signature_has_circular_return_type(signature)
        });
        let target_valid = target != type_
            && matches!(
                validate_stored_function_type(store, target),
                StoredFunctionTypeValidation::Valid(_)
            );
        let rest_valid = if signature_record
            .flags()
            .contains(SignatureFlags::HAS_REST_PARAMETER)
        {
            expected_parameter_types
                .and_then(|types| types.last())
                .copied()
                .is_some_and(|rest| store.validate_canonical_empty_tuple_type(rest).is_ok())
        } else {
            true
        };
        if !variable_valid || !return_valid || !target_valid || !rest_valid {
            return StoredSourceCallableValidation::Malformed;
        }
        edges.push(target);
        edges.push(return_type.expect("the contextual return was validated"));
        return StoredSourceCallableValidation::Valid(edges);
    }
    let Some((return_identity_node, return_null_literal_identity)) =
        store.function_signature_return_annotation(signature)
    else {
        return StoredSourceCallableValidation::Malformed;
    };
    if let Some(return_type) = signature_record.resolved_return_type() {
        let annotation =
            cached_annotation_identity(store, return_identity_node, return_null_literal_identity);
        if let Some(type_parameter) = generic_type_parameter {
            let Some(symbol) = cached_ordinary_type_parameter_owner(store, type_parameter) else {
                return StoredSourceCallableValidation::Malformed;
            };
            if !source_type_parameter_annotation_links_are_fully_warm(
                store,
                return_identity_node,
                symbol,
                type_parameter,
            ) {
                return StoredSourceCallableValidation::Malformed;
            }
        }
        let valid_return =
            if let Some(circular_annotation) = store.circular_return_annotation_type(signature) {
                let valid = store.intrinsic_bootstrap().is_some_and(|bootstrap| {
                    annotation == Some(circular_annotation) && return_type == bootstrap.any_type
                });
                if valid {
                    edges.push(circular_annotation);
                }
                valid
            } else {
                annotation == Some(return_type)
            };
        if !valid_return {
            return StoredSourceCallableValidation::Malformed;
        }
        edges.push(return_type);
    } else if store.signature_has_circular_return_type(signature) {
        return StoredSourceCallableValidation::Malformed;
    }
    StoredSourceCallableValidation::Valid(edges)
}

fn valid_stored_generic_source_signature(
    signature: &Signature,
    parameter_types: Option<&[TypeId]>,
    type_parameter: Option<TypeId>,
) -> bool {
    let Some(type_parameter) = type_parameter else {
        return true;
    };
    signature.flags() == SignatureFlags::NONE
        && signature.parameters().len() == 1
        && signature.min_argument_count() == 1
        && parameter_types.is_none_or(|types| types == [type_parameter])
        && signature
            .resolved_return_type()
            .is_none_or(|return_type| return_type == type_parameter)
}

fn valid_stored_source_type_parameters(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
    family: SourceCallableFamily,
    contextual: bool,
    type_parameters: &[TypeId],
) -> Option<Vec<TypeId>> {
    if type_parameters.is_empty() {
        return Some(Vec::new());
    }
    if contextual
        || family != SourceCallableFamily::FunctionDeclaration
        || type_parameters.len() != 1
    {
        return None;
    }
    let type_parameter = type_parameters[0];
    let symbol = cached_ordinary_type_parameter_owner(store, type_parameter)?;
    let symbol_record = store.symbol(symbol)?;
    let [type_parameter_declaration] = symbol_record.declarations()? else {
        return None;
    };
    if symbol_record.flags() != SymbolFlags::TYPE_PARAMETER
        || symbol_record.check_flags() != CheckFlags::NONE
        || symbol_record.value_declaration().is_some()
        || symbol_record.members().is_some()
        || symbol_record.exports().is_some()
        || symbol_record.parent().is_some()
        || symbol_record.export_symbol().is_some()
        || store.get_merged_symbol(symbol) != Some(symbol)
        || store.source_node_kind(*type_parameter_declaration) != Some(SyntaxKind::TypeParameter)
        || store.source_node_parent(*type_parameter_declaration)
            != Some(SourceNodeParent::Parent(declaration))
    {
        return None;
    }
    Some(vec![type_parameter])
}

fn valid_stored_function_export_route(
    store: &CanonicalTypeMapperStore,
    owner_symbol: SemanticSymbolId,
    owner: &ts_binder::semantic::Symbol,
    declaration: NodeRef,
    provenance: SourceCallableProvenance,
) -> bool {
    match (provenance.owner_parent, provenance.export_local) {
        (None, None) => owner.parent().is_none(),
        (Some(parent), Some(local)) if owner.parent() == Some(parent) => {
            store.symbol(local).is_some_and(|local_record| {
                store.get_merged_symbol(local) == Some(local)
                    && local_record.flags() == SymbolFlags::EXPORT_VALUE
                    && local_record.check_flags() == CheckFlags::NONE
                    && local_record.name() == owner.name()
                    && local_record.declarations() == Some(&[declaration])
                    && local_record.value_declaration().is_none()
                    && local_record.members().is_none()
                    && local_record.exports().is_none()
                    && local_record.parent().is_none()
                    && local_record.export_symbol() == Some(owner_symbol)
            })
        }
        _ => false,
    }
}

/// Returns the retained source family for either a branded callable or an
/// otherwise source-callable-shaped record rejected by the store validator.
pub(super) fn stored_source_callable_family(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
) -> Option<SourceCallableFamily> {
    if let Some(provenance) = store.source_callable_provenance(type_) {
        return Some(provenance.family);
    }
    let declaration = store
        .type_payload(type_)?
        .symbol()
        .and_then(|owner| store.symbol(owner))?
        .declarations()
        .and_then(|declarations| (declarations.len() == 1).then_some(declarations[0]))?;
    source_family_for_kind(store.source_node_kind(declaration))
}

const fn source_family_for_kind(kind: Option<SyntaxKind>) -> Option<SourceCallableFamily> {
    match kind {
        Some(SyntaxKind::FunctionDeclaration) => Some(SourceCallableFamily::FunctionDeclaration),
        Some(SyntaxKind::ArrowFunction) => Some(SourceCallableFamily::ArrowFunction),
        _ => None,
    }
}

fn validate_signature(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
) -> Result<(), SourceCallableError> {
    let record = store.signature(signature).ok_or_else(|| {
        invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        ))
    })?;
    let expected_parameters = plan
        .parameters
        .iter()
        .map(|parameter| parameter.symbol)
        .collect::<Vec<_>>();
    let expected_type_parameters = planned_type_parameter_ids(store, plan).ok_or_else(|| {
        invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        ))
    })?;
    if record.flags() != plan.flags
        || record.min_argument_count() != plan.min_argument_count
        || record.resolved_min_argument_count() != -1
        || record.declaration() != Some(plan.declaration)
        || record.type_parameters() != expected_type_parameters
        || record.parameters() != expected_parameters
        || record.this_parameter().is_some()
        || record.resolved_type_predicate().is_some()
        || record.target().is_some()
        || record.mapper().is_some()
        || record.isolated_signature_type().is_some()
        || record.composite().is_some()
        || store.function_signature_return_annotation(signature)
            != Some((plan.return_identity_node, plan.return_null_literal_identity))
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    Ok(())
}

fn planned_type_parameter_ids(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
) -> Option<Vec<TypeId>> {
    plan.type_parameters
        .iter()
        .map(|type_parameter| {
            let declared_type = store
                .declared_type_links(type_parameter.symbol)?
                .declared_type?;
            (cached_ordinary_type_parameter_owner(store, declared_type)
                == Some(type_parameter.symbol))
            .then_some(declared_type)
        })
        .collect()
}

fn exact_signature_link(
    store: &CanonicalTypeMapperStore,
    declaration: NodeRef,
) -> Result<SignatureId, SourceCallableError> {
    let Some(links) = store.signature_links(declaration) else {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            declaration,
        )));
    };
    let ResolvedSignatureState::Resolved(signature) = links.resolved_signature else {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            declaration,
        )));
    };
    if links.effects_signature != EffectsSignatureState::Unresolved
        || links.decorator_signature != DecoratorSignatureState::Unresolved
    {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            declaration,
        )));
    }
    Ok(signature)
}

fn default_signature_links(store: &CanonicalTypeMapperStore, declaration: NodeRef) -> bool {
    store
        .signature_links(declaration)
        .is_none_or(|links| links == &SignatureLinks::default())
}

fn default_parameter_links(store: &CanonicalTypeMapperStore, symbol: SemanticSymbolId) -> bool {
    store
        .value_symbol_links(symbol)
        .is_none_or(|links| links == &ValueSymbolLinks::default())
}

fn validate_parameter_links(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    parameter: &SourceCallableParameterPlan,
    expected: TypeId,
) -> Result<(), SourceCallableError> {
    let links = store.value_symbol_links(parameter.symbol).ok_or_else(|| {
        invariant(SourceCallableInvariant::InvalidParameterCache(
            parameter.declaration,
        ))
    })?;
    let Some(resolved) = links.resolved_type else {
        return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
            parameter.declaration,
        )));
    };
    if resolved != expected
        || links
            != &(ValueSymbolLinks {
                resolved_type: Some(resolved),
                ..ValueSymbolLinks::default()
            })
    {
        return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
            parameter.declaration,
        )));
    }
    let base = cached_annotation_identity(
        store,
        parameter.identity_node,
        parameter.null_literal_identity,
    )
    .ok_or_else(|| {
        invariant(SourceCallableInvariant::InvalidParameterCache(
            parameter.declaration,
        ))
    })?;
    let strict = store
        .intrinsic_bootstrap()
        .ok_or_else(|| {
            invariant(SourceCallableInvariant::InvalidParameterCache(
                parameter.declaration,
            ))
        })?
        .options
        .strict_null_checks;
    let valid = if strict && parameter.optional {
        valid_optional_type(store, plan.array_targets, base, resolved)
    } else {
        base == resolved
    };
    if !valid {
        return Err(invariant(SourceCallableInvariant::InvalidParameterCache(
            parameter.declaration,
        )));
    }
    Ok(())
}

fn validate_cached_return_type(
    store: &CanonicalTypeMapperStore,
    plan: &SourceCallablePlan,
    signature: SignatureId,
) -> Result<(), SourceCallableError> {
    let resolved = store
        .signature(signature)
        .and_then(Signature::resolved_return_type);
    let circular_annotation = store.circular_return_annotation_type(signature);
    if resolved.is_none() {
        return if circular_annotation.is_some() {
            Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
                plan.declaration,
            )))
        } else {
            Ok(())
        };
    }
    let resolved = resolved.expect("the unresolved branch returned");
    let annotation = cached_annotation_identity(
        store,
        plan.return_identity_node,
        plan.return_null_literal_identity,
    );
    let valid = if let Some(circular_annotation) = circular_annotation {
        store.intrinsic_bootstrap().is_some_and(|bootstrap| {
            annotation == Some(circular_annotation) && resolved == bootstrap.any_type
        })
    } else {
        annotation == Some(resolved)
    };
    if !valid {
        return Err(invariant(SourceCallableInvariant::InvalidSignatureCache(
            plan.declaration,
        )));
    }
    Ok(())
}

fn cached_annotation_identity(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    null_literal_identity: bool,
) -> Option<TypeId> {
    let kind = store.source_node_kind(node)?;
    let bootstrap = store.intrinsic_bootstrap()?;
    if null_literal_identity {
        return Some(bootstrap.null_type);
    }
    let keyword = match kind {
        SyntaxKind::AnyKeyword => Some(bootstrap.any_type),
        SyntaxKind::UnknownKeyword => Some(bootstrap.unknown_type),
        SyntaxKind::StringKeyword => Some(bootstrap.string_type),
        SyntaxKind::NumberKeyword => Some(bootstrap.number_type),
        SyntaxKind::BigIntKeyword => Some(bootstrap.bigint_type),
        SyntaxKind::BooleanKeyword => Some(bootstrap.boolean_type),
        SyntaxKind::SymbolKeyword => Some(bootstrap.es_symbol_type),
        SyntaxKind::VoidKeyword => Some(bootstrap.void_type),
        SyntaxKind::UndefinedKeyword => Some(bootstrap.undefined_type),
        SyntaxKind::NullKeyword => Some(bootstrap.null_type),
        SyntaxKind::NeverKeyword => Some(bootstrap.never_type),
        SyntaxKind::ObjectKeyword => Some(bootstrap.non_primitive_type),
        SyntaxKind::IntrinsicKeyword => Some(bootstrap.intrinsic_marker_type),
        _ => None,
    };
    keyword.or_else(|| {
        store
            .type_node_links(node)
            .and_then(|links| links.resolved_type)
    })
}

fn peel_parenthesized_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    mut node: NodeRef,
) -> Result<NodeRef, SourceCallableError> {
    loop {
        let record = preflight_node(store, host, node)?;
        let NodeData::ParenthesizedTypeNode(parenthesized) = &record.data else {
            return Ok(node);
        };
        if record.kind != SyntaxKind::ParenthesizedType {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(node)));
        }
        let inner = NodeRef::new(node.arena, node.file, parenthesized.type_);
        if preflight_node(store, host, inner)?.parent != Some(node.node) {
            return Err(invariant(SourceCallableInvariant::InvalidSyntax(node)));
        }
        node = inner;
    }
}

fn is_null_literal_type(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    node: NodeRef,
) -> Result<bool, SourceCallableError> {
    let record = preflight_node(store, host, node)?;
    let NodeData::LiteralTypeNode(literal) = &record.data else {
        return Ok(false);
    };
    if record.kind != SyntaxKind::LiteralType {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(node)));
    }
    let literal = NodeRef::new(node.arena, node.file, literal.literal);
    let literal_record = preflight_node(store, host, literal)?;
    if literal_record.parent != Some(node.node) || literal_record.range != record.range {
        return Err(invariant(SourceCallableInvariant::InvalidSyntax(node)));
    }
    Ok(literal_record.kind == SyntaxKind::NullKeyword
        && matches!(literal_record.data, NodeData::KeywordExpression(_)))
}

fn valid_optional_type(
    store: &CanonicalTypeMapperStore,
    array_targets: Option<CanonicalArrayTargets>,
    base: TypeId,
    resolved: TypeId,
) -> bool {
    let Some(undefined) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.undefined_type)
    else {
        return false;
    };
    let Some(base_record) = store.type_payload(base) else {
        return false;
    };
    if base == undefined
        || base_record
            .flags()
            .intersects(TypeFlags::ANY | TypeFlags::UNKNOWN)
    {
        return resolved == base;
    }
    let mut expected = match base_record.data() {
        TypeData::Union(union) if union.union.types.contains(&undefined) => {
            let valid = match array_targets {
                Some(targets) => store.validate_union_constituent_with_array_targets(targets, base),
                None => store.validate_union_constituent(base),
            };
            return resolved == base && valid.is_ok();
        }
        TypeData::Union(_) => {
            return store
                .validate_optional_union_of_union_result(array_targets, base, undefined, resolved)
                .is_ok();
        }
        _ => vec![base],
    };
    expected.retain(|type_| {
        store
            .type_payload(*type_)
            .is_some_and(|record| !record.flags().intersects(TypeFlags::NEVER))
    });
    if !expected.contains(&undefined) {
        expected.push(undefined);
    }
    if expected.len() == 1 {
        return resolved == expected[0];
    }
    let Some(TypeData::Union(union)) = store.type_payload(resolved).map(TypeRecord::data) else {
        return false;
    };
    let valid_union = match array_targets {
        Some(targets) => {
            store.validate_cached_union_result_with_array_targets(targets, resolved, None)
        }
        None => store.validate_cached_union_result(resolved, None),
    };
    expected.len() == union.union.types.len()
        && expected
            .iter()
            .all(|expected| union.union.types.contains(expected))
        && valid_union.is_ok()
}

const fn invariant(error: SourceCallableInvariant) -> SourceCallableError {
    SourceCallableError::Invariant(error)
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, NodeData, NodeRef};
    use ts_binder::{
        BoundFile, CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
        DeclaredTypeLinks, IntrinsicBootstrapOptions,
        production::GlobalMergeCompletion,
        source::{SourceCheckError, UnsupportedSourceSyntax},
        source_functions::SourceFunctionUnsupported,
        type_nodes::{CanonicalTypeQuery, CanonicalTypeQueryOptions},
    };

    struct QueryFixture {
        parsed: ParseResult,
        file: FileId,
        bound: BoundFile,
        store: CanonicalTypeMapperStore,
    }

    impl QueryFixture {
        fn new(source: &str, file: FileId) -> Self {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let mut binder = CanonicalBinder::new();
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source("\"/project/source_generic_query.ts\""),
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
            let mut store = CanonicalTypeMapperStore::from_symbol_store(symbols);
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

        fn generic_parts(&self) -> (NodeRef, NodeRef, NodeRef, NodeRef) {
            generic_function_parts(&self.parsed, self.file)
        }

        fn declaration_and_type_parameter(&self) -> (NodeRef, NodeRef) {
            let (declaration, type_parameter, _, _) = self.generic_parts();
            (declaration, type_parameter)
        }

        fn query_callable(
            &mut self,
            declaration: NodeRef,
            owner: SemanticSymbolId,
            diagnostics: &mut CanonicalCheckerDiagnostics,
        ) -> Result<TypeId, DeclaredTypeError> {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&self.parsed.arena, &self.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            CanonicalTypeQuery::new(
                &mut self.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                diagnostics,
            )?
            .get_type_of_source_callable(declaration, owner)
        }

        fn query_return(
            &mut self,
            signature: SignatureId,
            diagnostics: &mut CanonicalCheckerDiagnostics,
        ) -> Result<TypeId, DeclaredTypeError> {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&self.parsed.arena, &self.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            CanonicalTypeQuery::new(
                &mut self.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                diagnostics,
            )?
            .get_return_type_of_signature(signature)
        }

        fn query_type_node(
            &mut self,
            node: NodeRef,
            diagnostics: &mut CanonicalCheckerDiagnostics,
        ) -> Result<TypeId, DeclaredTypeError> {
            let host = DeclaredTypeHost::new_after_global_merge(
                [(&self.parsed.arena, &self.bound)],
                GlobalMergeCompletion::for_test(CanonicalNameResolverOptions::default()),
            )
            .unwrap();
            CanonicalTypeQuery::new(
                &mut self.store,
                &host,
                CanonicalTypeQueryOptions::default(),
                diagnostics,
            )?
            .get_type_from_type_node(node)
        }
    }

    fn bind_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source("\"/project/source_generic.ts\""),
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

    fn generic_function_parts(
        parsed: &ParseResult,
        file: FileId,
    ) -> (NodeRef, NodeRef, NodeRef, NodeRef) {
        let source = parsed.arena.get(parsed.source_file).unwrap();
        let NodeData::SourceFile(source) = &source.data else {
            panic!("expected source file")
        };
        for statement in &source.statements.nodes {
            let record = parsed.arena.get(*statement).unwrap();
            let NodeData::FunctionDeclaration(function) = &record.data else {
                continue;
            };
            let type_parameters = function
                .type_parameters
                .as_ref()
                .expect("expected generic function");
            let parameter = parsed
                .arena
                .get(function.parameters.nodes[0])
                .expect("expected generic parameter");
            let NodeData::ParameterDeclaration(parameter) = &parameter.data else {
                panic!("expected parameter declaration")
            };
            return (
                NodeRef::new(parsed.arena.id(), file, *statement),
                NodeRef::new(parsed.arena.id(), file, type_parameters.nodes[0]),
                NodeRef::new(
                    parsed.arena.id(),
                    file,
                    parameter.type_.expect("expected parameter annotation"),
                ),
                NodeRef::new(
                    parsed.arena.id(),
                    file,
                    function.type_.expect("expected return annotation"),
                ),
            );
        }
        panic!("expected function declaration")
    }

    fn function_and_type_parameter(parsed: &ParseResult, file: FileId) -> (NodeRef, NodeRef) {
        let (declaration, type_parameter, _, _) = generic_function_parts(parsed, file);
        (declaration, type_parameter)
    }

    fn publication_state(store: &CanonicalTypeMapperStore) -> (usize, usize, [usize; 4], usize) {
        (
            store.types().len(),
            store.signature_len(),
            store.source_callable_provenance_lengths(),
            store.callable_signature_parameter_types_len(),
        )
    }

    fn assert_exact_warm_type_parameter_annotation(
        store: &CanonicalTypeMapperStore,
        annotation: NodeRef,
        symbol: SemanticSymbolId,
        type_: TypeId,
    ) {
        assert_eq!(
            store.symbol_node_links(annotation),
            Some(&SymbolNodeLinks {
                resolved_symbol: Some(symbol),
            })
        );
        assert_eq!(
            store.type_node_links(annotation),
            Some(&TypeNodeLinks {
                resolved_type: Some(type_),
                outer_type_parameters: None,
            })
        );
    }

    #[test]
    fn exact_generic_identity_query_publishes_and_reuses_one_declared_identity() {
        let mut fixture = QueryFixture::new(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(951),
        );
        let (declaration, type_parameter_declaration) = fixture.declaration_and_type_parameter();
        let owner = fixture.bound.symbol(declaration).unwrap();
        let type_parameter_symbol = fixture.bound.symbol(type_parameter_declaration).unwrap();
        assert!(
            fixture
                .store
                .declared_type_links(type_parameter_symbol)
                .is_none()
        );
        assert!(
            fixture
                .store
                .source_callable_type_for_owner(owner)
                .is_none()
        );

        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        let callable = fixture
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = fixture
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let type_parameter = fixture
            .store
            .signature(signature)
            .unwrap()
            .type_parameters()[0];
        assert_eq!(
            fixture
                .store
                .declared_type_links(type_parameter_symbol)
                .and_then(|links| links.declared_type),
            Some(type_parameter)
        );
        let [parameter] = fixture.store.signature(signature).unwrap().parameters() else {
            panic!("expected identity parameter")
        };
        assert_eq!(
            fixture
                .store
                .value_symbol_links(*parameter)
                .and_then(|links| links.resolved_type),
            Some(type_parameter)
        );
        assert_eq!(
            fixture.query_return(signature, &mut diagnostics),
            Ok(type_parameter)
        );
        assert!(matches!(
            validate_stored_source_callable(&fixture.store, callable),
            StoredSourceCallableValidation::Valid(edges) if edges.contains(&type_parameter)
        ));

        let warm = publication_state(&fixture.store);
        assert_eq!(
            fixture.query_callable(declaration, owner, &mut diagnostics),
            Ok(callable)
        );
        assert_eq!(
            fixture.query_return(signature, &mut diagnostics),
            Ok(type_parameter)
        );
        assert_eq!(publication_state(&fixture.store), warm);
        assert_eq!(
            fixture
                .store
                .signature(signature)
                .unwrap()
                .type_parameters(),
            [type_parameter]
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn generic_annotation_warm_orders_reuse_the_declared_identity() {
        for (index, warm_return_first) in [false, true].into_iter().enumerate() {
            let mut fixture = QueryFixture::new(
                "function identity<T>(value: T): T { return value; }",
                FileId::new(953 + u32::try_from(index).unwrap()),
            );
            let (declaration, type_parameter_declaration, parameter_type, return_type) =
                fixture.generic_parts();
            let owner = fixture.bound.symbol(declaration).unwrap();
            let type_parameter_symbol = fixture.bound.symbol(type_parameter_declaration).unwrap();
            let first = if warm_return_first {
                return_type
            } else {
                parameter_type
            };
            let second = if warm_return_first {
                parameter_type
            } else {
                return_type
            };
            let mut diagnostics = CanonicalCheckerDiagnostics::default();

            let type_parameter = fixture.query_type_node(first, &mut diagnostics).unwrap();
            assert_eq!(
                fixture
                    .store
                    .declared_type_links(type_parameter_symbol)
                    .and_then(|links| links.declared_type),
                Some(type_parameter)
            );
            assert_exact_warm_type_parameter_annotation(
                &fixture.store,
                first,
                type_parameter_symbol,
                type_parameter,
            );
            assert!(
                fixture
                    .store
                    .symbol_node_links(second)
                    .is_none_or(|links| links == &SymbolNodeLinks::default())
            );
            assert!(
                fixture
                    .store
                    .type_node_links(second)
                    .is_none_or(|links| links == &TypeNodeLinks::default())
            );

            let callable = fixture
                .query_callable(declaration, owner, &mut diagnostics)
                .unwrap();
            let signature = fixture
                .store
                .source_callable_provenance(callable)
                .unwrap()
                .signature;
            assert_exact_warm_type_parameter_annotation(
                &fixture.store,
                parameter_type,
                type_parameter_symbol,
                type_parameter,
            );
            assert_eq!(
                fixture.query_return(signature, &mut diagnostics),
                Ok(type_parameter)
            );
            assert_exact_warm_type_parameter_annotation(
                &fixture.store,
                return_type,
                type_parameter_symbol,
                type_parameter,
            );
            assert!(matches!(
                validate_stored_source_callable(&fixture.store, callable),
                StoredSourceCallableValidation::Valid(edges)
                    if edges.iter().filter(|edge| **edge == type_parameter).count() >= 3
            ));
            assert!(diagnostics.is_empty());
        }
    }

    #[test]
    fn partial_and_poisoned_cold_generic_annotation_links_publish_nothing() {
        let source = "function identity<T>(value: T): T { return value; }";

        let mut symbol_only = QueryFixture::new(source, FileId::new(955));
        let (declaration, type_parameter_declaration, parameter_type, _) =
            symbol_only.generic_parts();
        let owner = symbol_only.bound.symbol(declaration).unwrap();
        let type_parameter_symbol = symbol_only
            .bound
            .symbol(type_parameter_declaration)
            .unwrap();
        assert!(symbol_only.store.set_symbol_node_links(
            parameter_type,
            SymbolNodeLinks {
                resolved_symbol: Some(type_parameter_symbol),
            },
        ));
        let before = publication_state(&symbol_only.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(
            symbol_only
                .query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&symbol_only.store), before);
        assert!(
            symbol_only
                .store
                .source_callable_type_for_owner(owner)
                .is_none()
        );

        let mut type_only = QueryFixture::new(source, FileId::new(956));
        let (declaration, _, parameter_type, return_type) = type_only.generic_parts();
        let owner = type_only.bound.symbol(declaration).unwrap();
        let type_parameter = type_only
            .query_type_node(return_type, &mut diagnostics)
            .unwrap();
        assert!(type_only.store.set_type_node_links(
            parameter_type,
            TypeNodeLinks {
                resolved_type: Some(type_parameter),
                outer_type_parameters: None,
            },
        ));
        let before = publication_state(&type_only.store);
        assert!(
            type_only
                .query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&type_only.store), before);
        assert!(
            type_only
                .store
                .source_callable_type_for_owner(owner)
                .is_none()
        );

        let mut outer_poison = QueryFixture::new(source, FileId::new(957));
        let (declaration, type_parameter_declaration, parameter_type, return_type) =
            outer_poison.generic_parts();
        let owner = outer_poison.bound.symbol(declaration).unwrap();
        let type_parameter_symbol = outer_poison
            .bound
            .symbol(type_parameter_declaration)
            .unwrap();
        let type_parameter = outer_poison
            .query_type_node(return_type, &mut diagnostics)
            .unwrap();
        assert!(outer_poison.store.set_symbol_node_links(
            parameter_type,
            SymbolNodeLinks {
                resolved_symbol: Some(type_parameter_symbol),
            },
        ));
        assert!(outer_poison.store.set_type_node_links(
            parameter_type,
            TypeNodeLinks {
                resolved_type: Some(type_parameter),
                outer_type_parameters: Some(vec![type_parameter]),
            },
        ));
        let before = publication_state(&outer_poison.store);
        assert!(
            outer_poison
                .query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&outer_poison.store), before);
        assert!(
            outer_poison
                .store
                .source_callable_type_for_owner(owner)
                .is_none()
        );

        let mut wrong_pair = QueryFixture::new(source, FileId::new(958));
        let (declaration, _, parameter_type, _) = wrong_pair.generic_parts();
        let owner = wrong_pair.bound.symbol(declaration).unwrap();
        let number = wrong_pair.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(wrong_pair.store.set_symbol_node_links(
            parameter_type,
            SymbolNodeLinks {
                resolved_symbol: Some(owner),
            },
        ));
        assert!(wrong_pair.store.set_type_node_links(
            parameter_type,
            TypeNodeLinks {
                resolved_type: Some(number),
                outer_type_parameters: None,
            },
        ));
        let before = publication_state(&wrong_pair.store);
        assert!(
            wrong_pair
                .query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&wrong_pair.store), before);
        assert!(
            wrong_pair
                .store
                .source_callable_type_for_owner(owner)
                .is_none()
        );
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn unsupported_generic_signature_shapes_publish_nothing() {
        for (index, source) in [
            "function f<T, U>(value: T): T { return value; }",
            "function f<T extends string>(value: T): T { return value; }",
            "function f<T = string>(value: T): T { return value; }",
            "function f<T>(value: T, other: T): T { return value; }",
            "function f<T>(value: T): string { return ''; }",
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(960 + u32::try_from(index).unwrap());
            let (declaration, type_parameter_declaration) =
                function_and_type_parameter(&parsed, file);
            let mut context = bind_context(&parsed, file);
            let (owner, type_parameter_symbol) = {
                let (_, bound) = context.file(file).unwrap();
                (
                    bound.symbol(declaration).unwrap(),
                    bound.symbol(type_parameter_declaration).unwrap(),
                )
            };
            let before = publication_state(context.store());
            assert!(matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Function(SourceFunctionUnsupported::Callable(_))
                ))
            ));
            assert_eq!(publication_state(context.store()), before);
            assert!(
                context
                    .store()
                    .declared_type_links(type_parameter_symbol)
                    .is_none()
            );
            assert!(
                context
                    .store()
                    .source_callable_type_for_owner(owner)
                    .is_none()
            );
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn poisoned_declared_or_signature_type_parameter_fails_without_new_publication() {
        let mut cold = QueryFixture::new(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(971),
        );
        let (declaration, type_parameter_declaration) = cold.declaration_and_type_parameter();
        let owner = cold.bound.symbol(declaration).unwrap();
        let type_parameter_symbol = cold.bound.symbol(type_parameter_declaration).unwrap();
        let forged = cold.store.alloc_type_parameter(None).unwrap();
        assert!(cold.store.set_declared_type_links(
            type_parameter_symbol,
            DeclaredTypeLinks {
                declared_type: Some(forged),
                ..DeclaredTypeLinks::default()
            }
        ));
        let poisoned_cold = publication_state(&cold.store);
        let mut diagnostics = CanonicalCheckerDiagnostics::default();
        assert!(
            cold.query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&cold.store), poisoned_cold);
        assert!(cold.store.source_callable_type_for_owner(owner).is_none());

        let mut warm = QueryFixture::new(
            "function identity<T>(value: T): T { return value; }",
            FileId::new(972),
        );
        let (declaration, _) = warm.declaration_and_type_parameter();
        let owner = warm.bound.symbol(declaration).unwrap();
        let callable = warm
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = warm
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let number = warm.store.intrinsic_bootstrap().unwrap().number_type;
        assert!(
            warm.store
                .set_signature_type_parameters(signature, vec![number])
        );
        assert_eq!(
            validate_stored_source_callable(&warm.store, callable),
            StoredSourceCallableValidation::Malformed
        );
        let poisoned_warm = publication_state(&warm.store);
        assert!(warm.query_return(signature, &mut diagnostics).is_err());
        assert_eq!(publication_state(&warm.store), poisoned_warm);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn poisoned_warm_generic_annotation_links_and_signature_shape_fail_closed() {
        let source = "function identity<T>(value: T): T { return value; }";
        let mut diagnostics = CanonicalCheckerDiagnostics::default();

        let mut parameter_poison = QueryFixture::new(source, FileId::new(973));
        let (declaration, _, parameter_type, _) = parameter_poison.generic_parts();
        let owner = parameter_poison.bound.symbol(declaration).unwrap();
        let callable = parameter_poison
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let number = parameter_poison
            .store
            .intrinsic_bootstrap()
            .unwrap()
            .number_type;
        assert!(parameter_poison.store.set_type_node_links(
            parameter_type,
            TypeNodeLinks {
                resolved_type: Some(number),
                outer_type_parameters: None,
            },
        ));
        let before = publication_state(&parameter_poison.store);
        assert!(
            parameter_poison
                .query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&parameter_poison.store), before);
        assert_eq!(
            parameter_poison.store.source_callable_type_for_owner(owner),
            Some(callable)
        );

        let mut return_poison = QueryFixture::new(source, FileId::new(974));
        let (declaration, _, _, return_type) = return_poison.generic_parts();
        let owner = return_poison.bound.symbol(declaration).unwrap();
        let callable = return_poison
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = return_poison
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        let type_parameter = return_poison
            .query_return(signature, &mut diagnostics)
            .unwrap();
        assert_eq!(
            return_poison
                .store
                .signature(signature)
                .unwrap()
                .resolved_return_type(),
            Some(type_parameter)
        );
        assert!(return_poison.store.set_symbol_node_links(
            return_type,
            SymbolNodeLinks {
                resolved_symbol: Some(owner),
            },
        ));
        assert_eq!(
            validate_stored_source_callable(&return_poison.store, callable),
            StoredSourceCallableValidation::Malformed
        );
        let before = publication_state(&return_poison.store);
        assert!(
            return_poison
                .query_return(signature, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&return_poison.store), before);

        let mut shape_poison = QueryFixture::new(source, FileId::new(975));
        let (declaration, _, _, _) = shape_poison.generic_parts();
        let owner = shape_poison.bound.symbol(declaration).unwrap();
        let callable = shape_poison
            .query_callable(declaration, owner, &mut diagnostics)
            .unwrap();
        let signature = shape_poison
            .store
            .source_callable_provenance(callable)
            .unwrap()
            .signature;
        assert!(
            shape_poison
                .store
                .set_signature_flags(signature, SignatureFlags::HAS_LITERAL_TYPES)
        );
        assert_eq!(
            validate_stored_source_callable(&shape_poison.store, callable),
            StoredSourceCallableValidation::Malformed
        );
        let before = publication_state(&shape_poison.store);
        assert!(
            shape_poison
                .query_callable(declaration, owner, &mut diagnostics)
                .is_err()
        );
        assert_eq!(publication_state(&shape_poison.store), before);
        assert!(diagnostics.is_empty());
    }
}
