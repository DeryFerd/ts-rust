//! Exact source integration for one ordinary identifier or own-property call.
//!
//! This deliberately admits only `identifier(arguments)` or a proven required
//! own-property `identifier.name(arguments)`. Arguments may contain scalar
//! values, identifier and property reads, object literals, nested direct calls,
//! or recursively proven primitive expressions, optionally parenthesized.
//! The semantic kernel remains in `calls`; this module owns the AST proof,
//! lazy-return/relation retries, call caches, and source diagnostics.

use std::collections::HashSet;

use ts_ast::{NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_binder::SymbolFlags;
use ts_core::{TextPos, TextRange};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalCheckerDiagnostic, CanonicalCheckerDiagnosticRange, CanonicalCheckerDiagnostics,
    CanonicalCheckerOptions, CanonicalCheckerRelatedInformation, CanonicalGlobalTypes,
    CanonicalTypeFormatFlags, CanonicalTypeMapperStore, DeclaredTypeHost, RelationUnavailable,
    ResolvedSignatureState, SignatureId, SignatureLinks, TypeId, TypeNodeLinks,
    callable_sets::{StoredCallableSetValidation, validate_stored_callable_set},
    calls::{
        DirectCallApplicability, DirectCallError, DirectCallForm, DirectCallRequest,
        DirectCallUnsupported, resolve_direct_call,
    },
    formatter::get_type_names_for_assignability_error_with_host_global_types_and_flags,
    generic_calls::{
        GenericCallVectorApplicability, GenericCallVectorError, GenericCallVectorRequest,
        GenericCallVectorResolution, GenericCallVectorUnsupported, IdentityGenericCallError,
        IdentityGenericCallRequest, IdentityGenericCallResolution, IdentityGenericCallUnsupported,
        demand_generic_call_vector_return_with_session,
        demand_identity_generic_call_return_with_session, materialize_generic_call_vector_source,
        resolve_generic_call_vector_with_session,
        resolve_source_identity_generic_call_with_session,
        source_declared_inference_candidate_is_exported,
    },
    inference::{NakedTypeCandidateError, NakedTypeInferenceError},
    instantiate::InstantiationSession,
    object_diagnostics::exact_optional_property_mismatch_details,
    source::{
        PlannedExpression, PlannedExpressionKind, SourceCheckError, UnsupportedSourceSyntax,
        logical_binary_operator_text, merge_retry_diagnostic, merge_retry_diagnostics,
        primitive_binary_operator_text,
    },
    source_callables::{StoredSourceCallableValidation, validate_stored_source_callable},
    type_nodes::CanonicalTypeQuery,
    type_records::TypeData,
};

/// Fully proven syntax plus source-planned callee and arguments.
#[derive(Clone, Debug)]
pub(super) struct SourceCallPlan {
    pub(super) node: NodeRef,
    pub(super) callee: PlannedExpression,
    callee_form: SourceCallCalleeForm,
    callee_diagnostic_node: NodeRef,
    type_arguments: Option<SourceTypeArgumentList>,
    pub(super) arguments: Vec<PlannedExpression>,
}

/// The exact callee family proven by call syntax.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SourceCallCalleeForm {
    Identifier,
    RequiredOwnProperty,
}

/// Exact parser-owned type-argument list syntax retained for checker recovery.
///
/// The local parser stores the surrounding angle brackets in `NodeList.range`,
/// while pinned TypeScript-Go stores the list range after `<` and before `>`.
/// `syntax_range` retains the complete bracketed list for grammar TS1099.
/// `diagnostic_range` retains the first type token through the last type token
/// or trailing comma for TS2558, excluding outer trivia and angle brackets. An
/// empty list remains present because call resolution treats it as inference.
#[derive(Clone, Debug)]
struct SourceTypeArgumentList {
    nodes: Vec<NodeRef>,
    syntax_range: TextRange,
    diagnostic_range: Option<TextRange>,
    trailing_comma_range: Option<TextRange>,
}

#[derive(Clone, Debug)]
pub(super) struct DirectSourceCallSyntax {
    node: NodeRef,
    callee: NodeRef,
    callee_form: SourceCallCalleeForm,
    callee_diagnostic_node: NodeRef,
    type_arguments: Option<SourceTypeArgumentList>,
    arguments: Vec<NodeRef>,
}

impl DirectSourceCallSyntax {
    pub(super) fn callee(&self) -> NodeRef {
        self.callee
    }

    pub(super) fn callee_form(&self) -> SourceCallCalleeForm {
        self.callee_form
    }

    pub(super) fn callee_diagnostic_node(&self) -> NodeRef {
        self.callee_diagnostic_node
    }

    pub(super) fn arguments(&self) -> &[NodeRef] {
        &self.arguments
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CheckedSourceCall {
    pub(super) return_type: TypeId,
}

/// Returns the shared parameter context for an object or array argument.
///
/// Generic signatures and overloads with different parameter types require
/// inference or overload selection before they can provide an exact context.
pub(super) fn source_call_argument_contextual_type(
    store: &CanonicalTypeMapperStore,
    global_types: &CanonicalGlobalTypes,
    plan: &SourceCallPlan,
    callee_type: TypeId,
    argument_index: usize,
) -> Result<Option<TypeId>, SourceCheckError> {
    let Some(argument) = plan.arguments.get(argument_index) else {
        return Err(SourceCheckError::Call(plan.node));
    };
    if !matches!(
        argument.unparenthesized().kind,
        PlannedExpressionKind::Object { .. } | PlannedExpressionKind::Array(_)
    ) {
        return Ok(None);
    }

    let StoredCallableSetValidation::Valid { projection, .. } =
        validate_stored_callable_set(store, callee_type)
    else {
        return Ok(None);
    };
    if !projection.construct_signatures.is_empty() || projection.call_signatures.is_empty() {
        return Ok(None);
    }

    let mut contextual_type = None;
    for callable in &projection.call_signatures {
        let Some(signature) = store.signature(callable.signature) else {
            return Err(SourceCheckError::Call(plan.node));
        };
        if !signature.type_parameters().is_empty() {
            return Ok(None);
        }
        let parameter_type = match callable.parameters.get(argument_index).copied() {
            Some(parameter) => Some(parameter),
            None => callable
                .rest_parameter
                .map(|rest| store.canonical_array_element_type(global_types, rest))
                .transpose()?
                .flatten(),
        };
        let Some(parameter_type) = parameter_type else {
            return Ok(None);
        };
        match contextual_type {
            None => contextual_type = Some(parameter_type),
            Some(existing) if existing == parameter_type => {}
            Some(_) => return Ok(None),
        }
    }
    Ok(contextual_type)
}

/// Proves the complete direct-call syntax and rejects poisoned cold/warm cache
/// shapes before source execution publishes value state.
pub(super) fn plan_direct_source_call_syntax(
    arena: &NodeArena,
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<DirectSourceCallSyntax, SourceCheckError> {
    let Some(record) = arena.get(node.node) else {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(node),
        ));
    };
    let NodeData::CallExpression(call) = &record.data else {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(node),
        ));
    };
    if record.kind != SyntaxKind::CallExpression
        || record.flags.0 != 0
        || call.question_dot_token.is_some()
        || call.symbol.is_some()
        || call.facts != 0
    {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(node),
        ));
    }

    let callee = NodeRef::new(node.arena, node.file, call.expression);
    let Some(callee_record) = arena.get(call.expression) else {
        return Err(SourceCheckError::Call(node));
    };
    if callee_record.parent != Some(node.node) {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(node),
        ));
    }
    let (callee_form, callee_diagnostic_node) = match (callee_record.kind, &callee_record.data) {
        (SyntaxKind::Identifier, NodeData::Identifier(_)) => {
            (SourceCallCalleeForm::Identifier, callee)
        }
        (SyntaxKind::PropertyAccessExpression, NodeData::PropertyAccessExpression(property)) => {
            let name = NodeRef::new(node.arena, node.file, property.name);
            let Some(name_record) = arena.get(property.name) else {
                return Err(SourceCheckError::Call(node));
            };
            if name_record.parent != Some(callee.node)
                || name_record.kind != SyntaxKind::Identifier
                || !matches!(&name_record.data, NodeData::Identifier(_))
                || call.type_arguments.is_some()
            {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Call(node),
                ));
            }
            (SourceCallCalleeForm::RequiredOwnProperty, name)
        }
        _ => {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Call(node),
            ));
        }
    };

    let type_arguments = call
        .type_arguments
        .as_ref()
        .map(|type_arguments| {
            let start = type_arguments.range.start.get();
            let end = type_arguments.range.end.get();
            if type_arguments.range.start < record.range.start
                || type_arguments.range.end > record.range.end
                || end < start.saturating_add(2)
                || arena.source_text().is_some_and(|source| {
                    let start = usize::try_from(start).ok();
                    let close = usize::try_from(end.saturating_sub(1)).ok();
                    start.is_none_or(|start| source.as_bytes().get(start) != Some(&b'<'))
                        || close.is_none_or(|close| source.as_bytes().get(close) != Some(&b'>'))
                })
            {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Call(node),
                ));
            }
            let nodes = type_arguments
                .nodes
                .iter()
                .map(|type_argument| {
                    let type_argument = NodeRef::new(node.arena, node.file, *type_argument);
                    let Some(type_argument_record) = arena.get(type_argument.node) else {
                        return Err(SourceCheckError::Call(node));
                    };
                    if type_argument_record.parent != Some(node.node)
                        || type_argument_record.range.start < type_arguments.range.start
                        || type_argument_record.range.end > type_arguments.range.end
                    {
                        return Err(SourceCheckError::Unsupported(
                            UnsupportedSourceSyntax::Call(node),
                        ));
                    }
                    Ok(type_argument)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let mut trailing_comma_range = None;
            let diagnostic_range = if let (Some(first), Some(last)) = (nodes.first(), nodes.last())
            {
                let first_range = arena
                    .get(first.node)
                    .ok_or(SourceCheckError::Call(node))?
                    .range;
                let last_range = arena
                    .get(last.node)
                    .ok_or(SourceCheckError::Call(node))?
                    .range;
                if first_range.start < TextPos::new(start.saturating_add(1))
                    || last_range.end > TextPos::new(end.saturating_sub(1))
                {
                    return Err(SourceCheckError::Unsupported(
                        UnsupportedSourceSyntax::Call(node),
                    ));
                }
                let diagnostic_end = if type_arguments.has_trailing_comma {
                    trailing_comma_range = arena.source_text().and_then(|source| {
                        trailing_type_argument_comma_range(
                            source,
                            last_range.end,
                            TextPos::new(end.saturating_sub(1)),
                        )
                    });
                    trailing_comma_range.map(|range| range.end)
                } else {
                    Some(last_range.end)
                };
                diagnostic_end
                    .map(|diagnostic_end| TextRange::new(first_range.start, diagnostic_end))
            } else {
                None
            };
            if type_arguments.has_trailing_comma && trailing_comma_range.is_none() {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Call(node),
                ));
            }
            Ok(SourceTypeArgumentList {
                nodes,
                syntax_range: type_arguments.range,
                diagnostic_range,
                trailing_comma_range,
            })
        })
        .transpose()?;

    let mut arguments = Vec::with_capacity(call.arguments.nodes.len());
    for argument_id in &call.arguments.nodes {
        let argument = NodeRef::new(node.arena, node.file, *argument_id);
        let Some(argument_record) = arena.get(*argument_id) else {
            return Err(SourceCheckError::Call(node));
        };
        if argument_record.parent != Some(node.node)
            || !is_supported_call_argument_syntax(arena, argument)
        {
            return Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Call(node),
            ));
        }
        arguments.push(argument);
    }
    preflight_call_links(store, node)?;
    Ok(DirectSourceCallSyntax {
        node,
        callee,
        callee_form,
        callee_diagnostic_node,
        type_arguments,
        arguments,
    })
}

fn trailing_type_argument_comma_range(
    source: &str,
    start: TextPos,
    closing_bracket: TextPos,
) -> Option<TextRange> {
    let start = usize::try_from(start.get()).ok()?;
    let closing_bracket = usize::try_from(closing_bracket.get()).ok()?;
    let before_close = source.get(start..closing_bracket)?;
    let comma = skip_call_type_argument_trivia(before_close)?;
    if before_close.as_bytes().get(comma) != Some(&b',') {
        return None;
    }
    Some(TextRange::new(
        TextPos::new(u32::try_from(start + comma).ok()?),
        TextPos::new(u32::try_from(start + comma + 1).ok()?),
    ))
}

fn skip_call_type_argument_trivia(text: &str) -> Option<usize> {
    let mut offset = 0;
    loop {
        let remaining = text.get(offset..)?;
        if remaining.starts_with("//") {
            offset += remaining.find(['\r', '\n']).unwrap_or(remaining.len());
            continue;
        }
        if remaining.starts_with("/*") {
            offset += remaining.find("*/")?.checked_add(2)?;
            continue;
        }
        let Some(character) = remaining.chars().next() else {
            return Some(offset);
        };
        if character.is_whitespace() || character == '\u{feff}' {
            offset = offset.checked_add(character.len_utf8())?;
            continue;
        }
        return Some(offset);
    }
}

pub(super) fn finish_direct_source_call_plan(
    syntax: &DirectSourceCallSyntax,
    callee: PlannedExpression,
    arguments: Vec<PlannedExpression>,
) -> Result<SourceCallPlan, SourceCheckError> {
    let exact_callee = match (&callee.kind, syntax.callee_form) {
        (PlannedExpressionKind::Identifier(_), SourceCallCalleeForm::Identifier) => true,
        (PlannedExpressionKind::Property(property), SourceCallCalleeForm::RequiredOwnProperty) => {
            property.is_call_callee_for(syntax.node, syntax.callee_diagnostic_node)
        }
        _ => false,
    };
    if callee.node != syntax.callee
        || !exact_callee
        || arguments.len() != syntax.arguments.len()
        || !arguments
            .iter()
            .zip(&syntax.arguments)
            .all(|(argument, syntax_node)| {
                argument.node == *syntax_node && is_supported_call_argument_plan(argument)
            })
    {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(syntax.node),
        ));
    }
    Ok(SourceCallPlan {
        node: syntax.node,
        callee,
        callee_form: syntax.callee_form,
        callee_diagnostic_node: syntax.callee_diagnostic_node,
        type_arguments: syntax.type_arguments.clone(),
        arguments,
    })
}

fn is_supported_call_argument_syntax(arena: &NodeArena, node: NodeRef) -> bool {
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    match record.kind {
        SyntaxKind::Identifier
        | SyntaxKind::NullKeyword
        | SyntaxKind::TrueKeyword
        | SyntaxKind::FalseKeyword
        | SyntaxKind::StringLiteral
        | SyntaxKind::NoSubstitutionTemplateLiteral
        | SyntaxKind::NumericLiteral
        | SyntaxKind::BigIntLiteral => true,
        SyntaxKind::ParenthesizedExpression => {
            let NodeData::ParenthesizedExpression(parenthesized) = &record.data else {
                return false;
            };
            let inner = NodeRef::new(node.arena, node.file, parenthesized.expression);
            arena
                .get(parenthesized.expression)
                .is_some_and(|inner_record| {
                    inner_record.parent == Some(node.node)
                        && is_supported_call_argument_syntax(arena, inner)
                })
        }
        SyntaxKind::PrefixUnaryExpression => {
            let NodeData::PrefixUnaryExpression(prefix) = &record.data else {
                return false;
            };
            arena.get(prefix.operand).is_some_and(|operand| {
                operand.parent == Some(node.node)
                    && matches!(
                        operand.kind,
                        SyntaxKind::NumericLiteral | SyntaxKind::BigIntLiteral
                    )
            })
        }
        SyntaxKind::PropertyAccessExpression => {
            let NodeData::PropertyAccessExpression(access) = &record.data else {
                return false;
            };
            if record.flags.0 != 0
                || access.flow_node.is_some()
                || access.question_dot_token.is_some()
                || access.facts != 0
            {
                return false;
            }
            let Some(receiver) = arena.get(access.expression) else {
                return false;
            };
            let Some(name) = arena.get(access.name) else {
                return false;
            };
            receiver.parent == Some(node.node)
                && receiver.kind == SyntaxKind::Identifier
                && receiver.flags.0 == 0
                && matches!(
                    &receiver.data,
                    NodeData::Identifier(identifier) if identifier.flow_node.is_none()
                )
                && name.parent == Some(node.node)
                && name.kind == SyntaxKind::Identifier
                && name.flags.0 == 0
                && matches!(
                    &name.data,
                    NodeData::Identifier(identifier)
                        if identifier.flow_node.is_none() && !identifier.text.is_empty()
                )
        }
        SyntaxKind::ElementAccessExpression => is_context_insensitive_element_syntax(arena, node),
        SyntaxKind::CallExpression => matches!(&record.data, NodeData::CallExpression(_)),
        SyntaxKind::ObjectLiteralExpression => {
            matches!(&record.data, NodeData::ObjectLiteralExpression(_))
        }
        SyntaxKind::BinaryExpression => {
            is_context_insensitive_primitive_binary_syntax(arena, node)
                || is_context_insensitive_logical_binary_syntax(arena, node)
        }
        _ => false,
    }
}

fn is_context_insensitive_element_syntax(arena: &NodeArena, node: NodeRef) -> bool {
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    let NodeData::ElementAccessExpression(access) = &record.data else {
        return false;
    };
    if record.kind != SyntaxKind::ElementAccessExpression
        || record.flags.0 != 0
        || access.flow_node.is_some()
        || access.question_dot_token.is_some()
        || access.facts != 0
    {
        return false;
    }
    let Some(receiver) = arena.get(access.expression) else {
        return false;
    };
    let Some(index) = arena.get(access.argument_expression) else {
        return false;
    };
    receiver.parent == Some(node.node)
        && receiver.kind == SyntaxKind::Identifier
        && receiver.flags.0 == 0
        && matches!(
            &receiver.data,
            NodeData::Identifier(identifier) if identifier.flow_node.is_none()
        )
        && index.parent == Some(node.node)
        && receiver.range.end <= index.range.start
        && is_context_insensitive_element_index_syntax(arena, access.argument_expression)
}

fn is_context_insensitive_element_index_syntax(arena: &NodeArena, node: ts_ast::NodeId) -> bool {
    let Some(record) = arena.get(node) else {
        return false;
    };
    match record.kind {
        SyntaxKind::Identifier => {
            record.flags.0 == 0
                && matches!(
                    &record.data,
                    NodeData::Identifier(identifier) if identifier.flow_node.is_none()
                )
        }
        SyntaxKind::NullKeyword
        | SyntaxKind::TrueKeyword
        | SyntaxKind::FalseKeyword
        | SyntaxKind::StringLiteral
        | SyntaxKind::NoSubstitutionTemplateLiteral
        | SyntaxKind::NumericLiteral
        | SyntaxKind::BigIntLiteral => true,
        SyntaxKind::PrefixUnaryExpression => {
            let NodeData::PrefixUnaryExpression(prefix) = &record.data else {
                return false;
            };
            arena.get(prefix.operand).is_some_and(|operand| {
                operand.parent == Some(node)
                    && matches!(
                        operand.kind,
                        SyntaxKind::NumericLiteral | SyntaxKind::BigIntLiteral
                    )
            })
        }
        _ => false,
    }
}

fn is_context_insensitive_logical_binary_syntax(arena: &NodeArena, node: NodeRef) -> bool {
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    let NodeData::BinaryExpression(binary) = &record.data else {
        return false;
    };
    if record.kind != SyntaxKind::BinaryExpression
        || record.flags.0 != 0
        || binary.symbol.is_some()
        || binary.type_.is_some()
        || binary.facts != 0
        || binary.modifiers.is_some()
    {
        return false;
    }
    let Some(left) = arena.get(binary.left) else {
        return false;
    };
    let Some(operator) = arena.get(binary.operator_token) else {
        return false;
    };
    let Some(right) = arena.get(binary.right) else {
        return false;
    };
    left.parent == Some(node.node)
        && operator.parent == Some(node.node)
        && right.parent == Some(node.node)
        && left.range.end <= operator.range.start
        && operator.range.end <= right.range.start
        && operator.flags.0 == 0
        && matches!(operator.data, NodeData::Token(_))
        && logical_binary_operator_text(operator.kind).is_some()
        && is_supported_call_argument_syntax(
            arena,
            NodeRef::new(node.arena, node.file, binary.left),
        )
        && is_supported_call_argument_syntax(
            arena,
            NodeRef::new(node.arena, node.file, binary.right),
        )
}

fn is_context_insensitive_primitive_binary_syntax(arena: &NodeArena, node: NodeRef) -> bool {
    // This is the call owner's context-sensitivity proof. Source planning still
    // performs the exact operator-spelling, cache, and operand capability proof.
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    let NodeData::BinaryExpression(binary) = &record.data else {
        return false;
    };
    if record.kind != SyntaxKind::BinaryExpression
        || record.flags.0 != 0
        || binary.symbol.is_some()
        || binary.type_.is_some()
        || binary.facts != 0
        || binary.modifiers.is_some()
    {
        return false;
    }
    let Some(left) = arena.get(binary.left) else {
        return false;
    };
    let Some(operator) = arena.get(binary.operator_token) else {
        return false;
    };
    let Some(right) = arena.get(binary.right) else {
        return false;
    };
    left.parent == Some(node.node)
        && operator.parent == Some(node.node)
        && right.parent == Some(node.node)
        && left.range.end <= operator.range.start
        && operator.range.end <= right.range.start
        && operator.flags.0 == 0
        && matches!(operator.data, NodeData::Token(_))
        && primitive_binary_operator_text(operator.kind).is_some()
        && is_context_insensitive_primitive_binary_operand_syntax(
            arena,
            NodeRef::new(node.arena, node.file, binary.left),
        )
        && is_context_insensitive_primitive_binary_operand_syntax(
            arena,
            NodeRef::new(node.arena, node.file, binary.right),
        )
}

fn is_context_insensitive_primitive_binary_operand_syntax(
    arena: &NodeArena,
    node: NodeRef,
) -> bool {
    let Some(record) = arena.get(node.node) else {
        return false;
    };
    match record.kind {
        SyntaxKind::Identifier
        | SyntaxKind::TrueKeyword
        | SyntaxKind::FalseKeyword
        | SyntaxKind::StringLiteral
        | SyntaxKind::NoSubstitutionTemplateLiteral
        | SyntaxKind::NumericLiteral
        | SyntaxKind::BigIntLiteral => true,
        SyntaxKind::ParenthesizedExpression => {
            let NodeData::ParenthesizedExpression(parenthesized) = &record.data else {
                return false;
            };
            let inner = NodeRef::new(node.arena, node.file, parenthesized.expression);
            arena
                .get(parenthesized.expression)
                .is_some_and(|inner_record| {
                    inner_record.parent == Some(node.node)
                        && is_context_insensitive_primitive_binary_operand_syntax(arena, inner)
                })
        }
        SyntaxKind::PrefixUnaryExpression => {
            let NodeData::PrefixUnaryExpression(prefix) = &record.data else {
                return false;
            };
            arena.get(prefix.operand).is_some_and(|operand| {
                operand.parent == Some(node.node)
                    && matches!(
                        operand.kind,
                        SyntaxKind::NumericLiteral | SyntaxKind::BigIntLiteral
                    )
            })
        }
        SyntaxKind::ElementAccessExpression => is_context_insensitive_element_syntax(arena, node),
        SyntaxKind::BinaryExpression => is_context_insensitive_primitive_binary_syntax(arena, node),
        _ => false,
    }
}

fn is_supported_call_argument_plan(expression: &PlannedExpression) -> bool {
    match &expression.kind {
        PlannedExpressionKind::Null
        | PlannedExpressionKind::String(_)
        | PlannedExpressionKind::Number { .. }
        | PlannedExpressionKind::BigInt { .. }
        | PlannedExpressionKind::Boolean(_)
        | PlannedExpressionKind::GlobalUndefined
        | PlannedExpressionKind::Identifier(_)
        | PlannedExpressionKind::Property(_)
        | PlannedExpressionKind::Element(_) => true,
        PlannedExpressionKind::Call(call) => {
            call.node == expression.node
                && call.arguments.iter().all(is_supported_call_argument_plan)
        }
        PlannedExpressionKind::Object { properties, .. } => {
            properties.iter().all(is_supported_call_argument_plan)
        }
        PlannedExpressionKind::Parenthesized(inner) => is_supported_call_argument_plan(inner),
        PlannedExpressionKind::Binary(binary) => {
            let (left, right) = binary.operands();
            binary.node() == expression.node
                && primitive_binary_operator_text(binary.operator()).is_some()
                && is_context_insensitive_primitive_binary_operand_plan(left)
                && is_context_insensitive_primitive_binary_operand_plan(right)
        }
        PlannedExpressionKind::Logical(binary) => {
            let (left, right) = binary.operands();
            binary.node() == expression.node
                && logical_binary_operator_text(binary.operator()).is_some()
                && is_supported_call_argument_plan(left)
                && is_supported_call_argument_plan(right)
        }
        PlannedExpressionKind::Assertion { .. }
        | PlannedExpressionKind::TypeImportValueUse(_)
        | PlannedExpressionKind::Array(_)
        | PlannedExpressionKind::New(_)
        | PlannedExpressionKind::Conditional(_) => false,
    }
}

fn is_context_insensitive_primitive_binary_operand_plan(expression: &PlannedExpression) -> bool {
    match &expression.kind {
        PlannedExpressionKind::String(_)
        | PlannedExpressionKind::Number { .. }
        | PlannedExpressionKind::BigInt { .. }
        | PlannedExpressionKind::Boolean(_)
        | PlannedExpressionKind::Identifier(_)
        | PlannedExpressionKind::Element(_) => true,
        PlannedExpressionKind::Parenthesized(inner) => {
            is_context_insensitive_primitive_binary_operand_plan(inner)
        }
        PlannedExpressionKind::Binary(binary) => {
            let (left, right) = binary.operands();
            binary.node() == expression.node
                && primitive_binary_operator_text(binary.operator()).is_some()
                && is_context_insensitive_primitive_binary_operand_plan(left)
                && is_context_insensitive_primitive_binary_operand_plan(right)
        }
        PlannedExpressionKind::Logical(binary) => {
            let (left, right) = binary.operands();
            binary.node() == expression.node
                && logical_binary_operator_text(binary.operator()).is_some()
                && is_context_insensitive_primitive_binary_operand_plan(left)
                && is_context_insensitive_primitive_binary_operand_plan(right)
        }
        PlannedExpressionKind::Null
        | PlannedExpressionKind::GlobalUndefined
        | PlannedExpressionKind::TypeImportValueUse(_)
        | PlannedExpressionKind::Assertion { .. }
        | PlannedExpressionKind::Array(_)
        | PlannedExpressionKind::Object { .. }
        | PlannedExpressionKind::Property(_)
        | PlannedExpressionKind::Call(_)
        | PlannedExpressionKind::New(_)
        | PlannedExpressionKind::Conditional(_) => false,
    }
}

fn preflight_call_links(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<(), SourceCheckError> {
    let mut resolved_type = None;
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
            return Err(SourceCheckError::Call(node));
        }
        resolved_type = links.resolved_type;
    }
    let mut resolved_signature = None;
    if let Some(links) = store.signature_links(node) {
        let expected = SignatureLinks {
            resolved_signature: links.resolved_signature,
            ..SignatureLinks::default()
        };
        if links != &expected
            || match links.resolved_signature {
                ResolvedSignatureState::Unresolved => false,
                ResolvedSignatureState::Resolving => true,
                ResolvedSignatureState::Resolved(signature) => store.signature(signature).is_none(),
            }
        {
            return Err(SourceCheckError::Call(node));
        }
        resolved_signature = links.resolved_signature.signature();
    }
    if resolved_type.is_some() != resolved_signature.is_some() {
        return Err(SourceCheckError::Call(node));
    }
    if let (Some(resolved_type), Some(resolved_signature)) = (resolved_type, resolved_signature)
        && store
            .signature(resolved_signature)
            .and_then(super::signatures::Signature::resolved_return_type)
            != Some(resolved_type)
    {
        return Err(SourceCheckError::Call(node));
    }
    Ok(())
}

/// Resolves one already-typed source call, retrying the two lazy semantic
/// boundaries before publishing its exact signature/return caches.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ResolvedLegacySourceCall {
    signature: SignatureId,
    return_type: TypeId,
    minimum_argument_count: usize,
    maximum_argument_count: usize,
    has_effective_rest: bool,
    applicability: DirectCallApplicability,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ResolvedSourceCall {
    Legacy(ResolvedLegacySourceCall),
    Vector(GenericCallVectorResolution),
    Identity(IdentityGenericCallResolution),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceCallResolutionError {
    Retry(SignatureId),
    Relation(RelationUnavailable),
    Unsupported,
    Invariant,
}

#[derive(Clone, Copy, Debug)]
struct SourceCallResolutionRequest<'a> {
    callee_form: SourceCallCalleeForm,
    callee_type: TypeId,
    argument_types: &'a [TypeId],
    explicit_type_arguments: Option<&'a [TypeId]>,
}

fn resolve_source_call_once(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    existing_call_signature: Option<SignatureId>,
    session: &mut InstantiationSession,
    request: SourceCallResolutionRequest<'_>,
) -> Result<ResolvedSourceCall, SourceCallResolutionError> {
    let SourceCallResolutionRequest {
        callee_form,
        callee_type,
        argument_types,
        explicit_type_arguments,
    } = request;
    if callee_form == SourceCallCalleeForm::RequiredOwnProperty && explicit_type_arguments.is_some()
    {
        return Err(SourceCallResolutionError::Unsupported);
    }
    if explicit_type_arguments.is_none() {
        let request = DirectCallRequest {
            form: DirectCallForm::Call,
            optional_chain: false,
            type_argument_count: 0,
            has_spread_argument: false,
            callee: callee_type,
            arguments: argument_types,
        };
        match resolve_direct_call(store, global_types, options.strict_function_types, request) {
            Ok(resolution) => {
                return Ok(ResolvedSourceCall::Legacy(ResolvedLegacySourceCall {
                    signature: resolution.projection.signature,
                    return_type: resolution.projection.return_type,
                    minimum_argument_count: resolution.projection.minimum_argument_count,
                    maximum_argument_count: resolution.projection.maximum_argument_count,
                    has_effective_rest: resolution.projection.has_effective_rest,
                    applicability: resolution.applicability,
                }));
            }
            Err(DirectCallError::Unsupported(DirectCallUnsupported::GenericSignature(_)))
                if callee_form == SourceCallCalleeForm::Identifier => {}
            Err(DirectCallError::Unsupported(DirectCallUnsupported::GenericSignature(_))) => {
                return Err(SourceCallResolutionError::Unsupported);
            }
            Err(
                DirectCallError::Unsupported(DirectCallUnsupported::UnresolvedReturnType(
                    signature,
                ))
                | DirectCallError::Relation(RelationUnavailable::UnresolvedSignatureReturn(
                    signature,
                )),
            ) => return Err(SourceCallResolutionError::Retry(signature)),
            Err(DirectCallError::Relation(error)) => {
                return Err(SourceCallResolutionError::Relation(error));
            }
            Err(DirectCallError::Unsupported(_)) => {
                return Err(SourceCallResolutionError::Unsupported);
            }
            Err(DirectCallError::Invariant(_)) => return Err(SourceCallResolutionError::Invariant),
        }
    }

    match validate_stored_source_callable(store, callee_type) {
        StoredSourceCallableValidation::Valid(_) => {}
        StoredSourceCallableValidation::NotSourceCallable
        | StoredSourceCallableValidation::Pending => {
            return Err(SourceCallResolutionError::Unsupported);
        }
        StoredSourceCallableValidation::Malformed => {
            return Err(SourceCallResolutionError::Invariant);
        }
    }
    let vector_request = GenericCallVectorRequest {
        form: DirectCallForm::Call,
        optional_chain: false,
        explicit_type_arguments,
        has_spread_argument: false,
        callee: callee_type,
        arguments: argument_types,
    };
    match resolve_generic_call_vector_with_session(
        store,
        global_types,
        options.strict_function_types,
        vector_request,
        existing_call_signature,
        session,
    ) {
        Ok(resolution) => return Ok(ResolvedSourceCall::Vector(resolution)),
        Err(
            GenericCallVectorError::Unsupported(
                GenericCallVectorUnsupported::UnresolvedReturnType(signature),
            )
            | GenericCallVectorError::Relation(RelationUnavailable::UnresolvedSignatureReturn(
                signature,
            )),
        ) => return Err(SourceCallResolutionError::Retry(signature)),
        Err(
            GenericCallVectorError::Relation(error)
            | GenericCallVectorError::Inference(NakedTypeCandidateError::Relation(error)),
        ) => {
            return Err(SourceCallResolutionError::Relation(error));
        }
        Err(error)
            if source_identity_fallback_is_exact(
                store,
                explicit_type_arguments,
                argument_types,
                &error,
            ) => {}
        Err(GenericCallVectorError::Invariant(_)) => {
            return Err(SourceCallResolutionError::Invariant);
        }
        Err(
            GenericCallVectorError::Unsupported(_)
            | GenericCallVectorError::Inference(_)
            | GenericCallVectorError::Instantiation(_),
        ) => return Err(SourceCallResolutionError::Unsupported),
    }

    let request = IdentityGenericCallRequest {
        form: DirectCallForm::Call,
        optional_chain: false,
        explicit_type_arguments,
        has_spread_argument: false,
        callee: callee_type,
        arguments: argument_types,
    };
    match resolve_source_identity_generic_call_with_session(
        store,
        host,
        global_types,
        options.strict_function_types,
        request,
        existing_call_signature,
        session,
    ) {
        Ok(resolution) => Ok(ResolvedSourceCall::Identity(resolution)),
        Err(
            IdentityGenericCallError::Unsupported(
                IdentityGenericCallUnsupported::UnresolvedReturnType(signature),
            )
            | IdentityGenericCallError::Relation(RelationUnavailable::UnresolvedSignatureReturn(
                signature,
            )),
        ) => Err(SourceCallResolutionError::Retry(signature)),
        Err(IdentityGenericCallError::Relation(error)) => {
            Err(SourceCallResolutionError::Relation(error))
        }
        Err(
            IdentityGenericCallError::Unsupported(_)
            | IdentityGenericCallError::Inference(_)
            | IdentityGenericCallError::Instantiation(_),
        ) => Err(SourceCallResolutionError::Unsupported),
        Err(IdentityGenericCallError::Invariant(_)) => Err(SourceCallResolutionError::Invariant),
    }
}

fn source_identity_fallback_is_exact(
    store: &CanonicalTypeMapperStore,
    explicit_type_arguments: Option<&[TypeId]>,
    argument_types: &[TypeId],
    error: &GenericCallVectorError,
) -> bool {
    let [argument] = argument_types else {
        return false;
    };
    explicit_type_arguments.is_none()
        && matches!(
            error,
            GenericCallVectorError::Inference(NakedTypeCandidateError::Candidate(
                NakedTypeInferenceError::UnsupportedCandidate(candidate),
            )) if candidate == argument
        )
        && source_declared_inference_candidate_is_exported(store, *argument)
}

#[allow(clippy::too_many_arguments)]
fn resolve_explicit_source_type_arguments(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    type_arguments: Option<&[NodeRef]>,
) -> Result<Option<Vec<TypeId>>, SourceCheckError> {
    let Some(type_arguments) = type_arguments else {
        return Ok(None);
    };
    if type_arguments.is_empty() {
        return Ok(None);
    }
    let mut type_argument_diagnostics = CanonicalCheckerDiagnostics::default();
    let result = (|| {
        let mut query = CanonicalTypeQuery::new_with_global_types_and_session(
            store,
            host,
            global_types,
            options,
            session,
            &mut type_argument_diagnostics,
        )?;
        type_arguments
            .iter()
            .map(|type_argument| query.get_type_from_type_node(*type_argument))
            .collect::<Result<Vec<_>, _>>()
    })();
    merge_retry_diagnostics(diagnostics, type_argument_diagnostics);
    Ok(Some(result?))
}

pub(super) fn emit_call_type_argument_grammar_diagnostics(
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &SourceCallPlan,
) -> Result<(), SourceCheckError> {
    let Some(type_arguments) = &plan.type_arguments else {
        return Ok(());
    };
    if let Some(range) = type_arguments.trailing_comma_range {
        merge_retry_diagnostic(
            diagnostics,
            CanonicalCheckerDiagnostic {
                node: Some(plan.node),
                range_override: Some(CanonicalCheckerDiagnosticRange::new(plan.node, range)),
                diagnostic: Diagnostic::new(
                    message_by_code(1009).ok_or(SourceCheckError::MissingDiagnostic(1009))?,
                ),
                related_information: Vec::new(),
            },
        );
        return Ok(());
    }
    if type_arguments.nodes.is_empty() {
        merge_retry_diagnostic(
            diagnostics,
            CanonicalCheckerDiagnostic {
                node: Some(plan.node),
                range_override: Some(CanonicalCheckerDiagnosticRange::new(
                    plan.node,
                    type_arguments.syntax_range,
                )),
                diagnostic: Diagnostic::new(
                    message_by_code(1099).ok_or(SourceCheckError::MissingDiagnostic(1099))?,
                ),
                related_information: Vec::new(),
            },
        );
    }
    Ok(())
}

fn extra_argument_diagnostic_range(
    host: &DeclaredTypeHost<'_>,
    plan: &SourceCallPlan,
    first_extra: usize,
) -> Result<CanonicalCheckerDiagnosticRange, SourceCheckError> {
    let first = plan
        .arguments
        .get(first_extra)
        .ok_or(SourceCheckError::Call(plan.node))?;
    let last = plan
        .arguments
        .last()
        .ok_or(SourceCheckError::Call(plan.node))?;
    let first_range = host
        .node(first.node)
        .ok_or(SourceCheckError::Call(plan.node))?
        .range;
    let last_range = host
        .node(last.node)
        .ok_or(SourceCheckError::Call(plan.node))?
        .range;
    Ok(CanonicalCheckerDiagnosticRange::new(
        plan.node,
        TextRange::new(first_range.start, last_range.end),
    ))
}

fn missing_argument_related_information(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    call: NodeRef,
    signature: SignatureId,
    actual: usize,
) -> Result<CanonicalCheckerRelatedInformation, SourceCheckError> {
    let parameter = *store
        .signature(signature)
        .and_then(|signature| signature.parameters().get(actual))
        .ok_or(SourceCheckError::Call(call))?;
    let symbol = store
        .symbol(parameter)
        .ok_or(SourceCheckError::Call(call))?;
    let declaration = *symbol
        .declarations()
        .and_then(|declarations| declarations.first())
        .ok_or(SourceCheckError::Call(call))?;
    if host.node(declaration).is_none() {
        return Err(SourceCheckError::Call(call));
    }
    let name = symbol
        .name()
        .as_utf8()
        .ok_or(SourceCheckError::Call(call))?
        .to_owned();
    Ok(CanonicalCheckerRelatedInformation {
        node: Some(declaration),
        diagnostic: Diagnostic::with_arguments(
            message_by_code(6210).ok_or(SourceCheckError::MissingDiagnostic(6210))?,
            [name],
        ),
    })
}

fn source_call_display_flags(options: CanonicalCheckerOptions) -> CanonicalTypeFormatFlags {
    let mut flags = CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
    if options.no_error_truncation {
        flags |= CanonicalTypeFormatFlags::NO_TRUNCATION;
    }
    flags
}

fn expected_count_text(minimum: usize, maximum: usize) -> String {
    if minimum == maximum {
        minimum.to_string()
    } else {
        format!("{minimum}-{maximum}")
    }
}

fn exact_optional_argument_mismatch(
    store: &CanonicalTypeMapperStore,
    options: CanonicalCheckerOptions,
    source: TypeId,
    target: TypeId,
) -> bool {
    if !options.intrinsic.exact_optional_property_types {
        return false;
    }
    let Some(undefined) = store
        .intrinsic_bootstrap()
        .map(|bootstrap| bootstrap.undefined_type)
    else {
        return false;
    };
    let Some(source_members) = store
        .type_payload(source)
        .and_then(|record| record.data().structured())
        .and_then(|structured| structured.members)
        .and_then(|members| store.symbol_table(members))
    else {
        return false;
    };
    let Some(target_properties) = store
        .type_payload(target)
        .and_then(|record| record.data().structured())
        .and_then(|structured| structured.properties.as_deref())
    else {
        return false;
    };
    target_properties.iter().any(|property| {
        let Some(target_property) = store.symbol(*property) else {
            return false;
        };
        if !target_property.flags().contains(SymbolFlags::OPTIONAL) {
            return false;
        }
        let Some(source_property) = source_members.get(target_property.name()) else {
            return false;
        };
        let Some(source_type) = store
            .value_symbol_links(source_property)
            .and_then(|links| links.resolved_type)
        else {
            return false;
        };
        let Some(target_type) = store
            .value_symbol_links(*property)
            .and_then(|links| links.resolved_type)
        else {
            return false;
        };
        type_contains_undefined(store, source_type, undefined)
            && !type_contains_undefined(store, target_type, undefined)
    })
}

fn type_contains_undefined(
    store: &CanonicalTypeMapperStore,
    type_: TypeId,
    undefined: TypeId,
) -> bool {
    type_ == undefined
        || store.type_payload(type_).is_some_and(|record| {
            matches!(record.data(), TypeData::Union(union) if union.union.types.contains(&undefined))
        })
}

#[allow(clippy::too_many_arguments)]
fn prepare_legacy_source_call_diagnostic(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceCallPlan,
    argument_types: &[TypeId],
    resolution: ResolvedLegacySourceCall,
) -> Result<Option<CanonicalCheckerDiagnostic>, SourceCheckError> {
    let diagnostic = match resolution.applicability {
        DirectCallApplicability::Applicable => return Ok(None),
        DirectCallApplicability::TooFewArguments {
            expected_at_least,
            actual,
        } => {
            if expected_at_least != resolution.minimum_argument_count
                || actual != plan.arguments.len()
                || actual != argument_types.len()
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            let (message, expected) = if resolution.has_effective_rest {
                (
                    message_by_code(2555).ok_or(SourceCheckError::MissingDiagnostic(2555))?,
                    resolution.minimum_argument_count.to_string(),
                )
            } else {
                (
                    message_by_code(2554).ok_or(SourceCheckError::MissingDiagnostic(2554))?,
                    expected_count_text(
                        resolution.minimum_argument_count,
                        resolution.maximum_argument_count,
                    ),
                )
            };
            CanonicalCheckerDiagnostic {
                node: Some(plan.callee_diagnostic_node),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(message, [expected, actual.to_string()]),
                related_information: vec![missing_argument_related_information(
                    store,
                    host,
                    plan.node,
                    resolution.signature,
                    actual,
                )?],
            }
        }
        DirectCallApplicability::TooManyArguments {
            expected_at_most,
            actual,
        } => {
            if resolution.has_effective_rest
                || expected_at_most != resolution.maximum_argument_count
                || actual != plan.arguments.len()
                || actual != argument_types.len()
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            CanonicalCheckerDiagnostic {
                node: Some(plan.node),
                range_override: Some(extra_argument_diagnostic_range(
                    host,
                    plan,
                    expected_at_most,
                )?),
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(2554).ok_or(SourceCheckError::MissingDiagnostic(2554))?,
                    [
                        expected_count_text(
                            resolution.minimum_argument_count,
                            resolution.maximum_argument_count,
                        ),
                        actual.to_string(),
                    ],
                ),
                related_information: Vec::new(),
            }
        }
        DirectCallApplicability::ArgumentNotAssignable {
            index,
            argument_type,
            parameter_type,
        } => {
            if argument_types.get(index).copied() != Some(argument_type) {
                return Err(SourceCheckError::Call(plan.node));
            }
            let display = get_type_names_for_assignability_error_with_host_global_types_and_flags(
                store,
                host,
                global_types,
                argument_type,
                parameter_type,
                source_call_display_flags(options),
            )?;
            let argument = plan
                .arguments
                .get(index)
                .ok_or(SourceCheckError::Call(plan.node))?;
            let exact_optional_mismatch =
                exact_optional_argument_mismatch(store, options, argument_type, parameter_type);
            let code = if exact_optional_mismatch { 2379 } else { 2345 };
            let details = if exact_optional_mismatch {
                exact_optional_property_mismatch_details(
                    store,
                    host,
                    global_types,
                    argument_type,
                    parameter_type,
                    source_call_display_flags(options),
                )?
            } else {
                Vec::new()
            };
            CanonicalCheckerDiagnostic {
                node: Some(argument.unparenthesized().node),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(code).ok_or(SourceCheckError::MissingDiagnostic(code))?,
                    [display.source, display.target],
                )
                .with_details(details),
                related_information: Vec::new(),
            }
        }
    };
    Ok(Some(diagnostic))
}

#[allow(clippy::too_many_arguments)]
fn prepare_vector_source_call_diagnostic(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    plan: &SourceCallPlan,
    argument_types: &[TypeId],
    explicit_type_arguments: Option<&[TypeId]>,
    resolution: &GenericCallVectorResolution,
) -> Result<Option<CanonicalCheckerDiagnostic>, SourceCheckError> {
    let projection = resolution.projection();
    let parameter_count = store
        .signature(projection.generic_signature)
        .map(|signature| signature.parameters().len())
        .ok_or(SourceCheckError::Call(plan.node))?;
    let diagnostic = match resolution.applicability() {
        GenericCallVectorApplicability::Applicable => return Ok(None),
        GenericCallVectorApplicability::TypeArgumentArity {
            minimum,
            maximum,
            actual,
        } => {
            let syntax = plan
                .type_arguments
                .as_ref()
                .ok_or(SourceCheckError::Call(plan.node))?;
            let resolved = explicit_type_arguments.ok_or(SourceCheckError::Call(plan.node))?;
            if actual == 0
                || actual != syntax.nodes.len()
                || actual != resolved.len()
                || minimum > maximum
                || maximum != projection.type_parameters.len()
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            let range = syntax
                .diagnostic_range
                .ok_or(SourceCheckError::Call(plan.node))?;
            CanonicalCheckerDiagnostic {
                node: Some(plan.node),
                range_override: Some(CanonicalCheckerDiagnosticRange::new(plan.node, range)),
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(2558).ok_or(SourceCheckError::MissingDiagnostic(2558))?,
                    [expected_count_text(minimum, maximum), actual.to_string()],
                ),
                related_information: Vec::new(),
            }
        }
        GenericCallVectorApplicability::TooFewArguments { expected, actual } => {
            if expected != parameter_count
                || actual != plan.arguments.len()
                || actual != argument_types.len()
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            CanonicalCheckerDiagnostic {
                node: Some(plan.callee_diagnostic_node),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(2554).ok_or(SourceCheckError::MissingDiagnostic(2554))?,
                    [expected.to_string(), actual.to_string()],
                ),
                related_information: vec![missing_argument_related_information(
                    store,
                    host,
                    plan.node,
                    projection.generic_signature,
                    actual,
                )?],
            }
        }
        GenericCallVectorApplicability::TooManyArguments { expected, actual } => {
            if expected != parameter_count
                || actual != plan.arguments.len()
                || actual != argument_types.len()
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            CanonicalCheckerDiagnostic {
                node: Some(plan.node),
                range_override: Some(extra_argument_diagnostic_range(host, plan, expected)?),
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(2554).ok_or(SourceCheckError::MissingDiagnostic(2554))?,
                    [expected.to_string(), actual.to_string()],
                ),
                related_information: Vec::new(),
            }
        }
        GenericCallVectorApplicability::ExplicitTypeArgumentConstraint {
            index,
            type_argument,
            constraint,
        } => {
            let syntax = plan
                .type_arguments
                .as_ref()
                .ok_or(SourceCheckError::Call(plan.node))?;
            let resolved = explicit_type_arguments.ok_or(SourceCheckError::Call(plan.node))?;
            let node = *syntax
                .nodes
                .get(index)
                .ok_or(SourceCheckError::Call(plan.node))?;
            if resolved.get(index).copied() != Some(type_argument) {
                return Err(SourceCheckError::Call(plan.node));
            }
            let display = get_type_names_for_assignability_error_with_host_global_types_and_flags(
                store,
                host,
                global_types,
                type_argument,
                constraint,
                source_call_display_flags(options),
            )?;
            CanonicalCheckerDiagnostic {
                node: Some(node),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(2344).ok_or(SourceCheckError::MissingDiagnostic(2344))?,
                    [display.source, display.target],
                ),
                related_information: Vec::new(),
            }
        }
        GenericCallVectorApplicability::ArgumentNotAssignable {
            index,
            argument_type,
            parameter_type,
        } => {
            if argument_types.get(index).copied() != Some(argument_type) {
                return Err(SourceCheckError::Call(plan.node));
            }
            let argument = plan
                .arguments
                .get(index)
                .ok_or(SourceCheckError::Call(plan.node))?;
            let display = get_type_names_for_assignability_error_with_host_global_types_and_flags(
                store,
                host,
                global_types,
                argument_type,
                parameter_type,
                source_call_display_flags(options),
            )?;
            let exact_optional_mismatch =
                exact_optional_argument_mismatch(store, options, argument_type, parameter_type);
            let code = if exact_optional_mismatch { 2379 } else { 2345 };
            let details = if exact_optional_mismatch {
                exact_optional_property_mismatch_details(
                    store,
                    host,
                    global_types,
                    argument_type,
                    parameter_type,
                    source_call_display_flags(options),
                )?
            } else {
                Vec::new()
            };
            CanonicalCheckerDiagnostic {
                node: Some(argument.unparenthesized().node),
                range_override: None,
                diagnostic: Diagnostic::with_arguments(
                    message_by_code(code).ok_or(SourceCheckError::MissingDiagnostic(code))?,
                    [display.source, display.target],
                )
                .with_details(details),
                related_information: Vec::new(),
            }
        }
    };
    Ok(Some(diagnostic))
}

fn preflight_call_publication(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
    return_type: TypeId,
) -> Result<Option<SignatureId>, SourceCheckError> {
    preflight_call_links(store, node)?;
    let existing_type = store
        .type_node_links(node)
        .and_then(|links| links.resolved_type);
    if existing_type.is_some_and(|existing| existing != return_type) {
        return Err(SourceCheckError::Call(node));
    }
    Ok(store
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature()))
}

#[allow(clippy::too_many_arguments)]
pub(super) fn check_direct_source_call(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &SourceCallPlan,
    callee_type: TypeId,
    argument_types: &[TypeId],
) -> Result<CheckedSourceCall, SourceCheckError> {
    preflight_call_links(store, plan.node)?;
    let existing_call_signature = store
        .signature_links(plan.node)
        .and_then(|links| links.resolved_signature.signature());
    let limit_mark = session.limit_event_mark();
    let explicit_type_arguments = resolve_explicit_source_type_arguments(
        store,
        host,
        global_types,
        options,
        session,
        diagnostics,
        plan.type_arguments
            .as_ref()
            .map(|type_arguments| type_arguments.nodes.as_slice()),
    )?;
    let mut retried_signatures = HashSet::new();
    let resolution = loop {
        match resolve_source_call_once(
            store,
            host,
            global_types,
            options,
            existing_call_signature,
            session,
            SourceCallResolutionRequest {
                callee_form: plan.callee_form,
                callee_type,
                argument_types,
                explicit_type_arguments: explicit_type_arguments.as_deref(),
            },
        ) {
            Ok(resolution) => break resolution,
            Err(SourceCallResolutionError::Retry(signature))
                if retried_signatures.insert(signature) =>
            {
                resolve_signature_return(
                    store,
                    host,
                    global_types,
                    options,
                    session,
                    diagnostics,
                    signature,
                )?;
            }
            Err(SourceCallResolutionError::Relation(error)) => return Err(error.into()),
            Err(SourceCallResolutionError::Unsupported) if plan.type_arguments.is_some() => {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Call(plan.node),
                ));
            }
            Err(
                SourceCallResolutionError::Retry(_)
                | SourceCallResolutionError::Unsupported
                | SourceCallResolutionError::Invariant,
            ) => {
                return Err(SourceCheckError::Call(plan.node));
            }
        }
    };

    let (signature, return_type, diagnostic) = match resolution {
        ResolvedSourceCall::Legacy(resolution) => {
            let existing = preflight_call_publication(store, plan.node, resolution.return_type)?;
            if existing.is_some_and(|existing| existing != resolution.signature) {
                return Err(SourceCheckError::Call(plan.node));
            }
            let diagnostic = prepare_legacy_source_call_diagnostic(
                store,
                host,
                global_types,
                options,
                plan,
                argument_types,
                resolution,
            )?;
            (resolution.signature, resolution.return_type, diagnostic)
        }
        ResolvedSourceCall::Vector(resolution) => {
            let diagnostic = prepare_vector_source_call_diagnostic(
                store,
                host,
                global_types,
                options,
                plan,
                argument_types,
                explicit_type_arguments.as_deref(),
                &resolution,
            )?;
            let materialized =
                materialize_generic_call_vector_source(store, &resolution, existing_call_signature)
                    .map_err(|error| match error {
                        GenericCallVectorError::Relation(error)
                        | GenericCallVectorError::Inference(NakedTypeCandidateError::Relation(
                            error,
                        )) => SourceCheckError::from(error),
                        GenericCallVectorError::Unsupported(_)
                        | GenericCallVectorError::Invariant(_)
                        | GenericCallVectorError::Inference(_)
                        | GenericCallVectorError::Instantiation(_) => {
                            SourceCheckError::Call(plan.node)
                        }
                    })?;
            let return_type =
                demand_generic_call_vector_return_with_session(store, &resolution, session)
                    .map_err(|error| match error {
                        GenericCallVectorError::Relation(error)
                        | GenericCallVectorError::Inference(NakedTypeCandidateError::Relation(
                            error,
                        )) => SourceCheckError::from(error),
                        GenericCallVectorError::Unsupported(_)
                        | GenericCallVectorError::Invariant(_)
                        | GenericCallVectorError::Inference(_)
                        | GenericCallVectorError::Instantiation(_) => {
                            SourceCheckError::Call(plan.node)
                        }
                    })?;
            if preflight_call_publication(store, plan.node, return_type)? != existing_call_signature
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            (materialized.call_signature, return_type, diagnostic)
        }
        ResolvedSourceCall::Identity(resolution) => {
            let return_type =
                demand_identity_generic_call_return_with_session(store, &resolution, session)
                    .map_err(|error| match error {
                        IdentityGenericCallError::Relation(error) => SourceCheckError::from(error),
                        IdentityGenericCallError::Unsupported(_)
                        | IdentityGenericCallError::Invariant(_)
                        | IdentityGenericCallError::Inference(_)
                        | IdentityGenericCallError::Instantiation(_) => {
                            SourceCheckError::Call(plan.node)
                        }
                    })?;
            if preflight_call_publication(store, plan.node, return_type)? != existing_call_signature
            {
                return Err(SourceCheckError::Call(plan.node));
            }
            let legacy = ResolvedLegacySourceCall {
                signature: resolution.projection.signature,
                return_type,
                minimum_argument_count: 1,
                maximum_argument_count: 1,
                has_effective_rest: false,
                applicability: resolution.applicability,
            };
            let diagnostic = prepare_legacy_source_call_diagnostic(
                store,
                host,
                global_types,
                options,
                plan,
                argument_types,
                legacy,
            )?;
            (resolution.projection.signature, return_type, diagnostic)
        }
    };
    publish_call_links(store, plan.node, signature, return_type)?;
    if let Some(diagnostic) = diagnostic {
        merge_retry_diagnostic(diagnostics, diagnostic);
    }
    if session.limit_event_occurred_since(limit_mark) {
        merge_retry_diagnostic(
            diagnostics,
            CanonicalCheckerDiagnostic {
                node: Some(plan.node),
                range_override: None,
                diagnostic: Diagnostic::new(
                    message_by_code(2589).ok_or(SourceCheckError::MissingDiagnostic(2589))?,
                ),
                related_information: Vec::new(),
            },
        );
    }
    Ok(CheckedSourceCall { return_type })
}

#[allow(clippy::too_many_arguments)]
fn resolve_signature_return(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    signature: super::SignatureId,
) -> Result<(), SourceCheckError> {
    let mut resolution_diagnostics = CanonicalCheckerDiagnostics::default();
    let result = CanonicalTypeQuery::new_with_global_types_and_session(
        store,
        host,
        global_types,
        options,
        session,
        &mut resolution_diagnostics,
    )?
    .get_return_type_of_signature(signature);
    merge_retry_diagnostics(diagnostics, resolution_diagnostics);
    result?;
    Ok(())
}

fn publish_call_links(
    store: &mut CanonicalTypeMapperStore,
    node: NodeRef,
    signature: super::SignatureId,
    return_type: TypeId,
) -> Result<(), SourceCheckError> {
    let expected_type = TypeNodeLinks {
        resolved_type: Some(return_type),
        ..TypeNodeLinks::default()
    };
    let expected_signature = SignatureLinks {
        resolved_signature: ResolvedSignatureState::Resolved(signature),
        ..SignatureLinks::default()
    };
    let type_links = store.type_node_links(node);
    let signature_links = store.signature_links(node);
    let exact = type_links == Some(&expected_type) && signature_links == Some(&expected_signature);
    if exact {
        return Ok(());
    }
    let type_is_cold = type_links.is_none_or(|links| links == &TypeNodeLinks::default());
    let signature_is_cold = signature_links.is_none_or(|links| links == &SignatureLinks::default());
    if !type_is_cold || !signature_is_cold {
        return Err(SourceCheckError::Call(node));
    }
    if !store.set_signature_links(node, expected_signature)
        || !store.set_type_node_links(node, expected_type)
    {
        return Err(SourceCheckError::Call(node));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName, SemanticSymbolId,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        CanonicalCheckerContext, SourceFileLinks,
        bootstrap::UnionReduction,
        module_resolution::{
            CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
            CanonicalModuleResolutionMode, CanonicalResolvedModuleInput,
        },
        object_members::{
            DeclaredPropertyTypeGraphValidation, validate_resolved_declared_property_type_graph,
        },
        source::{PlannedIdentifierRead, PlannedIdentifierReadKind},
        type_records::{LiteralValue, TypeData},
    };

    fn parsed(text: &str) -> ParseResult {
        let parsed = parse_source_file(text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        parsed
    }

    fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
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

    fn context_with_default_library<'arena>(
        library: &'arena ParseResult,
        library_file: FileId,
        source: &'arena ParseResult,
        source_file: FileId,
    ) -> CanonicalCheckerContext<'arena> {
        let files = [(library_file, library), (source_file, source)];
        let mut binder = CanonicalBinder::new();
        for (file, parsed) in files {
            let is_default_library = file == library_file;
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        is_default_library,
                        is_default_library,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
        }
        for (file, parsed) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        CanonicalCheckerContext::new(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn imported_context<'arena>(
        importer: &'arena ParseResult,
        importer_file: FileId,
        target: &'arena ParseResult,
        target_file: FileId,
    ) -> CanonicalCheckerContext<'arena> {
        let files = [(importer_file, importer), (target_file, target)];
        let mut binder = CanonicalBinder::new();
        for (file, parsed) in files {
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        false,
                        CanonicalModuleState::External,
                    ),
                )
                .unwrap();
        }
        for (file, parsed) in files {
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let mut module_specifiers = importer
            .arena
            .iter()
            .filter_map(|(_, record)| match &record.data {
                NodeData::ImportDeclaration(import) => Some((
                    record.range.start,
                    NodeRef::new(importer.arena.id(), importer_file, import.module_specifier),
                )),
                _ => None,
            })
            .collect::<Vec<_>>();
        module_specifiers.sort_by_key(|(start, _)| *start);
        assert!(
            !module_specifiers.is_empty(),
            "fixture contains an import declaration"
        );
        CanonicalCheckerContext::new_with_module_resolutions(
            binder.finish(),
            files
                .into_iter()
                .map(|(file, parsed)| (file, &parsed.arena))
                .collect(),
            CanonicalCheckerOptions::default(),
            CanonicalModuleResolutionManifestInput::new(module_specifiers.into_iter().map(
                |(_, module_specifier)| {
                    CanonicalModuleResolutionEntry::resolved(
                        module_specifier,
                        CanonicalResolvedModuleInput::new(
                            target_file,
                            CanonicalModuleResolutionMode::Esm,
                            CanonicalModuleResolutionMode::Esm,
                        ),
                    )
                },
            )),
        )
        .unwrap()
    }

    fn calls(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
        parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::CallExpression)
            .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
            .collect()
    }

    fn property_accesses(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
        parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::PropertyAccessExpression)
            .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
            .collect()
    }

    fn property_name(parsed: &ParseResult, file: FileId, access: NodeRef) -> NodeRef {
        let NodeData::PropertyAccessExpression(property) =
            &parsed.arena.get(access.node).unwrap().data
        else {
            panic!("expected a property access")
        };
        NodeRef::new(parsed.arena.id(), file, property.name)
    }

    fn first_function_symbol(
        parsed: &ParseResult,
        context: &CanonicalCheckerContext<'_>,
        file: FileId,
    ) -> SemanticSymbolId {
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::FunctionDeclaration)
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .expect("fixture must contain a function declaration");
        let (_, bound) = context.file(file).unwrap();
        bound.symbol(declaration).unwrap()
    }

    fn identifier_plan(node: NodeRef, symbol: SemanticSymbolId) -> PlannedExpression {
        PlannedExpression::new(
            node,
            PlannedExpressionKind::Identifier(PlannedIdentifierRead {
                resolved_symbol: symbol,
                value_symbol: symbol,
                kind: PlannedIdentifierReadKind::Function,
            }),
        )
    }

    fn string_argument_plans(syntax: &DirectSourceCallSyntax) -> Vec<PlannedExpression> {
        syntax
            .arguments()
            .iter()
            .enumerate()
            .map(|(index, node)| {
                PlannedExpression::new(
                    *node,
                    PlannedExpressionKind::String(format!("argument{index}")),
                )
            })
            .collect()
    }

    #[derive(Debug, Eq, PartialEq)]
    struct CallPublicationState {
        type_count: usize,
        mapper_count: usize,
        signature_count: usize,
        cached_signature_count: usize,
        type_links: Option<TypeNodeLinks>,
        signature_links: Option<SignatureLinks>,
        diagnostics: Vec<CanonicalCheckerDiagnostic>,
    }

    fn call_publication_state(
        context: &CanonicalCheckerContext<'_>,
        call: NodeRef,
    ) -> CallPublicationState {
        CallPublicationState {
            type_count: context.store().type_len(),
            mapper_count: context.store().mapper_len(),
            signature_count: context.store().signature_len(),
            cached_signature_count: context.store().cached_signature_len(),
            type_links: context.store().type_node_links(call).cloned(),
            signature_links: context.store().signature_links(call).cloned(),
            diagnostics: context.diagnostics().as_slice().to_vec(),
        }
    }

    fn mark_source_unchecked(context: &mut CanonicalCheckerContext<'_>, file: FileId) {
        let source = context.source_file(file).unwrap();
        let mut links = context
            .store()
            .source_file_links(source)
            .cloned()
            .unwrap_or_else(SourceFileLinks::default);
        links.type_checked = false;
        assert!(
            context
                .store_mut_for_test()
                .set_source_file_links(source, links)
        );
    }

    #[test]
    fn call_plan_retains_go_style_type_argument_list_interior() {
        let text = concat!(
            "function pair<T, U>(left: T, right: U): U { return right; } ",
            "const spaced = pair< string, number >(\"left\", 1); ",
            "const empty = pair<>(\"left\", 1); ",
            "const trailing = pair< string, number ,   >(\"left\", 1);",
        );
        let parsed = parsed(text);
        let file = FileId::new(435);
        let context = context(&parsed, file);
        let call_nodes = calls(&parsed, file);
        let [spaced, empty, trailing] = call_nodes.as_slice() else {
            panic!("expected spaced, empty, and trailing-comma generic calls")
        };

        let spaced = plan_direct_source_call_syntax(&parsed.arena, context.store(), *spaced)
            .unwrap()
            .type_arguments
            .unwrap();
        let spaced_start = text.find("string, number").unwrap();
        let spaced_end = spaced_start + "string, number".len();
        assert_eq!(spaced.nodes.len(), 2);
        assert_eq!(spaced.trailing_comma_range, None);
        let spaced_syntax_start = text.find("< string, number >").unwrap();
        let spaced_syntax_end = spaced_syntax_start + "< string, number >".len();
        assert_eq!(
            spaced.syntax_range,
            TextRange::new(
                TextPos::new(u32::try_from(spaced_syntax_start).unwrap()),
                TextPos::new(u32::try_from(spaced_syntax_end).unwrap()),
            )
        );
        assert_eq!(
            spaced.diagnostic_range,
            Some(TextRange::new(
                TextPos::new(u32::try_from(spaced_start).unwrap()),
                TextPos::new(u32::try_from(spaced_end).unwrap()),
            ))
        );

        let empty = plan_direct_source_call_syntax(&parsed.arena, context.store(), *empty)
            .unwrap()
            .type_arguments
            .unwrap();
        assert!(empty.nodes.is_empty());
        assert_eq!(empty.trailing_comma_range, None);
        let empty_syntax_start = text.find("<>").unwrap();
        assert_eq!(
            empty.syntax_range,
            TextRange::new(
                TextPos::new(u32::try_from(empty_syntax_start).unwrap()),
                TextPos::new(u32::try_from(empty_syntax_start + 2).unwrap()),
            )
        );
        assert_eq!(empty.diagnostic_range, None);

        let trailing = plan_direct_source_call_syntax(&parsed.arena, context.store(), *trailing)
            .unwrap()
            .type_arguments
            .unwrap();
        let trailing_start = text.rfind("string, number ,").unwrap();
        let trailing_end = trailing_start + "string, number ,".len();
        assert_eq!(trailing.nodes.len(), 2);
        assert_eq!(
            trailing.trailing_comma_range,
            Some(TextRange::new(
                TextPos::new(u32::try_from(trailing_end - 1).unwrap()),
                TextPos::new(u32::try_from(trailing_end).unwrap()),
            ))
        );
        assert_eq!(
            trailing.diagnostic_range,
            Some(TextRange::new(
                TextPos::new(u32::try_from(trailing_start).unwrap()),
                TextPos::new(u32::try_from(trailing_end).unwrap()),
            ))
        );
    }

    #[test]
    fn generic_call_grammar_diagnostics_use_exact_bracket_and_comma_ranges() {
        let text = concat!(
            "function identity<T>(value: T): T { return value; } ",
            "const empty = identity<>(1 + true); ",
            "const trailing = identity< string , /* trivia */ >(\"trailing\");",
        );
        let parsed = parsed(text);
        let file = FileId::new(436);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            vec![1099, 2365, 1009]
        );
        let mut call_nodes = calls(&parsed, file);
        call_nodes.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [empty, trailing] = call_nodes.as_slice() else {
            panic!("expected empty and trailing-comma generic calls")
        };
        let empty_start = text.find("<>").unwrap();
        assert_eq!(diagnostics[0].node, Some(*empty));
        assert_eq!(
            diagnostics[0].range_override,
            Some(CanonicalCheckerDiagnosticRange::new(
                *empty,
                TextRange::new(
                    TextPos::new(u32::try_from(empty_start).unwrap()),
                    TextPos::new(u32::try_from(empty_start + 2).unwrap()),
                ),
            ))
        );
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Type argument list cannot be empty."
        );
        let trailing_start = text.find(", /* trivia */").unwrap();
        assert_eq!(diagnostics[2].node, Some(*trailing));
        assert_eq!(
            diagnostics[2].range_override,
            Some(CanonicalCheckerDiagnosticRange::new(
                *trailing,
                TextRange::new(
                    TextPos::new(u32::try_from(trailing_start).unwrap()),
                    TextPos::new(u32::try_from(trailing_start + 1).unwrap()),
                ),
            ))
        );
        assert_eq!(
            diagnostics[2].diagnostic.render().unwrap(),
            "Trailing comma not allowed."
        );

        let cold_diagnostics = context.diagnostics().as_slice().to_vec();
        let cold_counts = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().cached_signature_len(),
        );
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(context.diagnostics().as_slice(), cold_diagnostics);
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().cached_signature_len(),
            ),
            cold_counts
        );
    }

    #[test]
    fn generic_call_recovery_replays_warm_without_source_writes() {
        let parsed = parsed(concat!(
            "function identity<T>(value: T): T { return value; } ",
            "const bad = identity<string>(1);",
        ));
        let file = FileId::new(439);
        let mut context = context(&parsed, file);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one generic call")
        };

        context.check_source_file(file).unwrap();

        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2345]
        );
        let cold = call_publication_state(&context, *call);
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(call_publication_state(&context, *call), cold);
    }

    #[test]
    fn finished_call_plan_rejects_a_same_shaped_forged_callee_without_publication() {
        let parsed = parsed(concat!(
            "function first(left: string, right: string): void {} ",
            "function second(left: string, right: string): void {} ",
            "const one = first('left', 'right'); ",
            "const two = second('other', 'tail');",
        ));
        let file = FileId::new(433);
        let mut call_nodes = calls(&parsed, file);
        call_nodes.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [first_call, second_call] = call_nodes.as_slice() else {
            panic!("expected two direct calls")
        };
        let context = context(&parsed, file);
        let first_syntax =
            plan_direct_source_call_syntax(&parsed.arena, context.store(), *first_call).unwrap();
        let second_syntax =
            plan_direct_source_call_syntax(&parsed.arena, context.store(), *second_call).unwrap();
        let symbol = first_function_symbol(&parsed, &context, file);
        let arguments = string_argument_plans(&first_syntax);
        assert!(
            finish_direct_source_call_plan(
                &first_syntax,
                identifier_plan(first_syntax.callee(), symbol),
                arguments.clone(),
            )
            .is_ok()
        );
        let before = call_publication_state(&context, *first_call);

        assert!(matches!(
            finish_direct_source_call_plan(
                &first_syntax,
                identifier_plan(second_syntax.callee(), symbol),
                arguments,
            ),
            Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(node)))
                if node == *first_call
        ));

        assert_eq!(call_publication_state(&context, *first_call), before);
    }

    #[test]
    fn finished_call_plan_rejects_swapped_same_shaped_arguments_without_publication() {
        let parsed = parsed(concat!(
            "function take(left: string, right: string): void {} ",
            "const result = take('left', 'right');",
        ));
        let file = FileId::new(434);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one direct call")
        };
        let context = context(&parsed, file);
        let syntax = plan_direct_source_call_syntax(&parsed.arena, context.store(), *call).unwrap();
        let symbol = first_function_symbol(&parsed, &context, file);
        let callee = identifier_plan(syntax.callee(), symbol);
        let mut arguments = string_argument_plans(&syntax);
        assert_eq!(arguments.len(), 2);
        assert!(finish_direct_source_call_plan(&syntax, callee.clone(), arguments.clone()).is_ok());
        arguments.swap(0, 1);
        let before = call_publication_state(&context, *call);

        assert!(matches!(
            finish_direct_source_call_plan(&syntax, callee, arguments),
            Err(SourceCheckError::Unsupported(UnsupportedSourceSyntax::Call(node)))
                if node == *call
        ));

        assert_eq!(call_publication_state(&context, *call), before);
    }

    #[test]
    fn required_own_property_calls_publish_function_and_source_callables_cold_and_warm() {
        let parsed = parsed(concat!(
            "type API = { fn: (value: number) => string }; ",
            "function fromType(api: API): string { return api.fn(1); } ",
            "function render(value: number): string { return 'ok'; } ",
            "const holder = { fn: render }; ",
            "const fromSource: string = holder.fn(1);",
        ));
        let file = FileId::new(440);
        let mut calls = calls(&parsed, file);
        calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let mut accesses = property_accesses(&parsed, file);
        accesses.sort_by_key(|access| parsed.arena.get(access.node).unwrap().range.start);
        assert_eq!(calls.len(), 2);
        assert_eq!(accesses.len(), 2);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        for (call, access) in calls.iter().zip(&accesses) {
            assert_eq!(
                context
                    .store()
                    .type_node_links(*call)
                    .and_then(|links| links.resolved_type),
                Some(string)
            );
            assert!(
                context
                    .store()
                    .signature_links(*call)
                    .is_some_and(|links| links.resolved_signature.signature().is_some())
            );
            assert!(
                context
                    .store()
                    .type_node_links(*access)
                    .and_then(|links| links.resolved_type)
                    .is_some()
            );
            assert!(
                context
                    .store()
                    .symbol_node_links(*access)
                    .is_some_and(|links| links.resolved_symbol.is_some())
            );
        }

        let cold_calls = calls
            .iter()
            .map(|call| call_publication_state(&context, *call))
            .collect::<Vec<_>>();
        let cold_properties = accesses
            .iter()
            .map(|access| {
                (
                    context.store().type_node_links(*access).cloned(),
                    context.store().symbol_node_links(*access).cloned(),
                )
            })
            .collect::<Vec<_>>();
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            calls
                .iter()
                .map(|call| call_publication_state(&context, *call))
                .collect::<Vec<_>>(),
            cold_calls
        );
        assert_eq!(
            accesses
                .iter()
                .map(|access| {
                    (
                        context.store().type_node_links(*access).cloned(),
                        context.store().symbol_node_links(*access).cloned(),
                    )
                })
                .collect::<Vec<_>>(),
            cold_properties
        );
    }

    #[test]
    fn declared_call_sets_match_the_pinned_oracle_and_preserve_overload_order() {
        // Pinned tsgo oracle: the first applicable overload wins. `ordered(1)`
        // therefore returns string even though the following overload has the
        // same parameter list, while `branching(1)` skips its string overload.
        let parsed = parsed(concat!(
            "interface Ordered { ",
            "(value: number): string; ",
            "(value: number): number; ",
            "} ",
            "type Branching = { ",
            "(value: string): number; ",
            "(value: number): string; ",
            "}; ",
            "type Unary = { (value: boolean): number; }; ",
            "function fromInterface(ordered: Ordered): string { return ordered(1); } ",
            "function fromTypeLiteral(branching: Branching): string { return branching(1); } ",
            "function exactSingle(unary: Unary): number { return unary(true); }",
        ));
        let file = FileId::new(480);
        let mut calls = calls(&parsed, file);
        calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [ordered_call, branching_call, exact_call] = calls.as_slice() else {
            panic!("expected the ordered, branching, and exact-single calls")
        };
        let mut declarations = parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::CallSignature)
            .map(|(node, record)| {
                (
                    record.range.start,
                    NodeRef::new(parsed.arena.id(), file, node),
                )
            })
            .collect::<Vec<_>>();
        declarations.sort_by_key(|(start, _)| *start);
        let [ordered_first, _, _, branching_second, exact_declaration] = declarations.as_slice()
        else {
            panic!("expected five declared call signatures")
        };
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            [*ordered_call, *branching_call, *exact_call].map(|call| {
                context
                    .store()
                    .type_node_links(call)
                    .and_then(|links| links.resolved_type)
            }),
            [
                Some(string),
                Some(string),
                Some(context.store().intrinsic_bootstrap().unwrap().number_type),
            ],
        );
        let declared_signature = |declaration: NodeRef| {
            context
                .store()
                .signature_links(declaration)
                .and_then(|links| links.resolved_signature.signature())
        };
        assert_eq!(
            context
                .store()
                .signature_links(*ordered_call)
                .and_then(|links| links.resolved_signature.signature()),
            declared_signature(ordered_first.1),
        );
        assert_eq!(
            context
                .store()
                .signature_links(*branching_call)
                .and_then(|links| links.resolved_signature.signature()),
            declared_signature(branching_second.1),
        );
        assert_eq!(
            context
                .store()
                .signature_links(*exact_call)
                .and_then(|links| links.resolved_signature.signature()),
            declared_signature(exact_declaration.1),
        );

        let cold_counts = (
            context.store().type_len(),
            context.store().signature_len(),
            context.store().callable_signature_parameter_types_len(),
        );
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().callable_signature_parameter_types_len(),
            ),
            cold_counts,
        );

        let ordered_callee =
            plan_direct_source_call_syntax(&parsed.arena, context.store(), *ordered_call)
                .unwrap()
                .callee();
        let callable = context
            .store()
            .type_node_links(ordered_callee)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let undefined = context
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_type;
        let callable_union = context
            .store_mut_for_test()
            .expression_union_type(&[callable, undefined], UnionReduction::Literal)
            .unwrap();
        assert_eq!(
            context
                .store()
                .validate_cached_union_result(callable_union, None),
            Ok(())
        );
    }

    #[test]
    fn declared_call_set_poison_fails_closed_without_republishing_the_call() {
        let parsed = parsed(concat!(
            "interface Callable { ",
            "(value: number): string; ",
            "(value: string): number; ",
            "} ",
            "function use(callable: Callable): string { return callable(1); }",
        ));
        let file = FileId::new(481);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one call")
        };
        let call = *call;
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::CallSignature)
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let mut context = context(&parsed, file);
        context.check_source_file(file).unwrap();
        mark_source_unchecked(&mut context, file);
        assert!(
            context
                .store_mut_for_test()
                .set_signature_links(declaration, SignatureLinks::default())
        );
        let poisoned_call = call_publication_state(&context, call);

        assert!(context.check_source_file(file).is_err());
        assert_eq!(call_publication_state(&context, call), poisoned_call);
        assert!(
            context
                .store()
                .signature_links(declaration)
                .is_some_and(|links| links == &SignatureLinks::default())
        );
    }

    #[test]
    fn declared_call_set_failure_recovery_remains_an_atomic_boundary() {
        // Pinned tsgo synthesizes a recovery signature whose return type is
        // `never`. That constructor is outside this overload slice, so the
        // call must remain unpublished rather than reuse either declaration.
        let parsed = parsed(concat!(
            "interface Recovery { ",
            "(value: number, other: number): string; ",
            "(value: string): number; ",
            "} ",
            "function use(callable: Recovery): number { return callable(true); }",
        ));
        let file = FileId::new(487);
        let call = calls(&parsed, file)
            .into_iter()
            .next()
            .expect("fixture contains one direct call");
        let declarations = parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::CallSignature)
            .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
            .collect::<Vec<_>>();
        let mut context = context(&parsed, file);

        assert!(context.check_source_file(file).is_err());

        assert!(context.diagnostics().is_empty());
        assert!(context.store().type_node_links(call).is_none());
        assert!(context.store().signature_links(call).is_none());
        assert!(declarations.iter().all(|declaration| {
            context
                .store()
                .signature_links(*declaration)
                .is_some_and(|links| links.resolved_signature.signature().is_some())
        }));
    }

    #[test]
    fn unsupported_declared_call_members_reject_before_signature_publication() {
        // The pinned oracle accepts each family below. This provider's first
        // production cut intentionally rejects them as one atomic boundary.
        for (index, member) in [
            "<T>(value: T): T;",
            "(value?: number): string;",
            "(...values: number[]): string;",
            "new (value: number): string; (value: number): string;",
            "value: number; (value: number): string;",
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parsed(&format!(
                "interface Callable {{ {member} }} function use(callable: Callable): string {{ return callable(1); }}"
            ));
            let file = FileId::new(482 + u32::try_from(index).unwrap());
            let call = calls(&parsed, file)
                .into_iter()
                .next()
                .expect("fixture contains one direct call");
            let declarations = parsed
                .arena
                .iter()
                .filter(|(_, record)| record.kind == SyntaxKind::CallSignature)
                .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
                .collect::<Vec<_>>();
            let mut context = context(&parsed, file);

            assert!(context.check_source_file(file).is_err());
            assert!(context.store().type_node_links(call).is_none());
            assert!(context.store().signature_links(call).is_none());
            assert!(
                declarations
                    .iter()
                    .all(|declaration| context.store().signature_links(*declaration).is_none())
            );
        }

        let parsed = parsed(concat!(
            "interface Callable { (value: number): string; } ",
            "declare var Callable: number; ",
            "function use(callable: Callable): string { return callable(1); }",
        ));
        let file = FileId::new(488);
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::CallSignature)
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let mut context = context(&parsed, file);
        assert!(context.check_source_file(file).is_err());
        assert!(context.store().signature_links(declaration).is_none());
    }

    #[test]
    fn property_call_diagnostics_retain_the_name_argument_and_call_nodes() {
        let text = concat!(
            "type API = { fn: (value: number) => string }; ",
            "function tooFew(api: API): string { return api.fn(); } ",
            "function wrong(api: API): string { return api.fn('bad'); } ",
            "function tooMany(api: API): string { return api.fn(1, 2); }",
        );
        let parsed = parsed(text);
        let file = FileId::new(441);
        let mut calls = calls(&parsed, file);
        calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let mut accesses = property_accesses(&parsed, file);
        accesses.sort_by_key(|access| parsed.arena.get(access.node).unwrap().range.start);
        let [too_few, _, too_many] = calls.as_slice() else {
            panic!("expected three property calls")
        };
        let [too_few_access, _, _] = accesses.as_slice() else {
            panic!("expected three property accesses")
        };
        let wrong_argument = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                matches!(&record.data, NodeData::StringLiteral(literal) if literal.text == "bad")
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            [2554, 2345, 2554]
        );
        assert_eq!(
            diagnostics[0].node,
            Some(property_name(&parsed, file, *too_few_access))
        );
        assert_eq!(diagnostics[0].range_override, None);
        assert_eq!(diagnostics[1].node, Some(wrong_argument));
        assert_eq!(diagnostics[1].range_override, None);
        assert_eq!(diagnostics[2].node, Some(*too_many));
        assert!(diagnostics[2].range_override.is_some());
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(calls.iter().all(|call| {
            context
                .store()
                .type_node_links(*call)
                .and_then(|links| links.resolved_type)
                == Some(string)
        }));
        assert_ne!(diagnostics[0].node, Some(*too_few));
    }

    #[test]
    fn property_call_poison_is_rejected_without_additional_publication() {
        for poison_property in [true, false] {
            let parsed = parsed(concat!(
                "type API = { fn: (value: number) => string }; ",
                "function use(api: API): string { return api.fn(1); }",
            ));
            let file = FileId::new(if poison_property { 442 } else { 443 });
            let call_nodes = calls(&parsed, file);
            let [call] = call_nodes.as_slice() else {
                panic!("expected one call")
            };
            let call = *call;
            let access_nodes = property_accesses(&parsed, file);
            let [access] = access_nodes.as_slice() else {
                panic!("expected one property access")
            };
            let access = *access;
            let mut context = context(&parsed, file);
            context.check_source_file(file).unwrap();
            mark_source_unchecked(&mut context, file);

            if poison_property {
                assert!(context.store_mut_for_test().set_type_node_links(
                    access,
                    TypeNodeLinks {
                        outer_type_parameters: Some(Vec::new()),
                        ..TypeNodeLinks::default()
                    },
                ));
            } else {
                assert!(
                    context
                        .store_mut_for_test()
                        .set_signature_links(call, SignatureLinks::default())
                );
            }
            let poisoned_call = call_publication_state(&context, call);
            let poisoned_property_type = context.store().type_node_links(access).cloned();
            let poisoned_property_symbol = context.store().symbol_node_links(access).cloned();
            let result = context.check_source_file(file);

            if poison_property {
                assert_eq!(result, Err(SourceCheckError::Property(access)));
            } else {
                assert_eq!(result, Err(SourceCheckError::Call(call)));
            }
            assert_eq!(call_publication_state(&context, call), poisoned_call);
            assert_eq!(
                context.store().type_node_links(access),
                poisoned_property_type.as_ref()
            );
            assert_eq!(
                context.store().symbol_node_links(access),
                poisoned_property_symbol.as_ref()
            );
            let source = context.source_file(file).unwrap();
            assert!(
                !context
                    .store()
                    .source_file_links(source)
                    .is_some_and(|links| links.type_checked)
            );
        }
    }

    #[test]
    fn hoisted_direct_call_publishes_exact_return_and_replays_warm() {
        let parsed = parsed(concat!(
            "const result = id(1); ",
            "function id(value: number): string { return 'ok'; }",
        ));
        let file = FileId::new(401);
        let call_nodes = calls(&parsed, file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one direct call")
        };
        let call = *call;
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(
            context
                .store()
                .type_node_links(call)
                .and_then(|links| links.resolved_type),
            Some(string)
        );
        let signature = context
            .store()
            .signature_links(call)
            .and_then(|links| links.resolved_signature.signature())
            .expect("call signature must be cached");
        assert_eq!(
            context
                .store()
                .signature(signature)
                .unwrap()
                .resolved_return_type(),
            Some(string)
        );
        assert!(context.diagnostics().is_empty());

        let type_count = context.store().type_len();
        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();
        assert_eq!(context.store().type_len(), type_count);
        assert_eq!(
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature()),
            Some(signature)
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn inferred_and_explicit_identity_calls_reuse_instantiated_signatures_warm() {
        let parsed = parsed(concat!(
            "function identity<T>(value: T): T { return value; } ",
            "const inferred: 'x' = identity('x'); ",
            "const explicit = identity<string>('x');",
        ));
        let file = FileId::new(404);
        let mut call_nodes = calls(&parsed, file);
        call_nodes.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [inferred, explicit] = call_nodes.as_slice() else {
            panic!("expected inferred and explicit calls")
        };
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let inferred_type = context
            .store()
            .type_node_links(*inferred)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_ne!(inferred_type, string);
        assert_eq!(
            context
                .store()
                .type_node_links(*explicit)
                .and_then(|links| links.resolved_type),
            Some(string)
        );
        let signatures = [inferred, explicit].map(|call| {
            context
                .store()
                .signature_links(*call)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap()
        });
        assert_ne!(signatures[0], signatures[1]);
        let counts = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        );
        assert!(context.diagnostics().is_empty());

        mark_source_unchecked(&mut context, file);
        context.check_source_file(file).unwrap();

        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
            ),
            counts
        );
        assert_eq!(
            [inferred, explicit].map(|call| {
                context
                    .store()
                    .signature_links(*call)
                    .and_then(|links| links.resolved_signature.signature())
                    .unwrap()
            }),
            signatures
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn imported_identity_calls_match_oracle_and_replay_importer_first_warm() {
        let target = parsed("export function identity<T>(value: T): T { return value; }");
        let importer = parsed(concat!(
            "import { identity } from './a'; ",
            "export const inferred = identity('inferred'); ",
            "export const explicit = identity<number>(42); ",
            "export const bad: string = identity<number>(42);",
        ));
        let importer_file = FileId::new(410);
        let target_file = FileId::new(411);
        let mut call_nodes = calls(&importer, importer_file);
        call_nodes.sort_by_key(|call| importer.arena.get(call.node).unwrap().range.start);
        let [inferred, explicit, bad] = call_nodes.as_slice() else {
            panic!("expected inferred, explicit, and bad calls")
        };
        let calls = [*inferred, *explicit, *bad];
        let mut context = imported_context(&importer, importer_file, &target, target_file);
        let target_source = context.source_file(target_file).unwrap();
        assert!(
            !context
                .store()
                .source_file_links(target_source)
                .is_some_and(|links| links.type_checked)
        );

        context.check_source_file(importer_file).unwrap();

        assert!(
            !context
                .store()
                .source_file_links(target_source)
                .is_some_and(|links| links.type_checked),
            "importer-first checking must lazily query, not recursively check, the target source"
        );
        let result_types = calls.map(|call| {
            context
                .store()
                .type_node_links(call)
                .and_then(|links| links.resolved_type)
                .expect("every imported call caches its result type")
        });
        let TypeData::Literal(inferred_literal) = context
            .store()
            .type_payload(result_types[0])
            .unwrap()
            .data()
        else {
            panic!("inferred identity result must preserve its string literal")
        };
        assert_eq!(
            inferred_literal.value,
            LiteralValue::String("inferred".to_owned())
        );
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(result_types[1..], [number, number]);

        let signatures = calls.map(|call| {
            context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature())
                .expect("every imported call caches its instantiated signature")
        });
        assert_ne!(signatures[0], signatures[1]);
        assert_eq!(signatures[1], signatures[2]);
        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            vec![2322]
        );
        assert_eq!(
            context.diagnostics().as_slice()[0]
                .diagnostic
                .render()
                .unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        let counts = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().cached_signature_len(),
        );

        mark_source_unchecked(&mut context, importer_file);
        context.check_source_file(importer_file).unwrap();

        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().cached_signature_len(),
            ),
            counts
        );
        assert_eq!(
            calls.map(|call| {
                context
                    .store()
                    .signature_links(call)
                    .and_then(|links| links.resolved_signature.signature())
                    .unwrap()
            }),
            signatures
        );
        assert_eq!(context.diagnostics().as_slice().len(), 1);
    }

    #[test]
    fn imported_declared_object_identity_calls_force_warm_replay_for_aliases_and_interfaces() {
        for (index, declaration) in [
            "export type User = { id: number }; ",
            "export interface User { id: number } ",
        ]
        .into_iter()
        .enumerate()
        {
            let target = parsed(&format!(
                "{declaration}export function identity<T>(value: T): T {{ return value; }}"
            ));
            let importer = parsed(concat!(
                "import type { User } from './a'; ",
                "import { identity } from './a'; ",
                "const user: User = { id: 1 }; ",
                "const inferred: User = identity(user); ",
                "const explicit = identity<string>('x');",
            ));
            let offset = u32::try_from(index).unwrap() * 2;
            let importer_file = FileId::new(420 + offset);
            let target_file = FileId::new(421 + offset);
            let mut call_nodes = calls(&importer, importer_file);
            call_nodes.sort_by_key(|call| importer.arena.get(call.node).unwrap().range.start);
            let [inferred, explicit] = call_nodes.as_slice() else {
                panic!("expected inferred declared-object and explicit primitive calls")
            };
            let mut context = imported_context(&importer, importer_file, &target, target_file);
            let target_source = context.source_file(target_file).unwrap();

            context.check_source_file(importer_file).unwrap();

            assert!(context.diagnostics().is_empty());
            assert!(
                !context
                    .store()
                    .source_file_links(target_source)
                    .is_some_and(|links| links.type_checked)
            );
            let result_types = [*inferred, *explicit].map(|call| {
                context
                    .store()
                    .type_node_links(call)
                    .and_then(|links| links.resolved_type)
                    .unwrap()
            });
            assert_eq!(context.type_to_string(result_types[0]).unwrap(), "User");
            assert_eq!(
                result_types[1],
                context.store().intrinsic_bootstrap().unwrap().string_type
            );
            let signatures = [*inferred, *explicit].map(|call| {
                context
                    .store()
                    .signature_links(call)
                    .and_then(|links| links.resolved_signature.signature())
                    .unwrap()
            });
            let counts = (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().cached_signature_len(),
            );

            mark_source_unchecked(&mut context, importer_file);
            context.check_source_file(importer_file).unwrap();

            assert_eq!(
                (
                    context.store().type_len(),
                    context.store().mapper_len(),
                    context.store().signature_len(),
                    context.store().cached_signature_len(),
                ),
                counts
            );
            assert_eq!(
                [*inferred, *explicit].map(|call| {
                    context
                        .store()
                        .signature_links(call)
                        .and_then(|links| links.resolved_signature.signature())
                        .unwrap()
                }),
                signatures
            );
            assert!(context.diagnostics().is_empty());
        }
    }

    #[test]
    fn exported_alias_owner_poison_rejects_warm_replay_without_new_call_publication() {
        let target = parsed(concat!(
            "export type User = { id: number }; ",
            "export function identity<T>(value: T): T { return value; }",
        ));
        let importer = parsed(concat!(
            "import type { User } from './a'; ",
            "import { identity } from './a'; ",
            "const user: User = { id: 1 }; ",
            "const inferred: User = identity(user);",
        ));
        let importer_file = FileId::new(430);
        let target_file = FileId::new(431);
        let call_nodes = calls(&importer, importer_file);
        let [call] = call_nodes.as_slice() else {
            panic!("expected one imported identity call")
        };
        let call = *call;
        let mut context = imported_context(&importer, importer_file, &target, target_file);
        context.check_source_file(importer_file).unwrap();
        assert!(context.diagnostics().is_empty());
        let call_type = context.store().type_node_links(call).cloned();
        let call_signature = context.store().signature_links(call).cloned();
        let (module, user, identity) = {
            let (_, bound) = context.file(target_file).unwrap();
            let module = bound.symbol(bound.source_file()).unwrap();
            let exports = context
                .store()
                .symbol(module)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| context.store().symbol_table(exports))
                .unwrap();
            (
                module,
                exports.get_source("User").unwrap(),
                exports.get_source("identity").unwrap(),
            )
        };
        let exports = context.store().symbol(module).unwrap().exports().unwrap();
        assert_eq!(
            context.store_mut_for_test().insert_symbol(
                exports,
                EscapedName::source("User"),
                identity,
            ),
            Some(Some(user))
        );
        mark_source_unchecked(&mut context, importer_file);
        let before = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.store().cached_signature_len(),
            context.store().relation_state_snapshot(),
        );

        let result = context.check_source_file(importer_file);

        assert!(matches!(
            result,
            Err(SourceCheckError::Import(node)) if node.file == importer_file
        ));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context.store().cached_signature_len(),
                context.store().relation_state_snapshot(),
            ),
            before
        );
        assert_eq!(context.store().type_node_links(call), call_type.as_ref());
        assert_eq!(
            context.store().signature_links(call),
            call_signature.as_ref()
        );
        assert!(context.diagnostics().is_empty());
    }

    #[test]
    fn nested_declared_objects_cannot_cross_the_source_inference_export_boundary() {
        let source = parsed(concat!(
            "function outer() { ",
            "type HiddenAlias = { id: number }; ",
            "interface HiddenInterface { id: number } ",
            "return 0; ",
            "}",
        ));
        let file = FileId::new(432);
        let mut context = context(&source, file);
        let symbols = {
            let (_, bound) = context.file(file).unwrap();
            source
                .arena
                .iter()
                .filter(|(_, record)| {
                    matches!(
                        record.kind,
                        SyntaxKind::TypeAliasDeclaration | SyntaxKind::InterfaceDeclaration
                    )
                })
                .map(|(node, _)| {
                    let declaration = NodeRef::new(source.arena.id(), file, node);
                    let raw = bound.symbol(declaration).unwrap();
                    context.store().get_merged_symbol(raw).unwrap()
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(symbols.len(), 2);

        for symbol in symbols {
            let type_ = context.get_declared_type_of_symbol(symbol).unwrap();
            assert!(matches!(
                validate_resolved_declared_property_type_graph(context.store(), type_),
                DeclaredPropertyTypeGraphValidation::Traversable(_)
            ));
            assert_eq!(
                super::super::inference::validate_inference_leaf(context.store(), type_),
                Err(super::super::inference::NakedTypeInferenceError::UnsupportedCandidate(type_)),
                "a nested declaration reaches the source-only override boundary"
            );
            assert!(
                !super::super::generic_calls::source_declared_inference_candidate_is_exported(
                    context.store(),
                    type_,
                ),
                "a nested modifier-free declaration must not mint export capability"
            );
        }
    }

    #[test]
    fn direct_calls_issue_exact_arity_and_argument_diagnostics_but_keep_return_type() {
        let text = concat!(
            "function take(value: number): string { return 'ok'; } ",
            "const tooFew = take(); ",
            "const wrong = take((('x'))); ",
            "const tooMany = take(1, ('extra'), true);",
        );
        let parsed = parsed(text);
        let file = FileId::new(402);
        let mut calls = calls(&parsed, file);
        calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [too_few, _, _] = calls.as_slice() else {
            panic!("expected too-few, wrong-type, and too-many calls")
        };
        let mut context = context(&parsed, file);
        let too_few_callee =
            plan_direct_source_call_syntax(&parsed.arena, context.store(), *too_few)
                .unwrap()
                .callee();
        let parameter = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::Parameter)
                    .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let wrong_start = text.find("'x'").unwrap();
        let wrong_argument = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::StringLiteral
                    && record.range.start == TextPos::new(u32::try_from(wrong_start).unwrap()))
                .then(|| NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();

        context.check_source_file(file).unwrap();

        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            vec![2554, 2345, 2554]
        );
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics[0].node, Some(too_few_callee));
        assert_eq!(diagnostics[0].range_override, None);
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Expected 1 arguments, but got 0."
        );
        assert_eq!(diagnostics[0].related_information.len(), 1);
        assert_eq!(diagnostics[0].related_information[0].node, Some(parameter));
        assert_eq!(
            diagnostics[0].related_information[0]
                .diagnostic
                .render()
                .unwrap(),
            "An argument for 'value' was not provided."
        );
        assert_eq!(diagnostics[1].node, Some(wrong_argument));
        assert_eq!(diagnostics[1].range_override, None);
        assert_eq!(
            diagnostics[1].diagnostic.render().unwrap(),
            "Argument of type 'string' is not assignable to parameter of type 'number'."
        );
        let too_many_start = text.find("('extra'), true").unwrap();
        let too_many_end = too_many_start + "('extra'), true".len();
        assert_eq!(diagnostics[2].node, Some(calls[2]));
        assert_eq!(
            diagnostics[2].range_override,
            Some(CanonicalCheckerDiagnosticRange::new(
                calls[2],
                TextRange::new(
                    TextPos::new(u32::try_from(too_many_start).unwrap()),
                    TextPos::new(u32::try_from(too_many_end).unwrap()),
                ),
            ))
        );
        assert_eq!(
            diagnostics[2].diagnostic.render().unwrap(),
            "Expected 1 arguments, but got 3."
        );
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert!(calls.iter().all(|call| {
            context
                .store()
                .type_node_links(*call)
                .and_then(|links| links.resolved_type)
                == Some(string)
        }));
    }

    #[test]
    fn array_rest_calls_project_every_extra_argument_and_use_minimum_arity_diagnostic() {
        let library = parsed("interface Array<T> {}");
        let text = concat!(
            "function take(head: string, ...values: number[]): string { return head; } ",
            "const tooFew = take(); ",
            "const good = take('ok', 1, 2); ",
            "const wrong = take('ok', 1, 'bad');",
        );
        let parsed = parsed(text);
        let library_file = FileId::new(402);
        let file = FileId::new(403);
        let mut calls = calls(&parsed, file);
        calls.sort_by_key(|call| parsed.arena.get(call.node).unwrap().range.start);
        let [too_few, good, wrong] = calls.as_slice() else {
            panic!("expected too-few, applicable, and wrong-rest calls")
        };
        let mut context = context_with_default_library(&library, library_file, &parsed, file);

        context.check_source_file(file).unwrap();

        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            vec![2555, 2345]
        );
        assert_eq!(
            context.diagnostics().as_slice()[0]
                .diagnostic
                .render()
                .unwrap(),
            "Expected at least 1 arguments, but got 0."
        );
        assert_eq!(
            context.diagnostics().as_slice()[1]
                .diagnostic
                .render()
                .unwrap(),
            "Argument of type 'string' is not assignable to parameter of type 'number'."
        );
        for call in [too_few, good, wrong] {
            let return_type = context
                .store()
                .type_node_links(*call)
                .and_then(|links| links.resolved_type)
                .unwrap();
            assert_eq!(
                return_type,
                context.store().intrinsic_bootstrap().unwrap().string_type
            );
        }
    }

    #[test]
    fn initialized_parameter_is_omittable_but_keeps_its_body_value_type() {
        let parsed = parsed(concat!(
            "function defaulted(value: number = 1): number { return value; } ",
            "const omitted: number = defaulted(); ",
            "const explicitUndefined: number = defaulted(undefined); ",
            "const wrong: number = defaulted('bad');",
        ));
        let file = FileId::new(404);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(diagnostics[0].diagnostic.code(), 2345);
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Argument of type 'string' is not assignable to parameter of type 'number'."
        );
        let owner = first_function_symbol(&parsed, &context, file);
        let callable = context
            .store()
            .value_symbol_links(owner)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let provenance = context
            .store()
            .source_callable_provenance(callable)
            .unwrap();
        let signature = context.store().signature(provenance.signature).unwrap();
        assert_eq!(signature.min_argument_count(), 0);
        let parameter = signature.parameters()[0];
        assert_eq!(
            context
                .store()
                .value_symbol_links(parameter)
                .and_then(|links| links.resolved_type),
            Some(context.store().intrinsic_bootstrap().unwrap().number_type)
        );
    }

    #[test]
    fn direct_call_cache_poison_is_rejected_before_call_publication() {
        for poison_signature in [false, true] {
            let parsed = parsed(concat!(
                "function id(value: number): string { return 'ok'; } ",
                "const result = id(1);",
            ));
            let file = FileId::new(if poison_signature { 404 } else { 403 });
            let call_nodes = calls(&parsed, file);
            let [call] = call_nodes.as_slice() else {
                panic!("expected one direct call")
            };
            let call = *call;
            let mut context = context(&parsed, file);
            if poison_signature {
                assert!(context.store_mut_for_test().set_signature_links(
                    call,
                    SignatureLinks {
                        resolved_signature: ResolvedSignatureState::Resolving,
                        ..SignatureLinks::default()
                    },
                ));
            } else {
                assert!(context.store_mut_for_test().set_type_node_links(
                    call,
                    TypeNodeLinks {
                        outer_type_parameters: Some(Vec::new()),
                        ..TypeNodeLinks::default()
                    },
                ));
            }

            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::Call(call))
            );
            assert!(context.diagnostics().is_empty());
            let source = context.source_file(file).unwrap();
            assert!(
                !context
                    .store()
                    .source_file_links(source)
                    .is_some_and(|links| links.type_checked)
            );
            if poison_signature {
                assert_eq!(
                    context
                        .store()
                        .signature_links(call)
                        .unwrap()
                        .resolved_signature,
                    ResolvedSignatureState::Resolving
                );
                assert!(context.store().type_node_links(call).is_none());
            } else {
                assert!(context.store().signature_links(call).is_none());
                assert_eq!(
                    context
                        .store()
                        .type_node_links(call)
                        .unwrap()
                        .outer_type_parameters,
                    Some(Vec::new())
                );
            }
        }
    }

    #[test]
    fn direct_call_partial_warm_cache_is_rejected_without_writes() {
        for retain_type in [false, true] {
            let parsed = parsed(concat!(
                "function id(value: number): string { return 'ok'; } ",
                "const result = id(1);",
            ));
            let file = FileId::new(if retain_type { 438 } else { 437 });
            let call_nodes = calls(&parsed, file);
            let [call] = call_nodes.as_slice() else {
                panic!("expected one direct call")
            };
            let call = *call;
            let mut context = context(&parsed, file);
            context.check_source_file(file).unwrap();
            mark_source_unchecked(&mut context, file);
            if retain_type {
                assert!(
                    context
                        .store_mut_for_test()
                        .set_signature_links(call, SignatureLinks::default())
                );
            } else {
                assert!(
                    context
                        .store_mut_for_test()
                        .set_type_node_links(call, TypeNodeLinks::default())
                );
            }
            let poisoned = call_publication_state(&context, call);

            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::Call(call))
            );
            assert_eq!(call_publication_state(&context, call), poisoned);
            let source = context.source_file(file).unwrap();
            assert!(
                !context
                    .store()
                    .source_file_links(source)
                    .is_some_and(|links| links.type_checked)
            );
        }
    }

    #[test]
    fn nested_identifier_calls_publish_each_signature_and_return_type() {
        let parsed = parsed(concat!(
            "function number(value: number): number { return value; } ",
            "function text(value: number): string { return 'ok'; } ",
            "const result: string = text(number(number(1)));",
        ));
        let file = FileId::new(405);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        assert!(context.diagnostics().is_empty());
        let calls = calls(&parsed, file);
        assert_eq!(calls.len(), 3);
        for call in &calls {
            assert!(
                context
                    .store()
                    .signature_links(*call)
                    .and_then(|links| links.resolved_signature.signature())
                    .is_some()
            );
            assert!(
                context
                    .store()
                    .type_node_links(*call)
                    .and_then(|links| links.resolved_type)
                    .is_some()
            );
        }

        let warm_counts = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        );
        context.check_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
            ),
            warm_counts
        );
    }

    #[test]
    fn explicitly_instantiated_nongeneric_identifier_calls_fail_closed() {
        let parsed =
            parsed("function f(value: number): number { return 1; } const x = f<number>(1);");
        let file = FileId::new(406);
        let mut context = context(&parsed, file);
        assert!(matches!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Call(_)
            ))
        ));
    }

    #[test]
    fn unsupported_property_callable_families_never_publish_calls() {
        for (index, (text, reaches_property_execution)) in [
            (
                concat!(
                    "type API = { fn: <T>(value: T) => T }; ",
                    "function use(api: API): number { return api.fn(1); }",
                ),
                false,
            ),
            (
                concat!(
                    "function identity<T>(value: T): T { return value; } ",
                    "const api = { fn: identity }; const result = api.fn(1);",
                ),
                true,
            ),
            (
                concat!(
                    "type API = { fn: number }; ",
                    "function use(api: API): string { return api.fn(1); }",
                ),
                true,
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parsed(text);
            let file = FileId::new(444 + u32::try_from(index).unwrap());
            let call_nodes = calls(&parsed, file);
            let [call] = call_nodes.as_slice() else {
                panic!("expected one property call")
            };
            let call = *call;
            let access_nodes = property_accesses(&parsed, file);
            let [access] = access_nodes.as_slice() else {
                panic!("expected one property access")
            };
            let access = *access;
            let mut context = context(&parsed, file);

            let result = context.check_source_file(file);
            if reaches_property_execution {
                assert_eq!(result, Err(SourceCheckError::Call(call)));
            } else {
                assert!(result.is_err());
            }
            assert!(context.store().type_node_links(call).is_none());
            assert!(context.store().signature_links(call).is_none());
            assert_eq!(
                context
                    .store()
                    .type_node_links(access)
                    .and_then(|links| links.resolved_type)
                    .is_some(),
                reaches_property_execution
            );
            assert_eq!(
                context
                    .store()
                    .symbol_node_links(access)
                    .is_some_and(|links| links.resolved_symbol.is_some()),
                reaches_property_execution
            );
        }
    }
}
