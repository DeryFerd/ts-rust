//! Exact source integration for one ordinary identifier call.
//!
//! This deliberately admits only `identifier(arguments)` where every argument
//! is a context-insensitive scalar, identifier, property read, or recursively
//! proven primitive binary expression, optionally parenthesized.
//! The semantic kernel remains in `calls`; this module owns the AST proof,
//! lazy-return/relation retries, call caches, and source diagnostics.

use std::collections::HashSet;

use ts_ast::{NodeArena, NodeData, NodeRef, SyntaxKind};
use ts_core::{TextPos, TextRange};
use ts_diagnostics::{Diagnostic, message_by_code};

use super::{
    CanonicalCheckerDiagnostic, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    CanonicalGlobalTypes, CanonicalTypeFormatFlags, CanonicalTypeMapperStore, DeclaredTypeHost,
    RelationUnavailable, ResolvedSignatureState, SignatureId, SignatureLinks, TypeId,
    TypeNodeLinks,
    calls::{
        DirectCallApplicability, DirectCallError, DirectCallForm, DirectCallRequest,
        DirectCallUnsupported, resolve_direct_call,
    },
    formatter::get_type_names_for_assignability_error_with_host_global_types_and_flags,
    generic_calls::{
        IdentityGenericCallError, IdentityGenericCallRequest, IdentityGenericCallUnsupported,
        resolve_source_identity_generic_call,
    },
    source::{
        PlannedExpression, PlannedExpressionKind, SourceCheckError, UnsupportedSourceSyntax,
        merge_retry_diagnostic, merge_retry_diagnostics, primitive_binary_operator_text,
    },
    type_nodes::CanonicalTypeQuery,
};

/// Fully proven syntax plus source-planned callee and arguments.
#[derive(Clone, Debug)]
pub(super) struct SourceCallPlan {
    pub(super) node: NodeRef,
    pub(super) callee: PlannedExpression,
    type_arguments: Option<SourceTypeArgumentList>,
    pub(super) arguments: Vec<PlannedExpression>,
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
#[allow(dead_code)] // Exact ranges are consumed by the next generic diagnostic slice.
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
    type_arguments: Option<SourceTypeArgumentList>,
    arguments: Vec<NodeRef>,
}

impl DirectSourceCallSyntax {
    pub(super) fn callee(&self) -> NodeRef {
        self.callee
    }

    pub(super) fn arguments(&self) -> &[NodeRef] {
        &self.arguments
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CheckedSourceCall {
    pub(super) return_type: TypeId,
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
    if callee_record.parent != Some(node.node) || callee_record.kind != SyntaxKind::Identifier {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(node),
        ));
    }

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
            let diagnostic_range = if let (Some(first), Some(last)) = (nodes.first(), nodes.last()) {
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
                diagnostic_end.map(|diagnostic_end| {
                    TextRange::new(first_range.start, diagnostic_end)
                })
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
            || !is_context_insensitive_argument_syntax(arena, argument)
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
            offset += remaining
                .find(['\r', '\n'])
                .unwrap_or(remaining.len());
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
    if callee.node != syntax.callee
        || !matches!(callee.kind, PlannedExpressionKind::Identifier(_))
        || arguments.len() != syntax.arguments.len()
        || !arguments
            .iter()
            .zip(&syntax.arguments)
            .all(|(argument, syntax_node)| {
                argument.node == *syntax_node && is_context_insensitive_argument_plan(argument)
            })
    {
        return Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Call(syntax.node),
        ));
    }
    Ok(SourceCallPlan {
        node: syntax.node,
        callee,
        type_arguments: syntax.type_arguments.clone(),
        arguments,
    })
}

fn is_context_insensitive_argument_syntax(arena: &NodeArena, node: NodeRef) -> bool {
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
                        && is_context_insensitive_argument_syntax(arena, inner)
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
        SyntaxKind::BinaryExpression => is_context_insensitive_primitive_binary_syntax(arena, node),
        _ => false,
    }
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
        SyntaxKind::BinaryExpression => is_context_insensitive_primitive_binary_syntax(arena, node),
        _ => false,
    }
}

fn is_context_insensitive_argument_plan(expression: &PlannedExpression) -> bool {
    match &expression.kind {
        PlannedExpressionKind::Null
        | PlannedExpressionKind::String(_)
        | PlannedExpressionKind::Number { .. }
        | PlannedExpressionKind::BigInt { .. }
        | PlannedExpressionKind::Boolean(_)
        | PlannedExpressionKind::GlobalUndefined
        | PlannedExpressionKind::Identifier(_)
        | PlannedExpressionKind::Property(_) => true,
        PlannedExpressionKind::Parenthesized(inner) => is_context_insensitive_argument_plan(inner),
        PlannedExpressionKind::Binary(binary) => {
            let (left, right) = binary.operands();
            binary.node() == expression.node
                && primitive_binary_operator_text(binary.operator()).is_some()
                && is_context_insensitive_primitive_binary_operand_plan(left)
                && is_context_insensitive_primitive_binary_operand_plan(right)
        }
        PlannedExpressionKind::Assertion { .. }
        | PlannedExpressionKind::TypeImportValueUse(_)
        | PlannedExpressionKind::Array(_)
        | PlannedExpressionKind::Object { .. }
        | PlannedExpressionKind::Call(_) => false,
    }
}

fn is_context_insensitive_primitive_binary_operand_plan(expression: &PlannedExpression) -> bool {
    match &expression.kind {
        PlannedExpressionKind::String(_)
        | PlannedExpressionKind::Number { .. }
        | PlannedExpressionKind::BigInt { .. }
        | PlannedExpressionKind::Boolean(_)
        | PlannedExpressionKind::Identifier(_) => true,
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
        PlannedExpressionKind::Null
        | PlannedExpressionKind::GlobalUndefined
        | PlannedExpressionKind::TypeImportValueUse(_)
        | PlannedExpressionKind::Assertion { .. }
        | PlannedExpressionKind::Array(_)
        | PlannedExpressionKind::Object { .. }
        | PlannedExpressionKind::Property(_)
        | PlannedExpressionKind::Call(_) => false,
    }
}

fn preflight_call_links(
    store: &CanonicalTypeMapperStore,
    node: NodeRef,
) -> Result<(), SourceCheckError> {
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
    }
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
    }
    Ok(())
}

/// Resolves one already-typed source call, retrying the two lazy semantic
/// boundaries before publishing its exact signature/return caches.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ResolvedSourceCall {
    signature: SignatureId,
    return_type: TypeId,
    minimum_argument_count: usize,
    maximum_argument_count: usize,
    applicability: DirectCallApplicability,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceCallResolutionError {
    Retry(SignatureId),
    Relation(RelationUnavailable),
    Unsupported,
}

fn resolve_source_call_once(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    callee_type: TypeId,
    argument_types: &[TypeId],
    explicit_type_arguments: Option<&[TypeId]>,
) -> Result<ResolvedSourceCall, SourceCallResolutionError> {
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
                return Ok(ResolvedSourceCall {
                    signature: resolution.projection.signature,
                    return_type: resolution.projection.return_type,
                    minimum_argument_count: resolution.projection.minimum_argument_count,
                    maximum_argument_count: resolution.projection.maximum_argument_count,
                    applicability: resolution.applicability,
                });
            }
            Err(DirectCallError::Unsupported(DirectCallUnsupported::GenericSignature(_))) => {}
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
            Err(DirectCallError::Unsupported(_) | DirectCallError::Invariant(_)) => {
                return Err(SourceCallResolutionError::Unsupported);
            }
        }
    }

    let request = IdentityGenericCallRequest {
        form: DirectCallForm::Call,
        optional_chain: false,
        explicit_type_arguments,
        has_spread_argument: false,
        callee: callee_type,
        arguments: argument_types,
    };
    match resolve_source_identity_generic_call(
        store,
        host,
        global_types,
        options.strict_function_types,
        request,
    ) {
        Ok(resolution) => Ok(ResolvedSourceCall {
            signature: resolution.projection.signature,
            return_type: resolution.projection.return_type,
            minimum_argument_count: 1,
            maximum_argument_count: 1,
            applicability: resolution.applicability,
        }),
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
            | IdentityGenericCallError::Invariant(_)
            | IdentityGenericCallError::Inference(_),
        ) => Err(SourceCallResolutionError::Unsupported),
    }
}

#[allow(clippy::too_many_arguments)]
fn resolve_explicit_source_type_arguments(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
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
        let mut query = CanonicalTypeQuery::new_with_global_types(
            store,
            host,
            global_types,
            options,
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

#[allow(clippy::too_many_arguments)]
pub(super) fn check_direct_source_call(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &SourceCallPlan,
    callee_type: TypeId,
    argument_types: &[TypeId],
) -> Result<CheckedSourceCall, SourceCheckError> {
    let explicit_type_arguments = resolve_explicit_source_type_arguments(
        store,
        host,
        global_types,
        options,
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
            callee_type,
            argument_types,
            explicit_type_arguments.as_deref(),
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
            Err(SourceCallResolutionError::Retry(_) | SourceCallResolutionError::Unsupported) => {
                return Err(SourceCheckError::Call(plan.node));
            }
        }
    };

    publish_call_links(
        store,
        plan.node,
        resolution.signature,
        resolution.return_type,
    )?;
    match resolution.applicability {
        DirectCallApplicability::Applicable => {}
        DirectCallApplicability::TooFewArguments { actual, .. }
        | DirectCallApplicability::TooManyArguments { actual, .. } => {
            let expected = if resolution.minimum_argument_count == resolution.maximum_argument_count
            {
                resolution.minimum_argument_count.to_string()
            } else {
                format!(
                    "{}-{}",
                    resolution.minimum_argument_count, resolution.maximum_argument_count
                )
            };
            merge_retry_diagnostic(
                diagnostics,
                CanonicalCheckerDiagnostic {
                    node: Some(plan.node),
                    range_override: None,
                    diagnostic: Diagnostic::with_arguments(
                        message_by_code(2554).ok_or(SourceCheckError::MissingDiagnostic(2554))?,
                        [expected, actual.to_string()],
                    ),
                    related_information: Vec::new(),
                },
            );
        }
        DirectCallApplicability::ArgumentNotAssignable {
            index,
            argument_type,
            parameter_type,
        } => {
            let mut flags = CanonicalTypeFormatFlags::TYPE_TO_STRING_DEFAULT;
            if options.no_error_truncation {
                flags |= CanonicalTypeFormatFlags::NO_TRUNCATION;
            }
            let display = get_type_names_for_assignability_error_with_host_global_types_and_flags(
                store,
                host,
                global_types,
                argument_type,
                parameter_type,
                flags,
            )?;
            let argument = plan
                .arguments
                .get(index)
                .ok_or(SourceCheckError::Call(plan.node))?;
            merge_retry_diagnostic(
                diagnostics,
                CanonicalCheckerDiagnostic {
                    node: Some(argument.node),
                    range_override: None,
                    diagnostic: Diagnostic::with_arguments(
                        message_by_code(2345).ok_or(SourceCheckError::MissingDiagnostic(2345))?,
                        [display.source, display.target],
                    ),
                    related_information: Vec::new(),
                },
            );
        }
    }
    Ok(CheckedSourceCall {
        return_type: resolution.return_type,
    })
}

#[allow(clippy::too_many_arguments)]
fn resolve_signature_return(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    global_types: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    signature: super::SignatureId,
) -> Result<(), SourceCheckError> {
    let mut resolution_diagnostics = CanonicalCheckerDiagnostics::default();
    let result = CanonicalTypeQuery::new_with_global_types(
        store,
        host,
        global_types,
        options,
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
    if store
        .type_node_links(node)
        .is_some_and(|links| links != &TypeNodeLinks::default() && links != &expected_type)
        || store.signature_links(node).is_some_and(|links| {
            links != &SignatureLinks::default() && links != &expected_signature
        })
    {
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
        let parsed = parsed(concat!(
            "function take(value: number): string { return 'ok'; } ",
            "const tooFew = take(); ",
            "const wrong = take('x');",
        ));
        let file = FileId::new(402);
        let calls = calls(&parsed, file);
        let mut context = context(&parsed, file);

        context.check_source_file(file).unwrap();

        assert_eq!(
            context
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| diagnostic.diagnostic.code())
                .collect::<Vec<_>>(),
            vec![2554, 2345]
        );
        assert_eq!(
            context.diagnostics().as_slice()[0]
                .diagnostic
                .render()
                .unwrap(),
            "Expected 1 arguments, but got 0."
        );
        assert_eq!(
            context.diagnostics().as_slice()[1]
                .diagnostic
                .render()
                .unwrap(),
            "Argument of type 'string' is not assignable to parameter of type 'number'."
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
    fn nested_and_non_identifier_calls_fail_closed() {
        for (index, text) in [
            "function f(value: number): number { return 1; } const x = f(f(1));",
            "const object = { f: 1 }; const x = object.f(1);",
            "function f(value: number): number { return 1; } const x = f<number>(1);",
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parsed(text);
            let file = FileId::new(405 + u32::try_from(index).unwrap());
            let mut context = context(&parsed, file);
            assert!(matches!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Call(_)
                ))
            ));
        }
    }
}
