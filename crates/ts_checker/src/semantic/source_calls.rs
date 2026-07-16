//! Exact source integration for one ordinary identifier call.
//!
//! This deliberately admits only `identifier(arguments)` where every argument
//! is a context-insensitive scalar or identifier, optionally parenthesized.
//! The semantic kernel remains in `calls`; this module owns the AST proof,
//! lazy-return/relation retries, call caches, and source diagnostics.

use std::collections::HashSet;

use ts_ast::{NodeArena, NodeData, NodeRef, SyntaxKind};
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
        resolve_identity_generic_call,
    },
    source::{
        PlannedExpression, PlannedExpressionKind, SourceCheckError, UnsupportedSourceSyntax,
        merge_retry_diagnostic, merge_retry_diagnostics,
    },
    type_nodes::CanonicalTypeQuery,
};

/// Fully proven syntax plus source-planned callee and arguments.
#[derive(Clone, Debug)]
pub(super) struct SourceCallPlan {
    pub(super) node: NodeRef,
    pub(super) callee: PlannedExpression,
    pub(super) type_arguments: Option<Vec<NodeRef>>,
    pub(super) arguments: Vec<PlannedExpression>,
}

#[derive(Clone, Debug)]
pub(super) struct DirectSourceCallSyntax {
    node: NodeRef,
    callee: NodeRef,
    type_arguments: Option<Vec<NodeRef>>,
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
            if type_arguments.nodes.is_empty()
                || type_arguments.range.start < record.range.start
                || type_arguments.range.end > record.range.end
            {
                return Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Call(node),
                ));
            }
            type_arguments
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
                .collect::<Result<Vec<_>, _>>()
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

pub(super) fn finish_direct_source_call_plan(
    syntax: &DirectSourceCallSyntax,
    callee: PlannedExpression,
    arguments: Vec<PlannedExpression>,
) -> Result<SourceCallPlan, SourceCheckError> {
    if !matches!(callee.kind, PlannedExpressionKind::Identifier(_))
        || arguments.len() != syntax.arguments.len()
        || !arguments.iter().all(is_context_insensitive_argument_plan)
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
        PlannedExpressionKind::Assertion { .. }
        | PlannedExpressionKind::Array(_)
        | PlannedExpressionKind::Object { .. }
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
    match resolve_identity_generic_call(store, global_types, options.strict_function_types, request)
    {
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
        plan.type_arguments.as_deref(),
    )?;
    let mut retried_signatures = HashSet::new();
    let resolution = loop {
        match resolve_source_call_once(
            store,
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
        EscapedName,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{CanonicalCheckerContext, SourceFileLinks};

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

    fn calls(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
        parsed
            .arena
            .iter()
            .filter(|(_, record)| record.kind == SyntaxKind::CallExpression)
            .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
            .collect()
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
