//! New-expression adapter for the shared declared constructor-value provider.

use super::super::{
    constructor_values::{
        DeclaredConstructorValueError, DeclaredConstructorValuePlan,
        plan_declared_constructor_value, prepare_declared_construct_signature,
        resolve_declared_construct_signature,
    },
    instantiate::InstantiationSession,
    object_members::PropertyObjectError,
};
use super::{
    CanonicalCheckerDiagnostics, CanonicalCheckerOptions, CanonicalGlobalTypes,
    CanonicalTypeMapperStore, CheckedSourceDefaultNew, DeclaredTypeHost, NodeData, NodeRef,
    SemanticSymbolId, SourceDefaultNewPlan, SourceNewArgument, SourceNewArgumentValue,
    SourceNewError, SourceNewInvariant, SourceNewParameter, SourceNewUnsupported, SymbolFlags,
    SyntaxKind, argument_matches_parameter, invariant, unsupported,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DeclaredConstructorPlan {
    value: DeclaredConstructorValuePlan,
    declaration: NodeRef,
    pub(super) parameter: Option<SourceNewParameter>,
}

pub(super) fn provider_error(
    constructor: NodeRef,
    symbol: SemanticSymbolId,
    error: DeclaredConstructorValueError,
) -> SourceNewError {
    match error {
        DeclaredConstructorValueError::DeclaredType(error) => error.into(),
        DeclaredConstructorValueError::Capacity(node)
        | DeclaredConstructorValueError::Members(PropertyObjectError::Capacity(node)) => {
            invariant(SourceNewInvariant::Capacity(node))
        }
        DeclaredConstructorValueError::Unsupported { .. }
        | DeclaredConstructorValueError::Members(PropertyObjectError::UnsupportedMember {
            ..
        }) => unsupported(SourceNewUnsupported::ConstructorClass {
            node: constructor,
            symbol,
        }),
        DeclaredConstructorValueError::InvalidValue(_)
        | DeclaredConstructorValueError::InvalidSignature(_)
        | DeclaredConstructorValueError::Members(_) => {
            invariant(SourceNewInvariant::InvalidConstructorCache(constructor))
        }
    }
}

/// Keeps existing type-literal, alias, union, and class routes outside this adapter.
pub(super) fn is_named_interface_value(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    symbol: SemanticSymbolId,
) -> bool {
    let Some(value) = store.symbol(symbol) else {
        return false;
    };
    if !value
        .flags()
        .intersects(SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::BLOCK_SCOPED_VARIABLE)
    {
        return false;
    }
    let Some(declaration) = value.value_declaration() else {
        return false;
    };
    let Some(NodeData::VariableDeclaration(variable)) =
        host.node(declaration).map(|node| &node.data)
    else {
        return false;
    };
    let Some(annotation) = variable
        .type_
        .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
    else {
        return false;
    };
    let Some(NodeData::TypeReferenceNode(reference)) = host.node(annotation).map(|node| &node.data)
    else {
        return false;
    };
    host.name_resolver_host(store)
        .ok()
        .and_then(|mut resolver| {
            resolver
                .resolve_entity_name(
                    NodeRef::new(annotation.arena, annotation.file, reference.type_name),
                    SymbolFlags::TYPE,
                )
                .ok()
                .flatten()
        })
        .and_then(|symbol| store.get_merged_symbol(symbol))
        .and_then(|symbol| store.symbol(symbol))
        .is_some_and(|owner| owner.flags().contains(SymbolFlags::INTERFACE))
}

/// Applies the admitted primitive-argument overload selection to real source signatures.
pub(super) fn plan(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    constructor: NodeRef,
    symbol: SemanticSymbolId,
    argument: Option<&SourceNewArgument>,
) -> Result<DeclaredConstructorPlan, SourceNewError> {
    let value = plan_declared_constructor_value(store, host, symbol)
        .map_err(|error| provider_error(constructor, symbol, error))?;
    let invalid = || invariant(SourceNewInvariant::InvalidConstructorCache(constructor));
    let mut candidates = Vec::with_capacity(value.construct_declarations().len());
    let mut last_parent = None;
    let mut last_symbol = None;
    let mut index = 0;
    let mut cutoff_index = 0;
    let mut specialized_count = 0;
    for declaration in value.construct_declarations() {
        let parent = host
            .node(declaration)
            .and_then(|node| node.parent)
            .map(|node| NodeRef::new(declaration.arena, declaration.file, node))
            .ok_or_else(invalid)?;
        let symbol = store
            .source_declaration_symbol(declaration)
            .ok_or_else(invalid)?;
        if last_symbol.is_none() || last_symbol == Some(symbol) {
            if last_parent == Some(parent) {
                index += 1;
            } else {
                last_parent = Some(parent);
                index = cutoff_index;
            }
        } else {
            index = candidates.len();
            cutoff_index = candidates.len();
            last_parent = Some(parent);
        }
        last_symbol = Some(symbol);
        let Some(NodeData::ConstructSignatureDeclaration(signature)) =
            host.node(declaration).map(|node| &node.data)
        else {
            return Err(invalid());
        };
        let specialized = signature.parameters.nodes.iter().any(|&node| {
            let parameter = NodeRef::new(declaration.arena, declaration.file, node);
            store
                .source_direct_type_annotation(parameter)
                .is_some_and(|annotation| {
                    store.source_node_kind(annotation) == Some(SyntaxKind::LiteralType)
                })
        });
        let insertion_index = if specialized {
            let insertion_index = specialized_count;
            specialized_count += 1;
            cutoff_index += 1;
            insertion_index
        } else {
            index
        };
        candidates.insert(insertion_index, declaration);
    }
    for declaration in candidates {
        let Some(NodeData::ConstructSignatureDeclaration(signature)) =
            host.node(declaration).map(|node| &node.data)
        else {
            return Err(invalid());
        };
        let minimum = signature.parameters.nodes.iter().position(|&node| {
            let parameter = NodeRef::new(declaration.arena, declaration.file, node);
            matches!(host.node(parameter).map(|node| &node.data), Some(NodeData::ParameterDeclaration(parameter)) if parameter.question_token.is_some())
        }).unwrap_or(signature.parameters.nodes.len());
        let supplied = usize::from(argument.is_some());
        if supplied < minimum || supplied > signature.parameters.nodes.len() {
            continue;
        }
        let parameter = if let Some(argument) = argument {
            let declaration = NodeRef::new(
                declaration.arena,
                declaration.file,
                signature.parameters.nodes[0],
            );
            let parameter_symbol = host
                .bound_file(declaration)
                .and_then(|bound| bound.symbol(declaration))
                .ok_or_else(invalid)?;
            let annotation = store
                .source_direct_type_annotation(declaration)
                .ok_or_else(invalid)?;
            let Some(parameter) =
                argument_parameter(store, host, argument, parameter_symbol, annotation)?
            else {
                continue;
            };
            Some(parameter)
        } else {
            None
        };
        return Ok(DeclaredConstructorPlan {
            value,
            declaration,
            parameter,
        });
    }
    Err(unsupported(SourceNewUnsupported::Arguments(constructor)))
}

fn argument_parameter(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    argument: &SourceNewArgument,
    symbol: SemanticSymbolId,
    annotation: NodeRef,
) -> Result<Option<SourceNewParameter>, SourceNewError> {
    let invalid = || invariant(SourceNewInvariant::InvalidConstructorCache(annotation));
    let record = host.node(annotation).ok_or_else(invalid)?;
    let bootstrap = store.intrinsic_bootstrap().ok_or_else(invalid)?;
    let type_ = match record.kind {
        SyntaxKind::StringKeyword => bootstrap.string_type,
        SyntaxKind::NumberKeyword => bootstrap.number_type,
        SyntaxKind::BooleanKeyword => bootstrap.boolean_type,
        SyntaxKind::AnyKeyword => bootstrap.any_type,
        SyntaxKind::UnknownKeyword => bootstrap.unknown_type,
        SyntaxKind::LiteralType => {
            let NodeData::LiteralTypeNode(literal) = &record.data else {
                return Err(invalid());
            };
            let literal = host
                .node(NodeRef::new(
                    annotation.arena,
                    annotation.file,
                    literal.literal,
                ))
                .ok_or_else(invalid)?;
            match (&argument.value, &literal.data) {
                (SourceNewArgumentValue::String(value), NodeData::StringLiteral(literal))
                    if value == &literal.text =>
                {
                    bootstrap.string_type
                }
                (SourceNewArgumentValue::Number(value), NodeData::NumericLiteral(literal))
                    if *value == ts_jsnum::from_string(&literal.text) =>
                {
                    bootstrap.number_type
                }
                (SourceNewArgumentValue::Boolean(value), NodeData::KeywordExpression(_))
                    if literal.kind
                        == if *value {
                            SyntaxKind::TrueKeyword
                        } else {
                            SyntaxKind::FalseKeyword
                        } =>
                {
                    bootstrap.boolean_type
                }
                _ => return Ok(None),
            }
        }
        _ => return Err(unsupported(SourceNewUnsupported::Arguments(argument.node))),
    };
    let parameter = SourceNewParameter { symbol, type_ };
    Ok(argument_matches_parameter(store, argument, parameter).then_some(parameter))
}

pub(super) fn resolve(
    store: &CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    plan: &SourceDefaultNewPlan,
    declared: &DeclaredConstructorPlan,
) -> Result<Option<CheckedSourceDefaultNew>, SourceNewError> {
    resolve_declared_construct_signature(store, host, &declared.value, declared.declaration)
        .map_err(|error| provider_error(plan.constructor, plan.resolved_symbol, error))?
        .map(|signature| {
            if signature.value().value_symbol() != plan.resolved_symbol
                || signature.declaration() != declared.declaration
            {
                return Err(invariant(SourceNewInvariant::InvalidConstructorCache(
                    plan.constructor,
                )));
            }
            Ok(CheckedSourceDefaultNew {
                value_type: signature.value().constructor_type(),
                instance_type: signature.return_type(),
                signature: signature.signature(),
            })
        })
        .transpose()
}

#[allow(clippy::too_many_arguments)] // The expression adapter borrows its caller's query context.
pub(super) fn prepare(
    store: &mut CanonicalTypeMapperStore,
    host: &DeclaredTypeHost<'_>,
    globals: &CanonicalGlobalTypes,
    options: CanonicalCheckerOptions,
    session: &mut InstantiationSession,
    diagnostics: &mut CanonicalCheckerDiagnostics,
    plan: &SourceDefaultNewPlan,
    declared: &DeclaredConstructorPlan,
) -> Result<(), SourceNewError> {
    prepare_declared_construct_signature(
        store,
        host,
        globals,
        options,
        session,
        diagnostics,
        &declared.value,
        declared.declaration,
    )
    .map(|_| ())
    .map_err(|error| provider_error(plan.constructor, plan.resolved_symbol, error))
}

#[cfg(test)]
mod tests {
    use ts_ast::FileId;
    use ts_binder::{
        CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
        EscapedName,
    };
    use ts_parser::parse_source_file;

    use super::*;
    use crate::semantic::CanonicalCheckerContext;

    #[test]
    fn merged_specialized_constructors_keep_provider_order_before_general_candidates() {
        for (index, (source, expected_declarations)) in [
            (
                "interface Factory { new(value: \"x\"): \"first\"; } interface Factory { new(value: \"x\"): \"second\"; } declare const Build: Factory; const result = new Build(\"x\");",
                vec![0],
            ),
            (
                concat!(
                    "interface Factory { new(value: \"x\"): \"first-special\"; new(value: string): \"first-general\"; } ",
                    "interface Factory { new(value: \"x\"): \"second-special\"; new(value: string): \"second-general\"; } ",
                    "declare const Build: Factory; const special = new Build(\"x\"); const general = new Build(\"other\");",
                ),
                vec![0, 3],
            ),
            (
                concat!(
                    "interface Factory { new(value: string): \"first-general\"; new(value: \"x\"): \"first-special\"; } ",
                    "interface Factory { new(value: string): \"second-general\"; new(value: \"x\"): \"second-special\"; } ",
                    "declare const Build: Factory; const special = new Build(\"x\"); const general = new Build(\"other\");",
                ),
                vec![1, 2],
            ),
        ].into_iter().enumerate() {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(9_780 + u32::try_from(index).unwrap());
            let mut binder = CanonicalBinder::new();
            binder.bind_source_file_with_facts(
                &parsed.arena, parsed.source_file, file,
                CanonicalSourceFileFacts::new(EscapedName::source("\"/merged-constructors.ts\""), CanonicalSourceLanguage::TypeScript, false, CanonicalModuleState::Script),
            ).unwrap();
            binder.bind_typescript_declaration_slice(&parsed.arena, file).unwrap();
            let mut context = CanonicalCheckerContext::new(binder.finish(), vec![(file, &parsed.arena)], CanonicalCheckerOptions::default()).unwrap();
            let declarations = parsed.arena.iter().filter_map(|(node, record)| {
                (record.kind == SyntaxKind::ConstructSignature).then_some(NodeRef::new(parsed.arena.id(), file, node))
            }).collect::<Vec<_>>();
            let expressions = parsed.arena.iter().filter_map(|(node, record)| {
                (record.kind == SyntaxKind::NewExpression).then_some(NodeRef::new(parsed.arena.id(), file, node))
            }).collect::<Vec<_>>();
            assert_eq!(expressions.len(), expected_declarations.len());
            context.check_source_file(file).unwrap();
            for (expression, expected) in expressions.iter().zip(expected_declarations) {
                let signature = context.store().signature_links(*expression).unwrap().resolved_signature.signature().unwrap();
                assert_eq!(context.store().signature(signature).unwrap().declaration(), Some(declarations[expected]), "{source}");
                let annotation = context.store().source_direct_type_annotation(declarations[expected]).unwrap();
                let expected_return = context.get_type_from_type_node(annotation).unwrap();
                assert_eq!(context.store().type_node_links(*expression).unwrap().resolved_type, Some(expected_return));
            }
            assert!(context.diagnostics().is_empty());
            let warm = (context.store().type_len(), context.store().signature_len(), context.store().checker_link_allocated_lengths());
            context.recheck_source_file(file).unwrap();
            assert_eq!((context.store().type_len(), context.store().signature_len(), context.store().checker_link_allocated_lengths()), warm);
            assert!(context.diagnostics().is_empty());
        }
    }
}
