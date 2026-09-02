use ts_ast::{FileId, NodeData, NodeRef};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, IntrinsicBootstrapOptions,
    SignatureId, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const CONSUMER: FileId = FileId::new(8_390);
const PROVIDER: FileId = FileId::new(8_391);
const LEGAL: &str = concat!(
    "import type * as path from './provider';\n",
    "export const normalize: typeof path.normalize = function(path: string) {\n",
    "  return path;\n",
    "};\n",
    "const result = normalize('ok');\n",
);
const PROVIDER_TEXT: &str = "export function normalize(path: string): string { return path; }\n";

fn context<'arena>(
    consumer: &'arena ParseResult,
    provider: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (CONSUMER, consumer, "\"/project/consumer.ts\""),
        (PROVIDER, provider, "\"/project/provider.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, name) in &files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(name),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::External,
                ),
            )
            .unwrap();
    }
    for &(file, parsed, _) in &files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    let specifiers = consumer
        .arena
        .iter()
        .filter_map(|(_, record)| match &record.data {
            NodeData::ImportDeclaration(import) => Some(import.module_specifier),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(specifiers.len(), 1);
    CanonicalCheckerContext::new_with_module_resolutions(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            no_implicit_any: true,
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            NodeRef::new(consumer.arena.id(), CONSUMER, specifiers[0]),
            CanonicalResolvedModuleInput::new(
                PROVIDER,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap()
}

fn variable(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                (
                    NodeRef::new(parsed.arena.id(), CONSUMER, id),
                    NodeRef::new(parsed.arena.id(), CONSUMER, variable.name),
                    NodeRef::new(parsed.arena.id(), CONSUMER, variable.initializer.unwrap()),
                )
            })
        })
        .unwrap()
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(node.file).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

struct Nodes {
    import: NodeRef,
    import_name: NodeRef,
    binding: NodeRef,
    binding_name: NodeRef,
    query: NodeRef,
    query_receiver: NodeRef,
    expression: NodeRef,
    parameter: NodeRef,
    parameter_name: NodeRef,
    call: NodeRef,
    provider_module: NodeRef,
    provider_function: NodeRef,
    provider_parameter: NodeRef,
    runtime: Option<(NodeRef, NodeRef)>,
}

fn nodes(consumer: &ParseResult, provider: &ParseResult, runtime: bool) -> Nodes {
    let (binding, binding_name, expression) = variable(consumer, "normalize");
    let (_, _, call) = variable(consumer, "result");
    let NodeData::VariableDeclaration(variable) = &consumer.arena.get(binding.node).unwrap().data
    else {
        unreachable!();
    };
    let query = NodeRef::new(consumer.arena.id(), CONSUMER, variable.type_.unwrap());
    assert_eq!(
        consumer.arena.get(query.node).unwrap().parent,
        Some(binding.node)
    );
    let NodeData::TypeQueryNode(query_data) = &consumer.arena.get(query.node).unwrap().data else {
        panic!("the annotation must remain a real type query");
    };
    let qualified = consumer.arena.get(query_data.expr_name).unwrap();
    assert_eq!(qualified.parent, Some(query.node));
    let NodeData::QualifiedName(qualified) = &qualified.data else {
        panic!("the type query must retain its qualified name");
    };
    let query_receiver = NodeRef::new(consumer.arena.id(), CONSUMER, qualified.left);
    let NodeData::FunctionExpression(function) = &consumer.arena.get(expression.node).unwrap().data
    else {
        panic!("expected the actual consumer function expression");
    };
    assert_eq!(function.parameters.nodes.len(), 1);
    let parameter = NodeRef::new(consumer.arena.id(), CONSUMER, function.parameters.nodes[0]);
    assert_eq!(
        consumer.arena.get(parameter.node).unwrap().parent,
        Some(expression.node)
    );
    let NodeData::ParameterDeclaration(parameter_data) =
        &consumer.arena.get(parameter.node).unwrap().data
    else {
        unreachable!();
    };
    let parameter_name = NodeRef::new(consumer.arena.id(), CONSUMER, parameter_data.name);
    let (import, import_name) = consumer
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::NamespaceImport(import) = &record.data else {
                return None;
            };
            Some((
                NodeRef::new(consumer.arena.id(), CONSUMER, id),
                NodeRef::new(consumer.arena.id(), CONSUMER, import.name),
            ))
        })
        .unwrap();
    let provider_function = provider
        .arena
        .iter()
        .find_map(|(id, record)| {
            matches!(record.data, NodeData::FunctionDeclaration(_)).then_some(NodeRef::new(
                provider.arena.id(),
                PROVIDER,
                id,
            ))
        })
        .unwrap();
    let NodeData::FunctionDeclaration(function) =
        &provider.arena.get(provider_function.node).unwrap().data
    else {
        unreachable!();
    };
    assert!(function.type_.is_some());
    assert_eq!(function.parameters.nodes.len(), 1);
    let provider_parameter =
        NodeRef::new(provider.arena.id(), PROVIDER, function.parameters.nodes[0]);
    let runtime = runtime.then(|| {
        let (_, _, property) = variable(consumer, "rejected");
        let NodeData::PropertyAccessExpression(access) =
            &consumer.arena.get(property.node).unwrap().data
        else {
            panic!("the rejected value use must be an actual property read");
        };
        let receiver = NodeRef::new(consumer.arena.id(), CONSUMER, access.expression);
        assert_eq!(
            consumer.arena.get(receiver.node).unwrap().parent,
            Some(property.node)
        );
        (property, receiver)
    });
    Nodes {
        import,
        import_name,
        binding,
        binding_name,
        query,
        query_receiver,
        expression,
        parameter,
        parameter_name,
        call,
        provider_module: NodeRef::new(provider.arena.id(), PROVIDER, provider.source_file),
        provider_function,
        provider_parameter,
        runtime,
    }
}

fn assert_alias(checker: &CanonicalCheckerContext<'_>, nodes: &Nodes) {
    let alias = symbol(checker, nodes.import);
    let module = symbol(checker, nodes.provider_module);
    let provider = symbol(checker, nodes.provider_function);
    for other in [
        module,
        provider,
        symbol(checker, nodes.parameter),
        symbol(checker, nodes.provider_parameter),
    ] {
        assert_ne!(alias, other);
    }
    let record = checker.store().symbol(module).unwrap();
    assert_eq!(record.flags(), SymbolFlags::VALUE_MODULE);
    assert_eq!(record.declarations(), Some(&[nodes.provider_module][..]));
    assert_eq!(record.value_declaration(), Some(nodes.provider_module));
    assert_eq!(
        checker.store().symbol(provider).unwrap().parent(),
        Some(module)
    );
    let links = checker.store().alias_symbol_links(alias).unwrap();
    assert_eq!(links.immediate_target, Some(module));
    assert_eq!(links.alias_target.symbol(), Some(module));
    assert_eq!(links.type_only_declaration, Some(nodes.import));
    assert!(!links.referenced);
    if let Some(type_) = checker
        .store()
        .value_symbol_links(alias)
        .and_then(|links| links.resolved_type)
    {
        assert_eq!(
            checker.store().type_payload(type_).unwrap().symbol(),
            Some(module)
        );
    }
}

fn assert_diagnostics(checker: &CanonicalCheckerContext<'_>, nodes: &Nodes) {
    let diagnostics = checker.diagnostics().as_slice();
    let Some((_, receiver)) = nodes.runtime else {
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
        return;
    };
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    let diagnostic = &diagnostics[0];
    assert_eq!(diagnostic.node, Some(receiver));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(diagnostic.diagnostic.code(), 1361);
    assert_eq!(diagnostic.diagnostic.arguments, ["path"]);
    assert!(diagnostic.diagnostic.details.is_empty());
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "'path' cannot be used as a value because it was imported using 'import type'.",
    );
    assert_eq!(diagnostic.related_information.len(), 1);
    let related = &diagnostic.related_information[0];
    assert_eq!(related.node, Some(nodes.import));
    assert_eq!(related.diagnostic.code(), 1376);
    assert_eq!(related.diagnostic.arguments, ["path"]);
    assert!(related.diagnostic.details.is_empty());
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "'path' was imported here."
    );
}

#[derive(Debug, PartialEq)]
struct Snapshot {
    types: Vec<TypeId>,
    symbols: Vec<SemanticSymbolId>,
    signatures: Vec<SignatureId>,
    counts: [usize; 4],
    diagnostics: CanonicalCheckerDiagnostics,
}

#[allow(clippy::too_many_lines)] // Keep both module owners and the cold-query order in one check.
fn check_queries(runtime: bool) {
    let text = if runtime {
        format!("{LEGAL}const rejected = path.normalize;\n")
    } else {
        LEGAL.to_owned()
    };
    let consumer = parse_source_file(&text);
    let provider = parse_source_file(PROVIDER_TEXT);
    let nodes = nodes(&consumer, &provider, runtime);
    let mut orders = vec![
        None,
        Some(nodes.query),
        Some(nodes.expression),
        Some(nodes.call),
    ];
    if let Some((property, _)) = nodes.runtime {
        orders.push(Some(property));
    }
    for first in orders {
        let mut checker = context(&consumer, &provider);
        let early = if let Some(first) = first {
            Some(checker.get_type_at_location(first).unwrap())
        } else {
            checker.check_source_file(CONSUMER).unwrap();
            None
        };
        // Read existing links before any explicit provider query or source check.
        assert_alias(&checker, &nodes);
        let provider_owner = symbol(&checker, nodes.provider_function);
        let provider_type = checker
            .store()
            .value_symbol_links(provider_owner)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let provider_signature = signature(&checker, nodes.provider_function);
        assert_eq!(
            checker
                .store()
                .signature(provider_signature)
                .unwrap()
                .declaration(),
            Some(nodes.provider_function)
        );
        if first.is_none() || first == nodes.runtime.map(|(property, _)| property) {
            assert_diagnostics(&checker, &nodes);
        }
        checker.check_source_file(CONSUMER).unwrap();
        assert_diagnostics(&checker, &nodes);
        checker.check_source_file(PROVIDER).unwrap();
        let mut cold = None;
        for replay in 0..3 {
            if replay != 0 {
                checker.recheck_source_file(CONSUMER).unwrap();
                checker.recheck_source_file(PROVIDER).unwrap();
            }
            let string = checker.store().intrinsic_bootstrap().unwrap().string_type;
            let own_type = checker.get_type_at_location(nodes.expression).unwrap();
            assert_ne!(own_type, provider_type);
            let own_owner = symbol(&checker, nodes.expression);
            let parameter = symbol(&checker, nodes.parameter);
            let provider_parameter = symbol(&checker, nodes.provider_parameter);
            assert_ne!(parameter, provider_parameter);
            assert_ne!(own_owner, provider_owner);
            assert_eq!(
                checker.store().type_payload(own_type).unwrap().symbol(),
                Some(own_owner)
            );
            assert_eq!(
                checker
                    .store()
                    .type_payload(provider_type)
                    .unwrap()
                    .symbol(),
                Some(provider_owner)
            );
            for node in [nodes.query, nodes.binding_name, nodes.provider_function] {
                assert_eq!(checker.get_type_at_location(node), Ok(provider_type));
            }
            assert_eq!(
                checker.get_type_at_location(nodes.parameter_name),
                Ok(string)
            );
            assert_eq!(checker.get_type_at_location(nodes.call), Ok(string));
            for node in [nodes.import_name, nodes.query_receiver] {
                assert_eq!(
                    checker.get_symbol_at_location(node),
                    Ok(Some(symbol(&checker, nodes.import)))
                );
            }
            assert_eq!(
                checker.get_symbol_at_location(nodes.parameter_name),
                Ok(Some(parameter))
            );
            let own_signature = signature(&checker, nodes.expression);
            assert_ne!(own_signature, provider_signature);
            for (type_, signature_id, declaration, parameter) in [
                (own_type, own_signature, nodes.expression, parameter),
                (
                    provider_type,
                    provider_signature,
                    nodes.provider_function,
                    provider_parameter,
                ),
            ] {
                assert_eq!(
                    checker.get_return_type_of_signature(signature_id),
                    Ok(string)
                );
                let record = checker.store().signature(signature_id).unwrap();
                assert_eq!(record.declaration(), Some(declaration));
                assert_eq!(record.parameters(), &[parameter]);
                assert_eq!(record.resolved_return_type(), Some(string));
                assert!(record.type_parameters().is_empty());
                assert_eq!(record.target(), None);
                assert_eq!(record.mapper(), None);
                let TypeData::Object(object) = checker.store().type_payload(type_).unwrap().data()
                else {
                    panic!("the real function must retain its callable object");
                };
                assert_eq!(
                    object.structured.signatures.as_deref(),
                    Some(&[signature_id][..])
                );
                assert_eq!(object.structured.call_signature_count, 1);
            }
            assert_eq!(signature(&checker, nodes.call), provider_signature);
            if let Some((property, receiver)) = nodes.runtime {
                assert_eq!(checker.get_type_at_location(property), Ok(provider_type));
                assert_eq!(
                    checker.get_symbol_at_location(receiver),
                    Ok(Some(symbol(&checker, nodes.import)))
                );
                assert_eq!(
                    checker.get_symbol_at_location(property),
                    Ok(Some(provider_owner))
                );
            }
            if let Some(early) = early {
                let expected = if first == Some(nodes.expression) {
                    own_type
                } else if first == Some(nodes.call) {
                    string
                } else {
                    provider_type
                };
                assert_eq!(early, expected);
            }
            assert_alias(&checker, &nodes);
            assert_diagnostics(&checker, &nodes);
            let store = checker.store();
            let snapshot = Snapshot {
                types: vec![own_type, provider_type, string],
                symbols: vec![
                    symbol(&checker, nodes.import),
                    symbol(&checker, nodes.provider_module),
                    symbol(&checker, nodes.binding),
                    own_owner,
                    provider_owner,
                    parameter,
                    provider_parameter,
                ],
                signatures: vec![
                    own_signature,
                    provider_signature,
                    signature(&checker, nodes.call),
                ],
                counts: [
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                ],
                diagnostics: checker.diagnostics().clone(),
            };
            if let Some(previous) = &cold {
                assert_eq!(&snapshot, previous);
            } else {
                cold = Some(snapshot);
            }
        }
    }
}

#[test]
fn qualified_type_only_namespace_query_keeps_module_and_callable_owners() {
    check_queries(false);
}

#[test]
fn cached_type_only_namespace_query_still_rejects_runtime_property_use() {
    check_queries(true);
}
