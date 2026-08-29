use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModuleInput, IntrinsicBootstrapOptions,
    SignatureId, TypeData, TypeId, types::TypeFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const IMPORTER: FileId = FileId::new(8_220);
const PROVIDER: FileId = FileId::new(8_221);
const IMPORTER_SOURCE: &str = "import make from './provider'; const copy = make;";

fn only_node(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed.arena.iter().filter_map(|(node, record)| {
        (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
    });
    let node = nodes.next().expect("the source must contain this node");
    assert!(nodes.next().is_none(), "expected one {kind:?}");
    node
}

fn context<'arena>(
    importer: &'arena ParseResult,
    provider: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (IMPORTER, importer, "\"/project/importer.ts\""),
        (PROVIDER, provider, "\"/project/provider.ts\""),
    ];
    let mut binder = CanonicalBinder::new();
    for &(file, parsed, path) in &files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
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
    let import = only_node(importer, IMPORTER, SyntaxKind::ImportDeclaration);
    let NodeData::ImportDeclaration(import) = &importer.arena.get(import.node).unwrap().data else {
        unreachable!();
    };
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
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
        CanonicalModuleResolutionManifestInput::new([CanonicalModuleResolutionEntry::resolved(
            NodeRef::new(importer.arena.id(), IMPORTER, import.module_specifier),
            CanonicalResolvedModuleInput::new(
                PROVIDER,
                CanonicalModuleResolutionMode::Esm,
                CanonicalModuleResolutionMode::Esm,
            ),
        )]),
    )
    .unwrap()
}

fn symbol(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(node.file).unwrap().1.symbol(node).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn checked(checker: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    checker
        .store()
        .source_file_links(checker.source_file(file).unwrap())
        .is_some_and(|links| links.type_checked)
}

fn counts(checker: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = checker.store();
    [
        store.type_len(),
        store.type_alias_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

struct Parameter {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
}

struct Arrow {
    declaration: NodeRef,
    binding: NodeRef,
    type_parameters: Vec<NodeRef>,
    parameters: Vec<Parameter>,
    annotation: NodeRef,
    body: NodeRef,
    result: NodeRef,
}

fn arrow(parsed: &ParseResult, declaration: NodeRef) -> Arrow {
    let node_ref = |node| NodeRef::new(parsed.arena.id(), PROVIDER, node);
    let record = parsed.arena.get(declaration.node).unwrap();
    let NodeData::ArrowFunction(arrow) = &record.data else {
        panic!("expected an actual arrow")
    };
    let result = match &parsed.arena.get(arrow.body).unwrap().data {
        NodeData::Block(block) => {
            assert!(block.statements.nodes.len() >= 2);
            let NodeData::ReturnStatement(returned) = &parsed
                .arena
                .get(*block.statements.nodes.last().unwrap())
                .unwrap()
                .data
            else {
                panic!("the linear body must end in its original return")
            };
            node_ref(returned.expression.unwrap())
        }
        _ => node_ref(arrow.body),
    };
    Arrow {
        declaration,
        binding: node_ref(record.parent.unwrap()),
        type_parameters: arrow
            .type_parameters
            .as_ref()
            .into_iter()
            .flat_map(|parameters| &parameters.nodes)
            .map(|&node| node_ref(node))
            .collect(),
        parameters: arrow
            .parameters
            .nodes
            .iter()
            .map(|&node| {
                let NodeData::ParameterDeclaration(parameter) =
                    &parsed.arena.get(node).unwrap().data
                else {
                    unreachable!()
                };
                Parameter {
                    declaration: node_ref(node),
                    name: node_ref(parameter.name),
                    annotation: node_ref(parameter.type_.unwrap()),
                }
            })
            .collect(),
        annotation: node_ref(arrow.type_.unwrap()),
        body: node_ref(arrow.body),
        result,
    }
}

#[derive(Debug, Eq, PartialEq)]
struct CallableState {
    owner: SemanticSymbolId,
    binding: SemanticSymbolId,
    type_: TypeId,
    signature: SignatureId,
    type_parameters: Vec<TypeId>,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    returned: TypeId,
}

#[allow(clippy::too_many_lines)] // Keep each callable's owner, parameters, and signature in one check.
fn callable_state(checker: &CanonicalCheckerContext<'_>, arrow: &Arrow) -> CallableState {
    let owner = symbol(checker, arrow.declaration);
    let binding = symbol(checker, arrow.binding);
    assert_ne!(owner, binding);
    let owner_record = checker.store().symbol(owner).unwrap();
    assert_eq!(owner_record.flags(), SymbolFlags::FUNCTION);
    assert_eq!(owner_record.declarations(), Some(&[arrow.declaration][..]));
    assert_eq!(owner_record.value_declaration(), Some(arrow.declaration));
    let binding_record = checker.store().symbol(binding).unwrap();
    let expected_flags = match checker
        .file(PROVIDER)
        .unwrap()
        .0
        .get(arrow.binding.node)
        .unwrap()
        .kind
    {
        SyntaxKind::ExportAssignment => SymbolFlags::PROPERTY,
        SyntaxKind::VariableDeclaration => SymbolFlags::BLOCK_SCOPED_VARIABLE,
        _ => panic!("expected the default export or child variable"),
    };
    assert_eq!(binding_record.flags(), expected_flags);
    assert_eq!(binding_record.declarations(), Some(&[arrow.binding][..]));
    assert_eq!(binding_record.value_declaration(), Some(arrow.binding));
    let type_ = checker
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_eq!(
        checker
            .store()
            .value_symbol_links(binding)
            .unwrap()
            .resolved_type,
        Some(type_)
    );
    let signature = checker
        .store()
        .signature_links(arrow.declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let record = checker.store().type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("expected the callable object")
    };
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    let type_parameters = arrow
        .type_parameters
        .iter()
        .map(|&node| {
            let owner = symbol(checker, node);
            let type_ = checker
                .store()
                .declared_type_links(owner)
                .unwrap()
                .declared_type
                .unwrap();
            let record = checker.store().type_payload(type_).unwrap();
            assert_eq!(record.flags(), TypeFlags::TYPE_PARAMETER);
            assert_eq!(record.symbol(), Some(owner));
            let TypeData::TypeParameter(parameter) = record.data() else {
                unreachable!()
            };
            assert_eq!(parameter.target, None);
            assert_eq!(parameter.mapper, None);
            type_
        })
        .collect::<Vec<_>>();
    let parameters = arrow
        .parameters
        .iter()
        .map(|parameter| {
            let symbol = symbol(checker, parameter.declaration);
            (
                symbol,
                checker
                    .store()
                    .value_symbol_links(symbol)
                    .unwrap()
                    .resolved_type
                    .unwrap(),
            )
        })
        .collect::<Vec<_>>();
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(arrow.declaration));
    assert_eq!(record.type_parameters(), type_parameters);
    assert_eq!(
        record.parameters(),
        parameters
            .iter()
            .map(|&(symbol, _)| symbol)
            .collect::<Vec<_>>()
    );
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.this_parameter(), None);
    assert_eq!(
        record.min_argument_count(),
        i32::try_from(arrow.parameters.len()).unwrap()
    );
    CallableState {
        owner,
        binding,
        type_,
        signature,
        type_parameters,
        parameters,
        returned: record.resolved_return_type().unwrap(),
    }
}

fn diagnostics(checker: &CanonicalCheckerContext<'_>, child: Option<&Arrow>, invalid_child: bool) {
    let actual = checker.diagnostics().as_slice();
    if invalid_child {
        let [diagnostic] = actual else {
            panic!("expected one child-body diagnostic: {actual:?}")
        };
        assert_eq!(diagnostic.node, Some(child.unwrap().result));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
    } else {
        assert!(actual.is_empty(), "{actual:?}");
    }
}

fn query_state(
    checker: &mut CanonicalCheckerContext<'_>,
    locations: &[NodeRef],
) -> Vec<(NodeRef, TypeId, Option<SemanticSymbolId>)> {
    assert!(checked(checker, PROVIDER));
    locations
        .iter()
        .map(|&node| {
            (
                node,
                checker.get_type_at_location(node).unwrap(),
                checker.get_symbol_at_location(node).unwrap(),
            )
        })
        .collect()
}

#[allow(clippy::too_many_lines)] // Keep importer demand, lexical ownership, body checking, and replay together.
fn check_body(source: &str, child_parameters: Option<usize>, invalid_child: bool) {
    let provider = parse_source_file(source);
    let importer = parse_source_file(IMPORTER_SOURCE);
    let node_ref = |node| NodeRef::new(provider.arena.id(), PROVIDER, node);
    let exported = only_node(&provider, PROVIDER, SyntaxKind::ExportAssignment);
    let NodeData::ExportAssignment(export) = &provider.arena.get(exported.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(!export.is_export_equals);
    let outer = arrow(&provider, node_ref(export.expression));
    assert_eq!(outer.binding, exported);
    assert_eq!(outer.type_parameters.len(), 1);
    assert_eq!(outer.parameters.len(), 1);
    let children = provider
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::ArrowFunction && node != outer.declaration.node)
                .then_some(node_ref(node))
        })
        .collect::<Vec<_>>();
    assert_eq!(children.len(), usize::from(child_parameters.is_some()));
    let child = children.first().map(|&node| arrow(&provider, node));
    if let Some(child) = &child {
        assert!(child.type_parameters.is_empty());
        assert_eq!(child.parameters.len(), child_parameters.unwrap());
    }
    let locals = provider
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            Some((
                node_ref(node),
                node_ref(variable.name),
                variable.type_.map(node_ref),
                node_ref(variable.initializer.unwrap()),
            ))
        })
        .collect::<Vec<_>>();
    let import = only_node(&importer, IMPORTER, SyntaxKind::ImportClause);
    let NodeData::ImportClause(clause) = &importer.arena.get(import.node).unwrap().data else {
        unreachable!()
    };
    let import_name = NodeRef::new(importer.arena.id(), IMPORTER, clause.name.unwrap());
    let copy = only_node(&importer, IMPORTER, SyntaxKind::VariableDeclaration);
    let NodeData::VariableDeclaration(copy) = &importer.arena.get(copy.node).unwrap().data else {
        unreachable!()
    };
    let copy_name = NodeRef::new(importer.arena.id(), IMPORTER, copy.name);

    for provider_first in [false, true] {
        let mut checker = context(&importer, &provider);
        assert_eq!(checker.file_order(), [IMPORTER, PROVIDER]);
        let outer_owner = symbol(&checker, outer.declaration);
        let export_owner = symbol(&checker, exported);
        let alias = symbol(&checker, import);
        assert_ne!(alias, outer_owner);
        assert_ne!(alias, export_owner);
        assert_ne!(outer_owner, export_owner);
        assert_eq!(
            checker.store().symbol(alias).unwrap().flags(),
            SymbolFlags::ALIAS
        );
        let module = symbol(&checker, checker.file(PROVIDER).unwrap().1.source_file());
        assert_eq!(
            checker.store().symbol(export_owner).unwrap().parent(),
            Some(module)
        );
        let exports = checker.store().symbol(module).unwrap().exports().unwrap();
        assert_eq!(
            checker
                .store()
                .symbol_table(exports)
                .unwrap()
                .get_source("default"),
            Some(export_owner)
        );
        assert!(!checked(&checker, IMPORTER));
        assert!(!checked(&checker, PROVIDER));
        if provider_first {
            checker.check_source_file(PROVIDER).unwrap();
        }
        checker.check_source_file(IMPORTER).unwrap();
        assert!(checked(&checker, IMPORTER));
        assert_eq!(checked(&checker, PROVIDER), provider_first);
        let before_body = callable_state(&checker, &outer);
        let t = before_body.type_parameters[0];
        let t_symbol = symbol(&checker, outer.type_parameters[0]);
        let value_symbol = before_body.parameters[0].0;
        assert_eq!(before_body.parameters[0].1, t);
        assert_eq!(before_body.returned, t);
        assert_eq!(
            checker
                .store()
                .value_symbol_links(alias)
                .unwrap()
                .resolved_type,
            Some(before_body.type_)
        );
        let alias_links = checker.store().alias_symbol_links(alias).cloned().unwrap();
        assert_eq!(alias_links.immediate_target, Some(export_owner));
        assert_eq!(
            alias_links.alias_target,
            AliasTargetState::Resolved(export_owner)
        );
        assert_eq!(alias_links.type_only_declaration, None);
        let before_query = counts(&checker);
        assert_eq!(
            checker.get_return_type_of_signature(before_body.signature),
            Ok(t)
        );
        assert_eq!(
            checker.get_type_at_location(copy_name),
            Ok(before_body.type_)
        );
        assert_eq!(
            checker.get_type_at_location(import_name),
            Ok(before_body.type_)
        );
        assert_eq!(counts(&checker), before_query);
        assert_eq!(checked(&checker, PROVIDER), provider_first);
        if !provider_first {
            assert!(checker.diagnostics().is_empty());
            for node in [outer.declaration, outer.body, outer.result] {
                assert!(checker.store().type_node_links(node).is_none());
            }
            for &(declaration, _, _, initializer) in &locals {
                assert!(
                    checker
                        .store()
                        .value_symbol_links(symbol(&checker, declaration))
                        .is_none()
                );
                assert!(checker.store().type_node_links(initializer).is_none());
            }
            if let Some(child) = &child {
                assert!(
                    checker
                        .store()
                        .value_symbol_links(symbol(&checker, child.declaration))
                        .is_none()
                );
                assert!(checker.store().signature_links(child.declaration).is_none());
                assert!(checker.store().type_node_links(child.result).is_none());
            }
        }
        checker.check_source_file(PROVIDER).unwrap();
        assert!(checked(&checker, PROVIDER));
        diagnostics(&checker, child.as_ref(), invalid_child);
        assert_eq!(callable_state(&checker, &outer), before_body);
        assert_eq!(
            checker
                .store()
                .type_node_links(outer.result)
                .unwrap()
                .resolved_type,
            Some(t)
        );
        assert_eq!(checker.get_type_at_location(outer.result), Ok(t));
        let NodeData::Identifier(returned_name) =
            &provider.arena.get(outer.result.node).unwrap().data
        else {
            panic!("the outer return must keep its original identifier")
        };
        let returned_symbol = if invalid_child {
            assert_eq!(returned_name.text, "value");
            value_symbol
        } else {
            locals
                .iter()
                .find_map(|&(declaration, name, _, _)| {
                    let NodeData::Identifier(name) = &provider.arena.get(name.node).unwrap().data
                    else {
                        unreachable!()
                    };
                    (name.text == returned_name.text).then(|| symbol(&checker, declaration))
                })
                .expect("the outer return must read its local binding")
        };
        assert_eq!(
            checker.get_symbol_at_location(outer.result),
            Ok(Some(returned_symbol))
        );
        let mut locations = vec![
            outer.declaration,
            outer.annotation,
            outer.result,
            import_name,
            copy_name,
        ];
        for parameter in &outer.parameters {
            locations.extend([parameter.name, parameter.annotation]);
        }
        let NodeData::TypeParameterDeclaration(type_parameter) = &provider
            .arena
            .get(outer.type_parameters[0].node)
            .unwrap()
            .data
        else {
            unreachable!()
        };
        locations.push(node_ref(type_parameter.name));
        for &(declaration, name, annotation, initializer) in &locals {
            let local_symbol = symbol(&checker, declaration);
            assert_ne!(local_symbol, value_symbol);
            assert_eq!(checker.get_symbol_at_location(name), Ok(Some(local_symbol)));
            locations.extend([name, initializer]);
            if matches!(
                provider.arena.get(initializer.node).unwrap().data,
                NodeData::Identifier(_)
            ) {
                assert_eq!(checker.get_type_at_location(initializer), Ok(t));
                assert_eq!(
                    checker.get_symbol_at_location(initializer),
                    Ok(Some(value_symbol))
                );
            }
            if let Some(annotation) = annotation {
                assert_eq!(
                    checker
                        .store()
                        .value_symbol_links(local_symbol)
                        .unwrap()
                        .resolved_type,
                    Some(t)
                );
                assert_eq!(
                    checker
                        .store()
                        .type_node_links(annotation)
                        .unwrap()
                        .resolved_type,
                    Some(t)
                );
                assert_eq!(checker.get_type_from_type_node(annotation), Ok(t));
                assert_eq!(
                    checker
                        .store()
                        .symbol_node_links(annotation)
                        .unwrap()
                        .resolved_symbol,
                    Some(t_symbol)
                );
                locations.push(annotation);
            }
        }
        let child_state = child.as_ref().map(|child| {
            let state = callable_state(&checker, child);
            assert!(state.type_parameters.is_empty());
            assert_ne!(state.owner, before_body.owner);
            assert_ne!(state.binding, before_body.binding);
            assert_eq!(
                checker.get_type_at_location(child.declaration),
                Ok(state.type_)
            );
            assert_eq!(checker.get_symbol_at_location(child.declaration), Ok(None));
            let &(_, child_name, _, _) = locals
                .iter()
                .find(|local| local.0 == child.binding)
                .unwrap();
            assert_eq!(checker.get_type_at_location(child_name), Ok(state.type_));
            locations.extend([child.declaration, child.annotation, child.result]);
            for (parameter, &(parameter_symbol, parameter_type)) in
                child.parameters.iter().zip(&state.parameters)
            {
                assert_ne!(parameter_symbol, value_symbol);
                assert_eq!(parameter_type, t);
                assert_eq!(
                    checker.get_symbol_at_location(parameter.name),
                    Ok(Some(parameter_symbol))
                );
                assert_eq!(
                    checker
                        .store()
                        .type_node_links(parameter.annotation)
                        .unwrap()
                        .resolved_type,
                    Some(t)
                );
                assert_eq!(checker.get_type_from_type_node(parameter.annotation), Ok(t));
                assert_eq!(
                    checker
                        .store()
                        .symbol_node_links(parameter.annotation)
                        .unwrap()
                        .resolved_symbol,
                    Some(t_symbol)
                );
                locations.extend([parameter.name, parameter.annotation]);
            }
            if invalid_child {
                assert_eq!(
                    state.returned,
                    checker.store().intrinsic_bootstrap().unwrap().string_type
                );
                let body_type = checker
                    .store()
                    .type_node_links(child.result)
                    .unwrap()
                    .resolved_type
                    .unwrap();
                assert_eq!(
                    checker.store().type_payload(body_type).unwrap().flags(),
                    TypeFlags::NUMBER_LITERAL
                );
            } else {
                assert_eq!(state.returned, t);
                assert_eq!(
                    checker
                        .store()
                        .type_node_links(child.result)
                        .unwrap()
                        .resolved_type,
                    Some(t)
                );
                assert_eq!(
                    checker.get_symbol_at_location(child.result),
                    Ok(Some(value_symbol))
                );
                assert_eq!(
                    checker
                        .store()
                        .type_node_links(child.annotation)
                        .unwrap()
                        .resolved_type,
                    Some(t)
                );
                assert_eq!(checker.get_type_from_type_node(child.annotation), Ok(t));
                assert_eq!(
                    checker
                        .store()
                        .symbol_node_links(child.annotation)
                        .unwrap()
                        .resolved_symbol,
                    Some(t_symbol)
                );
            }
            assert_eq!(
                checker.get_return_type_of_signature(state.signature),
                Ok(state.returned)
            );
            state
        });
        for (node, record) in provider.arena.iter() {
            if let NodeData::CallExpression(call) = &record.data {
                let state = child_state.as_ref().unwrap();
                let call_node = node_ref(node);
                assert_eq!(checker.get_type_at_location(call_node), Ok(t));
                assert_eq!(
                    checker.get_symbol_at_location(node_ref(call.expression)),
                    Ok(Some(state.binding))
                );
                assert_eq!(
                    checker
                        .store()
                        .signature_links(call_node)
                        .unwrap()
                        .resolved_signature
                        .signature(),
                    Some(state.signature)
                );
                locations.push(call_node);
            }
        }
        assert_eq!(
            checker.get_type_at_location(outer.declaration),
            Ok(before_body.type_)
        );
        assert_eq!(checker.get_symbol_at_location(outer.declaration), Ok(None));
        let artifacts = query_state(&mut checker, &locations);
        diagnostics(&checker, child.as_ref(), invalid_child);
        let cache_state = |checker: &CanonicalCheckerContext<'_>| {
            provider
                .arena
                .iter()
                .map(|(node, _)| {
                    let node = node_ref(node);
                    (
                        node,
                        checker.store().type_node_links(node).cloned(),
                        checker.store().symbol_node_links(node).cloned(),
                        checker.store().signature_links(node).cloned(),
                    )
                })
                .collect::<Vec<_>>()
        };
        let caches = cache_state(&checker);
        let before = counts(&checker);
        let expected_diagnostics = checker.diagnostics().clone();
        for _ in 0..2 {
            checker.recheck_source_file(IMPORTER).unwrap();
            checker.recheck_source_file(PROVIDER).unwrap();
            assert_eq!(callable_state(&checker, &outer), before_body);
            if let Some(child) = &child {
                let expected = child_state.as_ref().unwrap();
                assert_eq!(callable_state(&checker, child), *expected);
                assert_eq!(
                    checker.get_return_type_of_signature(expected.signature),
                    Ok(expected.returned)
                );
            }
            assert_eq!(
                checker.get_return_type_of_signature(before_body.signature),
                Ok(t)
            );
            assert_eq!(query_state(&mut checker, &locations), artifacts);
            assert_eq!(cache_state(&checker), caches);
            assert_eq!(
                checker.store().alias_symbol_links(alias),
                Some(&alias_links)
            );
            assert_eq!(checker.diagnostics(), &expected_diagnostics);
            assert_eq!(counts(&checker), before);
            assert!(checked(&checker, IMPORTER));
            assert!(checked(&checker, PROVIDER));
        }
    }
}

#[test]
fn generic_default_arrow_linear_local_keeps_the_outer_parameter() {
    check_body(
        "export default <T>(value: T): T => { const local: T = value; return local; };",
        None,
        false,
    );
}

#[test]
fn typed_inner_arrow_captures_the_outer_value_and_type_parameter() {
    check_body(
        "export default <T>(value: T): T => { const read = (candidate: T): T => value; const result: T = read(value); return result; };",
        Some(1),
        false,
    );
}

#[test]
fn zero_argument_inner_arrow_captures_the_outer_value_and_type_parameter() {
    check_body(
        "export default <T>(value: T): T => { const read = (): T => value; const result: T = read(); return result; };",
        Some(0),
        false,
    );
}

#[test]
fn invalid_inner_arrow_return_is_reported_only_when_the_provider_body_is_checked() {
    check_body(
        "export default <T>(value: T): T => { const read = (): string => 1; return value; };",
        Some(0),
        true,
    );
}
