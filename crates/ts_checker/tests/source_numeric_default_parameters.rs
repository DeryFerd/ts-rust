use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
};
use ts_diagnostics::Category;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(204_330);

fn context(parsed: &ParseResult, external: bool) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/numeric-default-parameters.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                if external {
                    CanonicalModuleState::External
                } else {
                    CanonicalModuleState::Script
                },
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            no_implicit_any: true,
            strict_function_types: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), FILE, id))
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    nodes
}

fn check_case(invalid: bool) {
    let source = if invalid {
        concat!(
            "function descend(depth = 0): number { const wrong: string = depth; return depth; }\n",
            "const result: number = descend(\"bad\");\n",
        )
    } else {
        concat!(
            "function descend(depth = 0): number { depth = depth + 1; return depth; }\n",
            "const omitted: number = descend();\n",
            "const explicitUndefined: number = descend(undefined);\n",
            "const supplied: number = descend(2);\n",
        )
    };
    let parsed = parse_source_file(source);
    let functions = nodes(&parsed, SyntaxKind::FunctionDeclaration);
    let parameters = nodes(&parsed, SyntaxKind::Parameter);
    let ([function], [parameter]) = (functions.as_slice(), parameters.as_slice()) else {
        panic!("expected one function and its defaulted parameter")
    };
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(data.type_.is_none());
    assert!(data.question_token.is_none());
    assert!(data.dot_dot_dot_token.is_none());
    assert_eq!(
        parsed.arena.get(parameter.node).unwrap().parent,
        Some(function.node)
    );
    let name = NodeRef::new(parsed.arena.id(), FILE, data.name);
    let initializer = NodeRef::new(parsed.arena.id(), FILE, data.initializer.unwrap());
    assert_eq!(
        parsed.arena.get(initializer.node).unwrap().kind,
        SyntaxKind::NumericLiteral
    );
    let reads = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::Identifier(identifier) = &record.data else {
                return None;
            };
            (id != name.node && identifier.text == "depth").then_some(NodeRef::new(
                parsed.arena.id(),
                FILE,
                id,
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(reads.len(), if invalid { 2 } else { 3 });
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), if invalid { 1 } else { 3 });

    for first in [None, Some(*parameter), Some(calls[0])] {
        let mut checker = context(&parsed, false);
        let early = first.map(|node| (node, checker.get_type_at_location(node).unwrap()));
        checker.check_source_file(FILE).unwrap();
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        let bound = checker.file(FILE).unwrap().1.symbol(*parameter).unwrap();
        let owner = checker.store().get_merged_symbol(bound).unwrap();
        assert_eq!(
            checker.get_symbol_declarations(owner).unwrap(),
            &[*parameter]
        );
        assert_eq!(
            checker
                .store()
                .value_symbol_links(owner)
                .unwrap()
                .resolved_type,
            Some(number)
        );
        for at in [*parameter, name].into_iter().chain(reads.iter().copied()) {
            assert_eq!(checker.get_type_at_location(at), Ok(number));
            assert_eq!(checker.get_symbol_at_location(at), Ok(Some(owner)));
        }
        let literal = checker.get_type_at_location(initializer).unwrap();
        assert_ne!(literal, number);
        assert_eq!(checker.type_to_string(literal).unwrap(), "0");
        let selected = checker
            .store()
            .signature_links(*function)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let signature = checker.store().signature(selected).unwrap();
        assert_eq!(signature.declaration(), Some(*function));
        assert_eq!(signature.parameters(), [owner]);
        assert_eq!(signature.min_argument_count(), 0);
        assert!(!signature.has_rest_parameter());
        assert_eq!(signature.resolved_return_type(), Some(number));
        for &call in &calls {
            assert_eq!(checker.get_type_at_location(call), Ok(number));
            assert_eq!(
                checker
                    .store()
                    .signature_links(call)
                    .unwrap()
                    .resolved_signature
                    .signature(),
                Some(selected)
            );
        }
        if let Some((node, type_)) = early {
            assert_eq!(type_, number);
            assert_eq!(checker.get_type_at_location(node), Ok(type_));
        }
        if invalid {
            let mut actual = checker
                .diagnostics()
                .as_slice()
                .iter()
                .map(|diagnostic| {
                    assert_eq!(diagnostic.diagnostic.category(), Category::Error);
                    assert!(diagnostic.range_override.is_none());
                    assert!(diagnostic.related_information.is_empty());
                    let node = diagnostic.node.unwrap();
                    let range = parsed.arena.get(node.node).unwrap().range;
                    (
                        diagnostic.diagnostic.code(),
                        range.start.get() as usize,
                        range.end.get() as usize,
                        diagnostic.diagnostic.arguments.clone(),
                    )
                })
                .collect::<Vec<_>>();
            actual.sort_by_key(|item| item.1);
            let local = source.find("wrong:").unwrap();
            let argument = source.find("\"bad\"").unwrap();
            assert_eq!(
                actual,
                [
                    (
                        2322,
                        local,
                        local + 5,
                        vec!["number".to_owned(), "string".to_owned()]
                    ),
                    (
                        2345,
                        argument,
                        argument + 5,
                        vec!["\"bad\"".to_owned(), "number | undefined".to_owned()]
                    ),
                ]
            );
        } else {
            assert!(
                checker.diagnostics().is_empty(),
                "{:?}",
                checker.diagnostics()
            );
        }
        let snapshot = |checker: &CanonicalCheckerContext<'_>| {
            let store = checker.store();
            (
                [
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                    store.index_info_len(),
                    store.symbol_store().symbol_table_len(),
                ],
                parsed
                    .arena
                    .iter()
                    .map(|(id, _)| {
                        let node = NodeRef::new(parsed.arena.id(), FILE, id);
                        (
                            store.node_links(node).cloned(),
                            store.type_node_links(node).cloned(),
                            store.symbol_node_links(node).cloned(),
                            store.signature_links(node).cloned(),
                        )
                    })
                    .collect::<Vec<_>>(),
                store.value_symbol_links(owner).cloned(),
                store.relation_state_snapshot(),
                store
                    .source_file_links(checker.source_file(FILE).unwrap())
                    .cloned(),
                checker.diagnostics().clone(),
            )
        };
        let before = snapshot(&checker);
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            for at in [*parameter, name]
                .into_iter()
                .chain(reads.iter().copied())
                .chain(calls.iter().copied())
            {
                assert_eq!(checker.get_type_at_location(at), Ok(number));
            }
            assert_eq!(checker.get_type_at_location(initializer), Ok(literal));
            assert_eq!(snapshot(&checker), before);
        }
    }
}

#[test]
fn numeric_defaults_infer_number_and_accept_optional_calls() {
    check_case(false);
    check_exported_overload();
}

#[test]
fn numeric_defaults_keep_argument_and_assignment_errors() {
    check_case(true);
}

fn check_exported_overload() {
    let parsed = parse_source_file(concat!(
        "export function replaceEqualDeep<T>(a: unknown, b: T, depth?: number): T;\n",
        "export function replaceEqualDeep(a: any, b: any, depth = 0): any {\n",
        "depth = depth + 1; return b;\n}\n",
    ));
    let functions = nodes(&parsed, SyntaxKind::FunctionDeclaration);
    assert_eq!(functions.len(), 2);
    let implementation = functions[1];
    let NodeData::FunctionDeclaration(function) =
        &parsed.arena.get(implementation.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(function.body.is_some());
    assert!(function.type_parameters.is_none());
    let parameter = NodeRef::new(parsed.arena.id(), FILE, function.parameters.nodes[2]);
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(data.type_.is_none());
    let name = NodeRef::new(parsed.arena.id(), FILE, data.name);
    let initializer = NodeRef::new(parsed.arena.id(), FILE, data.initializer.unwrap());
    for first in [None, Some(parameter)] {
        let mut checker = context(&parsed, true);
        let early = first.map(|node| checker.get_type_at_location(node).unwrap());
        checker.check_source_file(FILE).unwrap();
        assert!(
            checker.diagnostics().is_empty(),
            "{:?}",
            checker.diagnostics()
        );
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        assert!(early.is_none_or(|type_| type_ == number));
        let bound = checker.file(FILE).unwrap().1.symbol(parameter).unwrap();
        let owner = checker.store().get_merged_symbol(bound).unwrap();
        assert_eq!(
            checker.get_symbol_declarations(owner).unwrap(),
            &[parameter]
        );
        for at in [parameter, name] {
            assert_eq!(checker.get_type_at_location(at), Ok(number));
            assert_eq!(checker.get_symbol_at_location(at), Ok(Some(owner)));
        }
        let literal = checker.get_type_at_location(initializer).unwrap();
        assert_ne!(literal, number);
        assert_eq!(checker.type_to_string(literal).unwrap(), "0");
        let signature = checker
            .store()
            .signature_links(implementation)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let record = checker.store().signature(signature).unwrap();
        assert_eq!(record.declaration(), Some(implementation));
        assert_eq!(record.parameters().len(), 3);
        assert_eq!(record.parameters()[2], owner);
        assert_eq!(record.min_argument_count(), 2);
        let snapshot = |checker: &CanonicalCheckerContext<'_>| {
            let store = checker.store();
            (
                [
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                ],
                store.value_symbol_links(owner).cloned(),
                store.signature_links(implementation).cloned(),
                store.type_node_links(parameter).cloned(),
                store.type_node_links(initializer).cloned(),
                checker.diagnostics().clone(),
            )
        };
        let before = snapshot(&checker);
        for _ in 0..2 {
            checker.check_source_file(FILE).unwrap();
            checker.recheck_source_file(FILE).unwrap();
            assert_eq!(checker.get_type_at_location(parameter), Ok(number));
            assert_eq!(checker.get_type_at_location(initializer), Ok(literal));
            assert_eq!(snapshot(&checker), before);
        }
    }
}
