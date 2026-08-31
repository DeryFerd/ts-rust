use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    SourceFunctionUnsupported, UnsupportedSourceSyntax, ValueSymbolLinks,
};
use ts_parser::{ParseResult, parse_source_file};

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/annotated-uninitialized-locals.ts\""),
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
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_bind_call_apply: true,
            strict_builtin_iterator_return: true,
            strict_function_types: true,
            strict_property_initialization: true,
            use_unknown_in_catch_variables: true,
            no_implicit_any: true,
            no_implicit_this: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn unique_node(parsed: &ParseResult, file: FileId, matches: impl Fn(&NodeData) -> bool) -> NodeRef {
    let nodes = parsed
        .arena
        .iter()
        .filter_map(|(id, node)| {
            matches(&node.data).then_some(NodeRef::new(parsed.arena.id(), file, id))
        })
        .collect::<Vec<_>>();
    assert_eq!(nodes.len(), 1);
    nodes[0]
}

fn variable(parsed: &ParseResult, file: FileId, name: &str) -> NodeRef {
    unique_node(parsed, file, |node| {
        let NodeData::VariableDeclaration(variable) = node else {
            return false;
        };
        matches!(&parsed.arena.get(variable.name).unwrap().data,
            NodeData::Identifier(identifier) if identifier.text == name)
    })
}

fn initializer(parsed: &ParseResult, declaration: NodeRef) -> NodeRef {
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!()
    };
    NodeRef::new(
        declaration.arena,
        declaration.file,
        variable.initializer.unwrap(),
    )
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
) -> impl PartialEq + std::fmt::Debug + use<> {
    (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().relation_state_snapshot(),
        context
            .store()
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| (symbol, context.store().value_symbol_links(symbol).cloned()))
            .collect::<Vec<_>>(),
        parsed
            .arena
            .iter()
            .map(|(node, _)| {
                let node = NodeRef::new(parsed.arena.id(), file, node);
                (
                    node,
                    context.store().type_node_links(node).cloned(),
                    context.store().symbol_node_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        context.diagnostics().clone(),
    )
}

fn assert_replay(context: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult, file: FileId) {
    let before = snapshot(context, parsed, file);
    for _ in 0..2 {
        context.recheck_source_file(file).unwrap();
        assert_eq!(snapshot(context, parsed, file), before);
        assert!(
            context
                .store()
                .source_file_links(context.source_file(file).unwrap())
                .unwrap()
                .type_checked
        );
    }
}

#[test]
fn annotated_locals_keep_declared_types_after_real_assignments_and_replay() {
    for (index, (source, expected)) in [
        ("function read(): number { let value: number; value = 1; const first: number = value; value = 2; return value; }", "number"),
        ("const read = (): string => { let value: string; value = 'first'; const first: string = value; value = 'last'; return value; };", "string"),
    ].into_iter().enumerate() {
        let parsed = parse_source_file(source);
        let file = FileId::new(84_100 + u32::try_from(index).unwrap());
        let mut context = context(&parsed, file);
        let declaration = variable(&parsed, file, "value");
        let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
        let NodeData::VariableDeclaration(local) = &parsed.arena.get(declaration.node).unwrap().data else { unreachable!() };
        assert!(local.initializer.is_none());
        let annotation = NodeRef::new(declaration.arena, file, local.type_.unwrap());
        let name = NodeRef::new(declaration.arena, file, local.name);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty(), "{:?}", context.diagnostics());
        let declared = context.get_type_from_type_node(annotation).unwrap();
        assert_eq!(context.type_to_string(declared).unwrap(), expected);
        assert_eq!(context.get_symbol_at_location(name), Ok(Some(symbol)));
        assert_eq!(context.store().value_symbol_links(symbol), Some(&ValueSymbolLinks {
            resolved_type: Some(declared), ..ValueSymbolLinks::default()
        }));
        let first = variable(&parsed, file, "first");
        let read = initializer(&parsed, first);
        assert_eq!(context.get_symbol_at_location(read), Ok(Some(symbol)));
        assert_replay(&mut context, &parsed, file);
    }
}

#[test]
fn annotated_local_writes_keep_exact_type_errors_and_later_valid_writes() {
    let source =
        "function read(): number { let value: number; value = 'wrong'; value = 1; return value; }";
    let parsed = parse_source_file(source);
    let file = FileId::new(84_110);
    let mut context = context(&parsed, file);
    let bad = unique_node(&parsed, file, |node| {
        let NodeData::BinaryExpression(binary) = node else {
            return false;
        };
        matches!(
            &parsed.arena.get(binary.right).unwrap().data,
            NodeData::StringLiteral(_)
        )
    });
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(bad.node).unwrap().data else {
        unreachable!()
    };
    assert_eq!(
        parsed.arena.get(binary.operator_token).unwrap().kind,
        SyntaxKind::EqualsToken
    );
    let target = NodeRef::new(bad.arena, file, binary.left);
    context.check_source_file(file).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].node, Some(target));
    assert!(diagnostics[0].range_override.is_none());
    assert_eq!(diagnostics[0].diagnostic.code(), 2322);
    assert_eq!(diagnostics[0].diagnostic.arguments, ["string", "number"]);
    assert_eq!(
        diagnostics[0].diagnostic.render().unwrap(),
        "Type 'string' is not assignable to type 'number'."
    );
    assert!(diagnostics[0].related_information.is_empty());
    let declaration = variable(&parsed, file, "value");
    let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
    assert_eq!(
        context
            .store()
            .value_symbol_links(symbol)
            .unwrap()
            .resolved_type,
        Some(context.store().intrinsic_bootstrap().unwrap().number_type)
    );
    assert_replay(&mut context, &parsed, file);
}

#[test]
fn strict_local_reads_keep_definite_assignment_and_non_null_exemption() {
    for (index, (source, expected_read)) in [
        ("function early(): number { let value: number; const before: number = value; value = 1; return value; }", Some("before")),
        ("function asserted(): number { let value: number; const asserted: number = value!; return value; }", Some("return")),
        ("function unknownValue(): unknown { let value: unknown; return value; }", None),
        ("function optionalValue(): number | undefined { let value: number | undefined; return value; }", None),
    ].into_iter().enumerate() {
        let parsed = parse_source_file(source);
        let file = FileId::new(84_120 + u32::try_from(index).unwrap());
        let mut context = context(&parsed, file);
        let expected = expected_read.map(|read| {
            if read == "return" {
                let returned = unique_node(&parsed, file, |node| matches!(node, NodeData::ReturnStatement(_)));
                let NodeData::ReturnStatement(statement) = &parsed.arena.get(returned.node).unwrap().data else { unreachable!() };
                NodeRef::new(returned.arena, file, statement.expression.unwrap())
            } else {
                initializer(&parsed, variable(&parsed, file, read))
            }
        });
        context.check_source_file(file).unwrap();
        let diagnostics = context.diagnostics().as_slice();
        if let Some(expected) = expected {
            assert_eq!(diagnostics.len(), 1);
            assert_eq!(diagnostics[0].node, Some(expected));
            assert!(diagnostics[0].range_override.is_none());
            assert_eq!(diagnostics[0].diagnostic.code(), 2454);
            assert_eq!(diagnostics[0].diagnostic.arguments, ["value"]);
            assert_eq!(diagnostics[0].diagnostic.render().unwrap(), "Variable 'value' is used before being assigned.");
            assert!(diagnostics[0].related_information.is_empty());
        } else {
            assert!(diagnostics.is_empty(), "{diagnostics:?}");
        }
        assert_replay(&mut context, &parsed, file);
    }
}

#[test]
fn annotated_local_admission_preserves_existing_const_rules() {
    let parsed =
        parse_source_file("function fixed(): number { const value: number = 1; return value; }");
    let file = FileId::new(84_130);
    let mut valid = context(&parsed, file);
    valid.check_source_file(file).unwrap();
    assert!(valid.diagnostics().is_empty());
    assert_replay(&mut valid, &parsed, file);
    for (index, source) in [
        "function missing(): number { const value: number; return value; }",
        "function reassigned(): number { const value: number = 1; value = 2; return value; }",
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        let file = FileId::new(84_131 + u32::try_from(index).unwrap());
        let mut context = context(&parsed, file);
        let function = unique_node(&parsed, file, |node| {
            matches!(node, NodeData::FunctionDeclaration(_))
        });
        let NodeData::FunctionDeclaration(declaration) =
            &parsed.arena.get(function.node).unwrap().data
        else {
            unreachable!()
        };
        let body = NodeRef::new(function.arena, file, declaration.body.unwrap());
        let before = snapshot(&context, &parsed, file);
        for _ in 0..2 {
            assert_eq!(
                context.check_source_file(file),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Function(SourceFunctionUnsupported::FunctionBody(
                        body
                    ))
                ))
            );
            assert_eq!(snapshot(&context, &parsed, file), before);
            assert!(context.diagnostics().is_empty());
            assert!(
                context
                    .store()
                    .source_file_links(context.source_file(file).unwrap())
                    .is_none_or(|links| !links.type_checked)
            );
        }
    }
}

#[test]
fn annotated_local_initial_flow_narrows_after_the_condition_read() {
    for (index, (source, assigned)) in [
        (
            "function read(): number { let value: number; if (value) { return value; } else { return 0; } }",
            false,
        ),
        (
            "function read(): number { let value: number = 1; if (value) { return value; } else { return 0; } }",
            true,
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        let file = FileId::new(84_140 + u32::try_from(index).unwrap());
        let mut context = context(&parsed, file);
        let condition = unique_node(&parsed, file, |node| {
            matches!(node, NodeData::IfStatement(_))
        });
        let NodeData::IfStatement(statement) = &parsed.arena.get(condition.node).unwrap().data else {
            unreachable!()
        };
        let read = NodeRef::new(condition.arena, file, statement.expression);
        context.check_source_file(file).unwrap();
        let diagnostics = context.diagnostics().as_slice();
        if assigned {
            assert!(diagnostics.is_empty(), "{diagnostics:?}");
        } else {
            assert_eq!(diagnostics.len(), 1);
            assert_eq!(diagnostics[0].node, Some(read));
            assert!(diagnostics[0].range_override.is_none());
            assert_eq!(diagnostics[0].diagnostic.code(), 2454);
            assert_eq!(diagnostics[0].diagnostic.arguments, ["value"]);
            assert_eq!(
                diagnostics[0].diagnostic.render().unwrap(),
                "Variable 'value' is used before being assigned."
            );
            assert!(diagnostics[0].related_information.is_empty());
        }
        let declaration = variable(&parsed, file, "value");
        let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();
        assert_eq!(
            context.store().value_symbol_links(symbol).unwrap().resolved_type,
            Some(context.store().intrinsic_bootstrap().unwrap().number_type)
        );
        assert_replay(&mut context, &parsed, file);
    }
}

#[test]
fn pending_annotated_local_capture_keeps_its_exact_typed_boundary() {
    let parsed = parse_source_file(
        "function read(): number { let value: number; const get = () => value; return get(); }",
    );
    let file = FileId::new(84_150);
    let mut context = context(&parsed, file);
    let arrow = unique_node(&parsed, file, |node| {
        matches!(node, NodeData::ArrowFunction(_))
    });
    let NodeData::ArrowFunction(function) = &parsed.arena.get(arrow.node).unwrap().data else {
        unreachable!()
    };
    let read = NodeRef::new(arrow.arena, file, function.body);
    assert_eq!(
        parsed.arena.get(read.node).unwrap().kind,
        SyntaxKind::Identifier
    );
    let before = snapshot(&context, &parsed, file);
    for _ in 0..2 {
        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Syntax {
                    node: read,
                    kind: SyntaxKind::Identifier,
                    role: ts_checker::semantic::SourceSyntaxRole::FunctionBody,
                }
            ))
        );
        assert_eq!(snapshot(&context, &parsed, file), before);
        assert!(context.diagnostics().is_empty());
        assert!(
            context
                .store()
                .source_file_links(context.source_file(file).unwrap())
                .is_none_or(|links| !links.type_checked)
        );
    }
}
