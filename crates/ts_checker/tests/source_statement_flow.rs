use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
    ResolvedSignatureState, SignatureId, SignatureLinks, SourceCheckError,
    SourceFunctionUnsupported, TypeData, TypeId, TypeNodeLinks, UnsupportedSourceSyntax,
    signatures::SignatureFlags, type_records::LiteralValue,
};
use ts_parser::{ParseResult, parse_source_file};

const FLOW_SOURCE: &str = concat!(
    "function sequential(flag: boolean): number {\n",
    "  let first: number = 1, intermediate: number = first;\n",
    "  const second: number = intermediate;\n",
    "  let third: number = second;\n",
    "  if (((flag))) {\n",
    "    const result: number = third;\n",
    "    return result;\n",
    "  } else {\n",
    "    const result: number = first;\n",
    "    return result;\n",
    "  }\n",
    "}\n",
    "function assigned(flag: boolean): \"a\" | \"b\" {\n",
    "  let choice: \"a\" | \"b\" = \"a\";\n",
    "  const beforeChoice: \"a\" = choice;\n",
    "  if (flag) {\n",
    "    const thenChoice: \"a\" = choice;\n",
    "    return thenChoice;\n",
    "  } else {\n",
    "    const elseChoice: \"a\" = choice;\n",
    "    return elseChoice;\n",
    "  }\n",
    "}\n",
    "function stringTruth(value: string | undefined): string | undefined {\n",
    "  const entryString: string | undefined = value;\n",
    "  if (value) {\n",
    "    const truthyString: string = value;\n",
    "    return truthyString;\n",
    "  } else {\n",
    "    const falsyString: string | undefined = value;\n",
    "    return falsyString;\n",
    "  }\n",
    "}\n",
    "function objectTruth(value: object | undefined): object | undefined {\n",
    "  const entryObject: object | undefined = value;\n",
    "  if (value) {\n",
    "    const truthyObject: object = value;\n",
    "    return truthyObject;\n",
    "  } else {\n",
    "    const falsyObject: undefined = value;\n",
    "    return falsyObject;\n",
    "  }\n",
    "}\n",
    "function branchShadow(flag: boolean): string | number {\n",
    "  const shadow: boolean = flag;\n",
    "  if (flag) {\n",
    "    const shadow: number = 1;\n",
    "    return shadow;\n",
    "  } else {\n",
    "    const shadow: string = \"else\";\n",
    "    return shadow;\n",
    "  }\n",
    "}\n",
    "function objectCondition(value: object): number {\n",
    "  if (value) {\n",
    "    return 1;\n",
    "  } else {\n",
    "    return 2;\n",
    "  }\n",
    "}\n",
    "function literalCondition(value: \"yes\"): number {\n",
    "  if (value) {\n",
    "    return 1;\n",
    "  } else {\n",
    "    return 2;\n",
    "  }\n",
    "}\n",
    "function voidUnionCondition(value: void | boolean): number {\n",
    "  if (value) {\n",
    "    return 1;\n",
    "  } else {\n",
    "    return 2;\n",
    "  }\n",
    "}\n",
);

const DIAGNOSTIC_SOURCE: &str = concat!(
    "function ordered(gate: void): number {\n",
    "  const before: number = \"before\";\n",
    "  if (gate) {\n",
    "    const thenLocal: boolean = 0;\n",
    "    return thenLocal;\n",
    "  } else {\n",
    "    const elseLocal: string = false;\n",
    "    return elseLocal;\n",
    "  }\n",
    "}\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/source-statement-flow.ts\""),
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
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node_text<'source>(source: &'source str, parsed: &ParseResult, node: NodeRef) -> &'source str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing resolved type for {node:?}"))
}

fn variable_declarations(parsed: &ParseResult, file: FileId, expected: &str) -> Vec<NodeRef> {
    let mut declarations = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then_some((
                record.range.start.get(),
                NodeRef::new(parsed.arena.id(), file, node),
            ))
        })
        .collect::<Vec<_>>();
    declarations.sort_by_key(|(start, _)| *start);
    declarations
        .into_iter()
        .map(|(_, declaration)| declaration)
        .collect()
}

fn variable_initializer(parsed: &ParseResult, file: FileId, declaration: NodeRef) -> NodeRef {
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected variable declaration")
    };
    NodeRef::new(
        parsed.arena.id(),
        file,
        variable.initializer.expect("expected initialized variable"),
    )
}

#[test]
fn nested_function_declarations_preserve_independent_shadowed_variable_scopes() {
    let source = concat!(
        "function outer() {\n",
        "  const value = 0;\n",
        "  function inner() {\n",
        "    var value = 'inner';\n",
        "  }\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_231);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());

    let declarations = variable_declarations(&parsed, file, "value");
    let [outer, inner] = declarations.as_slice() else {
        panic!("nested functions must preserve both shadowed declarations")
    };
    let bound = context.file(file).unwrap().1;
    let outer_symbol = bound.symbol(*outer).unwrap();
    let inner_symbol = bound.symbol(*inner).unwrap();
    assert_ne!(outer_symbol, inner_symbol);
    for (symbol, expected) in [(outer_symbol, "0"), (inner_symbol, "string")] {
        let type_ = context
            .store()
            .value_symbol_links(symbol)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(context.type_to_string(type_).unwrap(), expected);
    }

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

fn unique_variable_initializer(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    let declarations = variable_declarations(parsed, file, expected);
    let [declaration] = declarations.as_slice() else {
        panic!("expected one declaration named {expected:?}")
    };
    variable_initializer(parsed, file, *declaration)
}

fn rendered_type(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    variable: &str,
) -> String {
    let initializer = unique_variable_initializer(parsed, file, variable);
    context
        .type_to_string(resolved_type(context, initializer))
        .unwrap_or_else(|error| panic!("failed to render initializer for {variable}: {error:?}"))
}

fn shadow_return_reads(parsed: &ParseResult, file: FileId) -> Vec<NodeRef> {
    let mut reads = parsed
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let NodeData::ReturnStatement(statement) = &record.data else {
                return None;
            };
            let expression = statement.expression?;
            let expression_record = parsed.arena.get(expression)?;
            let NodeData::Identifier(identifier) = &expression_record.data else {
                return None;
            };
            (identifier.text == "shadow").then_some((
                expression_record.range.start.get(),
                NodeRef::new(parsed.arena.id(), file, expression),
            ))
        })
        .collect::<Vec<_>>();
    reads.sort_by_key(|(start, _)| *start);
    reads.into_iter().map(|(_, read)| read).collect()
}

fn function_declaration(parsed: &ParseResult, file: FileId) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            matches!(&record.data, NodeData::FunctionDeclaration(_)).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .expect("expected function declaration")
}

fn node_of_kind(parsed: &ParseResult, file: FileId, kind: SyntaxKind) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap_or_else(|| panic!("expected one {kind:?} node"))
}

fn is_type_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .source_file(file)
        .and_then(|source| context.store().source_file_links(source))
        .is_some_and(|links| links.type_checked)
}

#[test]
fn final_if_flow_checks_sequential_locals_narrowing_shadowing_and_warm_state() {
    let parsed = parse_source_file(FLOW_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());

    for variable in ["intermediate", "second", "third"] {
        assert_eq!(rendered_type(&context, &parsed, file, variable), "number");
    }
    for declaration in variable_declarations(&parsed, file, "result") {
        let initializer = variable_initializer(&parsed, file, declaration);
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, initializer))
                .unwrap(),
            "number",
        );
    }

    for variable in ["beforeChoice", "thenChoice", "elseChoice"] {
        assert_eq!(rendered_type(&context, &parsed, file, variable), "\"a\"");
    }
    assert_eq!(
        rendered_type(&context, &parsed, file, "truthyString"),
        "string",
    );
    assert_eq!(
        rendered_type(&context, &parsed, file, "falsyString"),
        "string | undefined",
    );
    assert_eq!(
        rendered_type(&context, &parsed, file, "truthyObject"),
        "object",
    );
    assert_eq!(
        rendered_type(&context, &parsed, file, "falsyObject"),
        "undefined",
    );

    let shadows = variable_declarations(&parsed, file, "shadow");
    let [outer_shadow, then_shadow, else_shadow] = shadows.as_slice() else {
        panic!("expected outer, then, and else shadow declarations")
    };
    let (_, bound) = context.file(file).unwrap();
    let outer_symbol = bound.symbol(*outer_shadow).unwrap();
    let then_symbol = bound.symbol(*then_shadow).unwrap();
    let else_symbol = bound.symbol(*else_shadow).unwrap();
    assert_ne!(outer_symbol, then_symbol);
    assert_ne!(outer_symbol, else_symbol);
    assert_ne!(then_symbol, else_symbol);

    let shadow_reads = shadow_return_reads(&parsed, file);
    let [then_read, else_read] = shadow_reads.as_slice() else {
        panic!("expected one shadow return read in each branch")
    };
    assert_eq!(
        context
            .store()
            .symbol_node_links(*then_read)
            .and_then(|links| links.resolved_symbol),
        Some(then_symbol),
    );
    assert_eq!(
        context
            .store()
            .symbol_node_links(*else_read)
            .and_then(|links| links.resolved_symbol),
        Some(else_symbol),
    );

    assert!(is_type_checked(&context, file));
    let cold_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    let cold_diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        cold_counts,
    );
    assert_eq!(context.diagnostics(), &cold_diagnostics);
    assert!(is_type_checked(&context, file));
}

#[test]
fn final_if_flow_preserves_local_condition_and_return_diagnostic_order_and_anchors() {
    let parsed = parse_source_file(DIAGNOSTIC_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let diagnostics = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            let node = diagnostic.node.expect("expected node-anchored diagnostic");
            (
                diagnostic.diagnostic.code(),
                parsed.arena.get(node.node).unwrap().kind,
                node_text(DIAGNOSTIC_SOURCE, &parsed, node),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        diagnostics,
        [
            (2322, SyntaxKind::Identifier, "before"),
            (1345, SyntaxKind::Identifier, "gate"),
            (2322, SyntaxKind::Identifier, "thenLocal"),
            (2322, SyntaxKind::ReturnStatement, "return thenLocal;"),
            (2322, SyntaxKind::Identifier, "elseLocal"),
            (2322, SyntaxKind::ReturnStatement, "return elseLocal;"),
        ],
    );
    assert_eq!(
        context.diagnostics().as_slice()[1]
            .diagnostic
            .render()
            .unwrap(),
        "An expression of type 'void' cannot be tested for truthiness.",
    );
    assert!(is_type_checked(&context, file));

    let cold_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    let cold_diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        cold_counts,
    );
    assert_eq!(context.diagnostics(), &cold_diagnostics);
    assert!(is_type_checked(&context, file));
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the original source and its checked diagnostic replay together.
fn missing_else_remains_an_explicit_atomic_boundary() {
    let source = concat!(
        "function missingElse(value: string | undefined): string {\n",
        "  if (value) {\n",
        "    const result: string = value;\n",
        "    return result;\n",
        "  }\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2);
    let declaration = function_declaration(&parsed, file);
    let NodeData::FunctionDeclaration(function) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!();
    };
    let annotation = NodeRef::new(parsed.arena.id(), file, function.type_.unwrap());
    let result_read = unique_variable_initializer(&parsed, file, "result");
    let mut context = context(&parsed, file);
    let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
    assert!(context.store().value_symbol_links(owner).is_none());
    assert!(context.store().signature_links(declaration).is_none());
    assert!(!is_type_checked(&context, file));

    context.check_source_file(file).unwrap();

    assert!(is_type_checked(&context, file));
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let callable = context.get_type_at_location(declaration).unwrap();
    assert_eq!(
        context
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type,
        Some(callable),
    );
    let signature = context
        .store()
        .signature_links(declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data() else {
        panic!("expected the original function object");
    };
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    assert_eq!(
        context.store().signature(signature).unwrap().declaration(),
        Some(declaration)
    );
    assert_eq!(context.get_return_type_of_signature(signature), Ok(string));
    assert_eq!(context.get_type_from_type_node(annotation), Ok(string));
    assert_eq!(resolved_type(&context, result_read), string);
    assert_eq!(context.get_type_at_location(result_read), Ok(string));
    let parameter = NodeRef::new(parsed.arena.id(), file, function.parameters.nodes[0]);
    let parameter_owner = context.file(file).unwrap().1.symbol(parameter).unwrap();
    assert_eq!(
        context.get_symbol_at_location(result_read),
        Ok(Some(parameter_owner))
    );
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected only the missing return diagnostic");
    };
    assert_eq!(diagnostic.diagnostic.code(), 2366);
    assert_eq!(diagnostic.node, Some(annotation));
    assert_eq!(node_text(source, &parsed, annotation), "string");
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Function lacks ending return statement and return type does not include 'undefined'.",
    );
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());

    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            [
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.type_resolution_len(),
            ],
            store.value_symbol_links(owner).cloned(),
            store.signature_links(declaration).cloned(),
            [declaration, annotation, result_read].map(|node| {
                (
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                )
            }),
            store
                .source_file_links(context.source_file(file).unwrap())
                .cloned(),
            context.diagnostics().clone(),
        )
    };
    let before = snapshot(&context);
    for _ in 0..2 {
        context.recheck_source_file(file).unwrap();
        assert!(is_type_checked(&context, file));
        assert_eq!(context.get_type_at_location(declaration), Ok(callable));
        assert_eq!(context.get_return_type_of_signature(signature), Ok(string));
        assert_eq!(context.get_type_at_location(result_read), Ok(string));
        assert_eq!(
            context.get_symbol_at_location(result_read),
            Ok(Some(parameter_owner))
        );
        assert_eq!(snapshot(&context), before);
    }
}

#[test]
fn inferred_final_if_preserves_joined_return_identity() {
    let source = concat!(
        "function inferred(value: object | undefined) {\n",
        "  if (value) {\n",
        "    const result: object = value;\n",
        "    return result;\n",
        "  } else {\n",
        "    const result: undefined = value;\n",
        "    return result;\n",
        "  }\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3);
    let declaration = function_declaration(&parsed, file);
    let mut context = context(&parsed, file);
    let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();

    context.check_source_file(file).unwrap();

    assert!(context.store().value_symbol_links(owner).is_some());
    assert!(context.store().signature_links(declaration).is_some());
    assert!(context.diagnostics().is_empty());
    assert!(is_type_checked(&context, file));

    let warm = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
        context.diagnostics().as_slice().to_vec(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.diagnostics().as_slice().to_vec(),
        ),
        warm,
    );
}

#[test]
fn final_if_flow_recreates_invocation_state_after_a_later_semantic_failure() {
    let source = concat!(
        "interface Recovery {\n",
        "  (value: number, other: number): string;\n",
        "  (value: string): number;\n",
        "}\n",
        "type Broken = { fn: Recovery };\n",
        "function replay(flag: boolean): number {\n",
        "  let value: number = 1;\n",
        "  if (flag) {\n",
        "    const branch: number = value;\n",
        "    return branch;\n",
        "  } else {\n",
        "    const branch: number = value;\n",
        "    return branch;\n",
        "  }\n",
        "}\n",
        "declare const api: Broken;\n",
        "const stopped = api.fn(true);\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4);
    let call = node_of_kind(&parsed, file, SyntaxKind::CallExpression);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    let cold = final_if_recovery_state(&context, &parsed, file);
    let recovered = assert_final_if_overload_recovery(&context, &parsed, file, call);
    let argument = node_of_kind(&parsed, file, SyntaxKind::TrueKeyword);
    let range = parsed.arena.get(argument.node).unwrap().range;
    assert_eq!((range.start.get(), range.end.get()), (377, 381));
    assert_eq!(node_text(source, &parsed, argument), "true");

    // Keep the original second check, then force real invocation-state replay.
    context.check_source_file(file).unwrap();
    assert_eq!(final_if_recovery_state(&context, &parsed, file), cold);
    for _ in 0..2 {
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            assert_final_if_overload_recovery(&context, &parsed, file, call),
            recovered,
        );
        assert_eq!(final_if_recovery_state(&context, &parsed, file), cold);
        let never = context.store().intrinsic_bootstrap().unwrap().never_type;
        assert_eq!(context.get_type_at_location(call).unwrap(), never);
        assert_eq!(
            context.get_return_type_of_signature(recovered).unwrap(),
            never
        );
        assert_eq!(final_if_recovery_state(&context, &parsed, file), cold);
    }
}

fn final_if_recovery_state(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.type_predicate_len(),
            store.index_info_len(),
            store.type_alias_len(),
            store.type_resolution_len(),
        ],
        store.relation_state_snapshot(),
        context.diagnostics().clone(),
        store
            .source_file_links(context.source_file(file).unwrap())
            .cloned(),
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = NodeRef::new(parsed.arena.id(), file, id);
                (
                    node,
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.value_symbol_links(symbol).cloned(),
                    store.declared_type_links(symbol).cloned(),
                    store.type_alias_links(symbol).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .signatures()
            .map(|(id, signature)| {
                (
                    (
                        id,
                        signature.flags(),
                        signature.declaration(),
                        signature.parameters().to_vec(),
                        signature.min_argument_count(),
                        signature.resolved_min_argument_count(),
                        signature.resolved_return_type(),
                    ),
                    (
                        signature.type_parameters().to_vec(),
                        signature.this_parameter(),
                        signature.target(),
                        signature.mapper(),
                        signature.resolved_type_predicate(),
                        signature.isolated_signature_type(),
                        signature.composite().cloned(),
                    ),
                )
            })
            .collect::<Vec<_>>(),
    )
}

fn assert_recovery_source_signatures(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    call: NodeRef,
) -> [SignatureId; 2] {
    let store = context.store();
    let bound = context.file(file).unwrap().1;
    let reference = |node| NodeRef::new(parsed.arena.id(), file, node);
    let mut declarations = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::CallSignature).then_some(reference(node))
        })
        .collect::<Vec<_>>();
    declarations.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    let declarations: [NodeRef; 2] = declarations.try_into().unwrap();
    let first = parsed.arena.get(declarations[0].node).unwrap();
    let owner = reference(first.parent.unwrap());
    let NodeData::InterfaceDeclaration(interface) = &parsed.arena.get(owner.node).unwrap().data
    else {
        panic!("Recovery must own both source signatures")
    };
    assert_eq!(interface.members.nodes, declarations.map(|node| node.node));
    let owner_symbol = bound.symbol(owner).unwrap();
    let NodeData::CallExpression(syntax) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected the original property call")
    };
    let callable = resolved_type(context, reference(syntax.expression));
    let record = store.type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(owner_symbol));
    let TypeData::Interface(interface) = record.data() else {
        panic!("the callee must keep the real Recovery interface")
    };
    let signatures = declarations.map(|node| {
        let links = store.signature_links(node).unwrap();
        links.resolved_signature.signature().unwrap()
    });
    let members = &interface.reference.object.structured;
    assert_eq!(members.signatures.as_deref(), Some(signatures.as_slice()));
    assert_eq!(members.call_signature_count, 2);
    let intrinsic = store.intrinsic_bootstrap().unwrap();
    for ((declaration, id), expected_return) in declarations
        .into_iter()
        .zip(signatures)
        .zip([intrinsic.string_type, intrinsic.number_type])
    {
        assert_eq!(
            parsed.arena.get(declaration.node).unwrap().parent,
            Some(owner.node)
        );
        let NodeData::CallSignatureDeclaration(syntax) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("expected a real call-signature declaration")
        };
        let signature = store.signature(id).unwrap();
        let parameters = syntax
            .parameters
            .nodes
            .iter()
            .map(|&node| assert_recovery_parameter(context, parsed, reference(node)))
            .collect::<Vec<_>>();
        assert_eq!(signature.declaration(), Some(declaration));
        assert_eq!(signature.parameters(), parameters);
        assert_eq!(signature.resolved_return_type(), Some(expected_return));
        assert_eq!(
            resolved_type(context, reference(syntax.type_.unwrap())),
            expected_return
        );
        assert!(signature.type_parameters().is_empty());
        assert!(signature.this_parameter().is_none());
        assert!(
            !signature
                .flags()
                .contains(SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE)
        );
    }
    signatures
}

fn assert_recovery_parameter(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    parameter: NodeRef,
) -> SemanticSymbolId {
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        panic!("expected an owned source parameter")
    };
    assert!(data.question_token.is_none());
    let annotation = NodeRef::new(parameter.arena, parameter.file, data.type_.unwrap());
    let type_ = resolved_type(context, annotation);
    let store = context.store();
    let intrinsic = store.intrinsic_bootstrap().unwrap();
    match parsed.arena.get(annotation.node).unwrap().kind {
        SyntaxKind::NumberKeyword => assert_eq!(type_, intrinsic.number_type),
        SyntaxKind::StringKeyword => assert_eq!(type_, intrinsic.string_type),
        SyntaxKind::ArrayType => assert!(data.dot_dot_dot_token.is_some()),
        _ => panic!("expected a scalar parameter or the real trailing array rest"),
    }
    let symbol = context
        .file(parameter.file)
        .unwrap()
        .1
        .symbol(parameter)
        .unwrap();
    assert_eq!(
        store.value_symbol_links(symbol).unwrap().resolved_type,
        Some(type_)
    );
    symbol
}

fn assert_final_if_local_state(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    completed: bool,
) {
    let store = context.store();
    let bound = context.file(file).unwrap().1;
    let number = store.intrinsic_bootstrap().unwrap().number_type;
    let declarations = ["value", "branch"]
        .into_iter()
        .flat_map(|name| variable_declarations(parsed, file, name))
        .collect::<Vec<_>>();
    assert_eq!(declarations.len(), 3);
    let symbols = declarations
        .iter()
        .map(|&node| bound.symbol(node).unwrap())
        .collect::<Vec<_>>();
    assert_ne!(symbols[0], symbols[1]);
    assert_ne!(symbols[0], symbols[2]);
    assert_ne!(symbols[1], symbols[2]);
    for (index, (&declaration, &symbol)) in declarations.iter().zip(&symbols).enumerate() {
        if completed {
            assert_eq!(
                store.value_symbol_links(symbol).unwrap().resolved_type,
                Some(number)
            );
        } else {
            assert!(store.value_symbol_links(symbol).is_none());
        }
        let initializer = variable_initializer(parsed, file, declaration);
        let initializer_type = resolved_type(context, initializer);
        if index == 0 {
            let TypeData::Literal(literal) = store.type_payload(initializer_type).unwrap().data()
            else {
                panic!("the leading initializer must keep the original numeric literal")
            };
            assert_eq!(
                literal.value,
                LiteralValue::Number(ts_jsnum::from_string("1"))
            );
        } else {
            assert_eq!(initializer_type, number);
            if completed {
                assert_eq!(
                    store
                        .symbol_node_links(initializer)
                        .unwrap()
                        .resolved_symbol,
                    Some(symbols[0])
                );
            }
        }
    }
    let mut returns = parsed
        .arena
        .iter()
        .filter_map(|(_, record)| {
            let NodeData::ReturnStatement(statement) = &record.data else {
                return None;
            };
            Some(NodeRef::new(
                parsed.arena.id(),
                file,
                statement.expression.unwrap(),
            ))
        })
        .collect::<Vec<_>>();
    returns.sort_by_key(|node| parsed.arena.get(node.node).unwrap().range.start);
    assert_eq!(returns.len(), 2);
    for (read, symbol) in returns.into_iter().zip(&symbols[1..]) {
        assert_eq!(resolved_type(context, read), number);
        if completed {
            assert_eq!(
                store.symbol_node_links(read).unwrap().resolved_symbol,
                Some(*symbol)
            );
        }
    }
    assert_eq!(store.type_resolution_len(), 0);
    assert_eq!(is_type_checked(context, file), completed);
}

fn assert_final_if_overload_recovery(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    call: NodeRef,
) -> SignatureId {
    let visible = assert_recovery_source_signatures(context, parsed, file, call);
    let store = context.store();
    let intrinsic = store.intrinsic_bootstrap().unwrap();
    let call_links = store.signature_links(call).unwrap();
    let recovered = call_links.resolved_signature.signature().unwrap();
    assert_eq!(
        call_links,
        &SignatureLinks {
            resolved_signature: ResolvedSignatureState::Resolved(recovered),
            ..SignatureLinks::default()
        }
    );
    assert!(!visible.contains(&recovered));
    let signature = store.signature(recovered).unwrap();
    let original = store.signature(visible[0]).unwrap();
    assert_eq!(original.flags(), SignatureFlags::NONE);
    assert_eq!(original.min_argument_count(), 2);
    assert_eq!(original.parameters().len(), 2);
    let second = store.signature(visible[1]).unwrap();
    assert_eq!(second.flags(), SignatureFlags::NONE);
    assert_eq!(second.min_argument_count(), 1);
    assert_eq!(second.parameters().len(), 1);
    assert_eq!(
        signature.flags(),
        SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE
    );
    assert_eq!(signature.declaration(), original.declaration());
    assert_eq!(signature.min_argument_count(), 1);
    assert_eq!(signature.parameters().len(), 2);
    assert_eq!(signature.resolved_return_type(), Some(intrinsic.never_type));
    assert_eq!(
        store.type_node_links(call),
        Some(&TypeNodeLinks {
            resolved_type: Some(intrinsic.never_type),
            ..TypeNodeLinks::default()
        })
    );
    assert!(signature.type_parameters().is_empty());
    assert!(signature.this_parameter().is_none());
    assert!(signature.target().is_none());
    assert!(signature.mapper().is_none());
    assert!(signature.composite().is_none());
    assert!(signature.resolved_type_predicate().is_none());
    assert!(signature.isolated_signature_type().is_none());
    let mut parameter_types = Vec::new();
    for (&parameter, &source) in signature.parameters().iter().zip(original.parameters()) {
        assert_ne!(parameter, source);
        let record = store.symbol(parameter).unwrap();
        let source_record = store.symbol(source).unwrap();
        assert_eq!(
            record.flags(),
            source_record.flags() | SymbolFlags::TRANSIENT
        );
        assert_eq!(record.declarations(), source_record.declarations());
        assert_eq!(
            record.value_declaration(),
            source_record.value_declaration()
        );
        assert_eq!(record.parent(), source_record.parent());
        assert_eq!(record.name(), source_record.name());
        let links = store.value_symbol_links(parameter).unwrap();
        assert_eq!(links.target, Some(source));
        assert!(links.mapper.is_none());
        assert!(links.write_type.is_none());
        parameter_types.push(links.resolved_type.unwrap());
    }
    let TypeData::Union(union) = store.type_payload(parameter_types[0]).unwrap().data() else {
        panic!("the recovery parameter must combine both real scalar parameters")
    };
    let mut expected = [intrinsic.string_type, intrinsic.number_type];
    expected.sort_unstable();
    assert_eq!(union.union.types, expected);
    assert_eq!(parameter_types[1], intrinsic.number_type);
    assert_overload_argument_diagnostic(context, parsed, file);
    assert_final_if_local_state(context, parsed, file, true);
    let stopped = variable_declarations(parsed, file, "stopped");
    let [stopped] = stopped.as_slice() else {
        panic!("expected the original call result binding")
    };
    let symbol = context.file(file).unwrap().1.symbol(*stopped).unwrap();
    assert_eq!(
        store.value_symbol_links(symbol).unwrap().resolved_type,
        Some(intrinsic.never_type)
    );
    recovered
}

fn assert_overload_argument_diagnostic(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
) {
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("only the one-argument overload must supply an argument diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(diagnostic.diagnostic.arguments, ["boolean", "string"]);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'boolean' is not assignable to parameter of type 'string'."
    );
    assert_eq!(
        diagnostic.node,
        Some(node_of_kind(parsed, file, SyntaxKind::TrueKeyword))
    );
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.diagnostic.details.is_empty());
    assert!(diagnostic.related_information.is_empty());
}

fn assert_unsupported_rest_recovery(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    call: NodeRef,
) {
    let signatures = assert_recovery_source_signatures(context, parsed, file, call);
    let store = context.store();
    let first = store.signature(signatures[0]).unwrap();
    let second = store.signature(signatures[1]).unwrap();
    assert_eq!(first.flags(), SignatureFlags::HAS_REST_PARAMETER);
    assert_eq!(first.min_argument_count(), 2);
    assert_eq!(first.parameters().len(), 3);
    assert_eq!(second.flags(), SignatureFlags::NONE);
    assert_eq!(second.min_argument_count(), 1);
    assert_eq!(second.parameters().len(), 1);
    assert_ne!(first.resolved_return_type(), second.resolved_return_type());
    let rest = store
        .value_symbol_links(first.parameters()[2])
        .unwrap()
        .resolved_type
        .unwrap();
    let TypeData::TypeReference(array) = store.type_payload(rest).unwrap().data() else {
        panic!("the real trailing rest annotation must be Array<number>")
    };
    assert_eq!(array.object.target, Some(context.global_types().array_type));
    assert_eq!(
        array.resolved_type_arguments.as_deref(),
        Some([store.intrinsic_bootstrap().unwrap().number_type].as_slice())
    );
    for (name, target) in [
        ("Array", context.global_types().array_type),
        ("ReadonlyArray", context.global_types().readonly_array_type),
    ] {
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::InterfaceDeclaration(interface) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &parsed.arena.get(interface.name)?.data
                else {
                    return None;
                };
                (identifier.text == name).then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .unwrap();
        let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
        assert_eq!(store.type_payload(target).unwrap().symbol(), Some(owner));
    }
    assert!(store.type_node_links(call).is_none());
    assert!(store.signature_links(call).is_none());
    assert!(context.diagnostics().is_empty());
    assert_final_if_local_state(context, parsed, file, false);
}

#[test]
fn final_if_flow_retries_after_unsupported_mixed_return_rest_overload_recovery() {
    let source = concat!(
        "interface Array<T> {} interface ReadonlyArray<T> {}\n",
        "interface Recovery {\n",
        "  (value: number, other: number, ...more: number[]): string;\n",
        "  (value: string): number;\n",
        "}\n",
        "type Broken = { fn: Recovery };\n",
        "function replay(flag: boolean): number {\n",
        "  let value: number = 1;\n",
        "  if (flag) {\n",
        "    const branch: number = value;\n",
        "    return branch;\n",
        "  } else {\n",
        "    const branch: number = value;\n",
        "    return branch;\n",
        "  }\n",
        "}\n",
        "declare const api: Broken;\n",
        "const stopped = api.fn(true);\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8_232);
    let call = node_of_kind(&parsed, file, SyntaxKind::CallExpression);
    let mut context = context(&parsed, file);
    let mut first_state = None;

    for _ in 0..2 {
        assert_eq!(
            context.check_source_file(file),
            Err(SourceCheckError::Call(call))
        );
        assert_unsupported_rest_recovery(&context, &parsed, file, call);
        let state = final_if_recovery_state(&context, &parsed, file);
        if let Some(first) = &first_state {
            assert_eq!(&state, first);
        } else {
            first_state = Some(state);
        }
    }
}

#[test]
fn function_declaration_flow_starts_captured_variables_at_their_declared_types() {
    let source = concat!(
        "const fixed: string | number = \"fixed\";\n",
        "let mutable: string | number = \"mutable\";\n",
        "function capture(flag: boolean): string {\n",
        "  const fromConst: string = fixed;\n",
        "  const fromLet: string = mutable;\n",
        "  if (flag) {\n",
        "    return \"ok\";\n",
        "  } else {\n",
        "    return mutable;\n",
        "  }\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(5);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let diagnostics = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            let node = diagnostic.node.expect("expected node-anchored diagnostic");
            (
                diagnostic.diagnostic.code(),
                parsed.arena.get(node.node).unwrap().kind,
                node_text(source, &parsed, node),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        diagnostics,
        [
            (2322, SyntaxKind::Identifier, "fromConst"),
            (2322, SyntaxKind::Identifier, "fromLet"),
            (2322, SyntaxKind::ReturnStatement, "return mutable;"),
        ],
    );
    assert!(is_type_checked(&context, file));

    let cold_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    let cold_diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        cold_counts,
    );
    assert_eq!(context.diagnostics(), &cold_diagnostics);
}

#[test]
fn structural_thenable_condition_remains_a_stable_semantic_boundary() {
    let source = concat!(
        "type Thenable = { then: (onfulfilled: (value: number) => unknown) => unknown };\n",
        "function structural(value: Thenable): number {\n",
        "  if (value) {\n",
        "    return 1;\n",
        "  } else {\n",
        "    return 2;\n",
        "  }\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(6);
    let mut context = context(&parsed, file);

    let first = context.check_source_file(file).unwrap_err();
    assert!(matches!(
        first,
        SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
            SourceFunctionUnsupported::FunctionBody(_)
        ))
    ));
    assert!(context.diagnostics().is_empty());
    assert!(!is_type_checked(&context, file));
    let first_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );

    assert_eq!(context.check_source_file(file), Err(first));
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        first_counts,
    );
    assert!(context.diagnostics().is_empty());
    assert!(!is_type_checked(&context, file));
}

#[test]
fn joined_if_flow_restores_the_named_union_before_trailing_statements() {
    let source = concat!(
        "type Choice = \"yes\" | \"\" | undefined;\n",
        "function joined(value: Choice): Choice {\n",
        "  const before: Choice = value;\n",
        "  if (((value))) {\n",
        "    const truthy: \"yes\" = value;\n",
        "  } else {\n",
        "    const falsy: \"\" | undefined = value;\n",
        "  }\n",
        "  const after: Choice = value;\n",
        "  return value;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(7);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    assert_eq!(rendered_type(&context, &parsed, file, "before"), "Choice");
    assert_eq!(rendered_type(&context, &parsed, file, "truthy"), "\"yes\"");
    assert_eq!(
        rendered_type(&context, &parsed, file, "falsy"),
        "\"\" | undefined",
    );
    assert_eq!(rendered_type(&context, &parsed, file, "after"), "Choice");
    assert!(is_type_checked(&context, file));

    let cold_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    let cold_diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        cold_counts,
    );
    assert_eq!(context.diagnostics(), &cold_diagnostics);
}

#[test]
fn joined_if_flow_preserves_branch_then_trailing_diagnostic_order() {
    let source = concat!(
        "type Choice = \"yes\" | \"\" | undefined;\n",
        "function joinedErrors(value: Choice): Choice {\n",
        "  if (value) {\n",
        "    const badTruthy: \"\" = value;\n",
        "  } else {\n",
        "    const badFalsy: \"yes\" = value;\n",
        "  }\n",
        "  const badAfter: \"yes\" = value;\n",
        "  return value;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    let diagnostics = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            let node = diagnostic.node.expect("expected node-anchored diagnostic");
            (
                diagnostic.diagnostic.code(),
                parsed.arena.get(node.node).unwrap().kind,
                node_text(source, &parsed, node),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        diagnostics,
        [
            (2322, SyntaxKind::Identifier, "badTruthy"),
            (2322, SyntaxKind::Identifier, "badFalsy"),
            (2322, SyntaxKind::Identifier, "badAfter"),
        ],
    );
    assert!(is_type_checked(&context, file));

    let cold_counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    let cold_diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        cold_counts,
    );
    assert_eq!(context.diagnostics(), &cold_diagnostics);
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the original named union and each narrowed path together.
fn joined_if_branch_returns_remain_an_atomic_boundary() {
    let source = concat!(
        "type Choice = \"yes\" | \"\" | undefined;\n",
        "function branchReturn(value: Choice): Choice {\n",
        "  if (value) {\n",
        "    return value;\n",
        "  } else {\n",
        "    const falsy: \"\" | undefined = value;\n",
        "  }\n",
        "  const after: Choice = value;\n",
        "  return value;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(9);
    let declaration = function_declaration(&parsed, file);
    let NodeData::FunctionDeclaration(function) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        unreachable!();
    };
    let annotation = NodeRef::new(parsed.arena.id(), file, function.type_.unwrap());
    let parameter = NodeRef::new(parsed.arena.id(), file, function.parameters.nodes[0]);
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!();
    };
    let parameter_annotation = NodeRef::new(parsed.arena.id(), file, parameter_data.type_.unwrap());
    let alias = node_of_kind(&parsed, file, SyntaxKind::TypeAliasDeclaration);
    let falsy = variable_declarations(&parsed, file, "falsy")[0];
    let after = variable_declarations(&parsed, file, "after")[0];
    let falsy_read = variable_initializer(&parsed, file, falsy);
    let after_read = variable_initializer(&parsed, file, after);
    let NodeData::VariableDeclaration(after_data) = &parsed.arena.get(after.node).unwrap().data
    else {
        unreachable!();
    };
    let after_annotation = NodeRef::new(parsed.arena.id(), file, after_data.type_.unwrap());
    let mut returns = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::ReturnStatement(returned) = &record.data else {
                return None;
            };
            Some((
                record.range.start.get(),
                NodeRef::new(parsed.arena.id(), file, id),
                NodeRef::new(parsed.arena.id(), file, returned.expression.unwrap()),
            ))
        })
        .collect::<Vec<_>>();
    returns.sort_by_key(|&(start, _, _)| start);
    assert_eq!(returns.len(), 2);
    let then_read = returns[0].2;
    let final_read = returns[1].2;
    let mut context = context(&parsed, file);
    let (_, bound) = context.file(file).unwrap();
    let owner = bound.symbol(declaration).unwrap();
    let parameter_owner = bound.symbol(parameter).unwrap();
    let alias_owner = bound.symbol(alias).unwrap();
    let after_owner = bound.symbol(after).unwrap();
    assert!(context.store().signature_links(declaration).is_none());
    assert!(!is_type_checked(&context, file));

    context.check_source_file(file).unwrap();

    assert!(is_type_checked(&context, file));
    assert!(context.diagnostics().is_empty());
    let choice = context.get_declared_type_of_symbol(alias_owner).unwrap();
    assert_eq!(context.type_to_string(choice).unwrap(), "Choice");
    let alias_id = context
        .store()
        .type_payload(choice)
        .unwrap()
        .alias()
        .unwrap();
    assert_eq!(
        context.store().type_alias(alias_id).unwrap().symbol(),
        Some(alias_owner)
    );
    assert_eq!(
        context.store().symbol(alias_owner).unwrap().declarations(),
        Some(&[alias][..])
    );
    let callable = context.get_type_at_location(declaration).unwrap();
    assert_eq!(
        context.store().type_payload(callable).unwrap().symbol(),
        Some(owner)
    );
    assert_eq!(
        context.store().symbol(owner).unwrap().declarations(),
        Some(&[declaration][..])
    );
    let signature = context
        .store()
        .signature_links(declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data() else {
        panic!("expected the original function object");
    };
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.parameters(), &[parameter_owner]);
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(
        context
            .store()
            .symbol(parameter_owner)
            .unwrap()
            .declarations(),
        Some(&[parameter][..])
    );
    for annotation in [annotation, parameter_annotation, after_annotation] {
        assert_eq!(context.get_type_from_type_node(annotation), Ok(choice));
        assert_eq!(
            context
                .store()
                .symbol_node_links(annotation)
                .unwrap()
                .resolved_symbol,
            Some(alias_owner)
        );
    }
    for value_owner in [parameter_owner, after_owner] {
        assert_eq!(
            context
                .store()
                .value_symbol_links(value_owner)
                .unwrap()
                .resolved_type,
            Some(choice)
        );
    }
    assert_eq!(context.get_return_type_of_signature(signature), Ok(choice));
    let truthy = context.get_type_at_location(then_read).unwrap();
    let falsy_type = context.get_type_at_location(falsy_read).unwrap();
    assert_eq!(context.type_to_string(truthy).unwrap(), "\"yes\"");
    assert_eq!(
        context.type_to_string(falsy_type).unwrap(),
        "\"\" | undefined"
    );
    assert_ne!(truthy, falsy_type);
    assert_ne!(choice, falsy_type);
    for location in [falsy_read, after_read, final_read] {
        assert_eq!(resolved_type(&context, location), falsy_type);
        assert_eq!(context.get_type_at_location(location), Ok(falsy_type));
    }
    for location in [then_read, falsy_read, after_read, final_read] {
        assert_eq!(
            context.get_symbol_at_location(location),
            Ok(Some(parameter_owner))
        );
    }
    let (_, bound) = context.file(file).unwrap();
    assert_ne!(bound.flow_at(returns[0].1), bound.flow_at(returns[1].1));
    assert_eq!(bound.flow_graph().container_end(declaration), None);
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            [
                store.type_len(),
                store.type_alias_len(),
                store.mapper_len(),
                store.signature_len(),
                store.type_resolution_len(),
            ],
            [owner, parameter_owner, after_owner]
                .map(|symbol| store.value_symbol_links(symbol).cloned()),
            store.signature_links(declaration).cloned(),
            [
                annotation,
                parameter_annotation,
                after_annotation,
                then_read,
                falsy_read,
                after_read,
                final_read,
            ]
            .map(|node| {
                (
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                )
            }),
            store
                .source_file_links(context.source_file(file).unwrap())
                .cloned(),
            context.diagnostics().clone(),
        )
    };
    let before = snapshot(&context);
    for _ in 0..2 {
        context.recheck_source_file(file).unwrap();
        assert!(is_type_checked(&context, file));
        assert_eq!(context.get_type_at_location(declaration), Ok(callable));
        assert_eq!(context.get_return_type_of_signature(signature), Ok(choice));
        assert_eq!(context.get_type_at_location(then_read), Ok(truthy));
        for location in [falsy_read, after_read, final_read] {
            assert_eq!(context.get_type_at_location(location), Ok(falsy_type));
            assert_eq!(
                context.get_symbol_at_location(location),
                Ok(Some(parameter_owner))
            );
        }
        assert_eq!(snapshot(&context), before);
    }
}

#[test]
fn final_if_accepts_direct_and_mixed_return_branches() {
    let source = concat!(
        "function direct(value: string | undefined): string | undefined {\n",
        "  if (value) return value;\n",
        "  else return value;\n",
        "}\n",
        "function mixedThen(value: string | undefined): string | undefined {\n",
        "  if (value) {\n",
        "    const narrowed: string = value;\n",
        "    return narrowed;\n",
        "  } else return value;\n",
        "}\n",
        "function mixedElse(value: string | undefined): string | undefined {\n",
        "  if (value) return value;\n",
        "  else {\n",
        "    const remaining: string | undefined = value;\n",
        "    return remaining;\n",
        "  }\n",
        "}\n",
        "function typed(value: string | number): string | number {\n",
        "  if (typeof value === \"string\") return value;\n",
        "  else return value;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(10);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());
    assert_eq!(rendered_type(&context, &parsed, file, "narrowed"), "string");
    assert_eq!(
        rendered_type(&context, &parsed, file, "remaining"),
        "string | undefined",
    );

    let mut returns = parsed
        .arena
        .iter()
        .filter_map(|(_, node)| {
            let NodeData::ReturnStatement(statement) = &node.data else {
                return None;
            };
            statement.expression.map(|expression| {
                (
                    node.range.start.get(),
                    NodeRef::new(parsed.arena.id(), file, expression),
                )
            })
        })
        .collect::<Vec<_>>();
    returns.sort_by_key(|(start, _)| *start);
    let return_types = returns
        .into_iter()
        .map(|(_, expression)| {
            context
                .type_to_string(resolved_type(&context, expression))
                .unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        return_types,
        [
            "string",
            "string | undefined",
            "string",
            "string | undefined",
            "string",
            "string | undefined",
            "string",
            "number",
        ],
    );

    let counts = (
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
        counts,
    );
}

#[test]
fn assignments_to_type_only_namespaces_report_ts2708_and_keep_expression_types() {
    let source = "namespace A {}\nA = undefined;\n";
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_160);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one namespace assignment diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2708);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Cannot use namespace 'A' as a value.",
    );
    assert_eq!(node_text(source, &parsed, diagnostic.node.unwrap()), "A",);

    let assignment = node_of_kind(&parsed, file, SyntaxKind::BinaryExpression);
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(assignment.node).unwrap().data
    else {
        panic!("expected namespace assignment")
    };
    let left = NodeRef::new(parsed.arena.id(), file, binary.left);
    let right = NodeRef::new(parsed.arena.id(), file, binary.right);
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, left))
            .unwrap(),
        "any",
    );
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, assignment))
            .unwrap(),
        "undefined",
    );
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, right))
            .unwrap(),
        "undefined",
    );

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn numeric_runtime_namespace_variables_keep_inferred_and_literal_types() {
    let parsed = parse_source_file("namespace Values { var count = 10; }");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_161);
    let mut context = context(&parsed, file);
    let declarations = variable_declarations(&parsed, file, "count");
    let [declaration] = declarations.as_slice() else {
        panic!("expected one namespace variable")
    };
    let declaration = *declaration;
    let initializer = variable_initializer(&parsed, file, declaration);
    let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    assert_eq!(
        context
            .type_to_string(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .and_then(|links| links.resolved_type)
                    .unwrap(),
            )
            .unwrap(),
        "number",
    );
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, initializer))
            .unwrap(),
        "10",
    );

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

#[test]
fn annotated_namespace_objects_keep_interface_and_literal_property_types() {
    let parsed = parse_source_file(concat!(
        "namespace Values { ",
        "interface Shape { salt: number; pepper: number; } ",
        "var value: Shape = { salt: 2, pepper: 0 }; ",
        "}",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_162);
    let mut context = context(&parsed, file);
    let declarations = variable_declarations(&parsed, file, "value");
    let [declaration] = declarations.as_slice() else {
        panic!("expected one annotated namespace variable")
    };
    let declaration = *declaration;
    let initializer = variable_initializer(&parsed, file, declaration);
    let symbol = context.file(file).unwrap().1.symbol(declaration).unwrap();

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    assert_eq!(
        context
            .type_to_string(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .and_then(|links| links.resolved_type)
                    .unwrap(),
            )
            .unwrap(),
        "Shape",
    );
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, initializer))
            .unwrap(),
        "{ salt: number; pepper: number; }",
    );
    let NodeData::ObjectLiteralExpression(object) =
        &parsed.arena.get(initializer.node).unwrap().data
    else {
        panic!("expected an object initializer")
    };
    for (property, expected) in object.properties.nodes.iter().zip(["2", "0"]) {
        let NodeData::PropertyAssignment(property) = &parsed.arena.get(*property).unwrap().data
        else {
            panic!("expected a numeric object property")
        };
        let value = NodeRef::new(parsed.arena.id(), file, property.initializer);
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, value))
                .unwrap(),
            expected,
        );
    }

    let warm = (
        context.store().type_len(),
        context.store().symbol_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().symbol_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}
