use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "function withDefault(seed: number, value: number = seed + 1): number { return value; }\n",
    "function incompatible(value: number = 'wrong'): number { return value; }\n",
    "function trailingBeforeRequired(value: number = 2, required: string,): void {}\n",
    "const arrow = (seed: number, value: number = seed + 2): number => value;\n",
    "const omitted: number = withDefault(1);\n",
    "const explicitUndefined: number = withDefault(1, undefined);\n",
    "const supplied: number = withDefault(1, 4);\n",
    "const arrowOmitted: number = arrow(1);\n",
    "const trailingCall: void = trailingBeforeRequired(undefined, 'ready');\n",
    "const wrongCall: number = withDefault(1, 'bad');\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/parameter-initializers.ts\""),
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

fn initialized_parameter(
    source: &str,
    parsed: &ParseResult,
    file: FileId,
    initializer_text: &str,
) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::ParameterDeclaration(parameter) = &record.data else {
                return None;
            };
            let initializer = parameter.initializer?;
            let initializer = NodeRef::new(parsed.arena.id(), file, initializer);
            (node_text(source, parsed, initializer) == initializer_text)
                .then_some((NodeRef::new(parsed.arena.id(), file, node), initializer))
        })
        .unwrap_or_else(|| panic!("missing initialized parameter {initializer_text:?}"))
}

fn variable_initializer(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected)
                .then_some(variable.initializer)
                .flatten()
                .map(|initializer| NodeRef::new(parsed.arena.id(), file, initializer))
        })
        .unwrap_or_else(|| panic!("missing variable initializer for {expected}"))
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing resolved type for {node:?}"))
}

#[test]
#[allow(clippy::too_many_lines)] // One source checks assignment, scope, calls, and warm identity.
fn default_parameter_initializers_check_assignability_scope_calls_and_warm_state() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let diagnostics = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.diagnostic.code(),
                node_text(SOURCE, &parsed, diagnostic.node.unwrap()),
                diagnostic.diagnostic.render().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        diagnostics,
        [
            (
                2322,
                "value: number = 'wrong'",
                "Type 'string' is not assignable to type 'number'.".to_owned(),
            ),
            (
                2345,
                "'bad'",
                "Argument of type 'string' is not assignable to parameter of type 'number'."
                    .to_owned(),
            ),
        ]
    );

    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    for initializer_text in ["seed + 1", "'wrong'", "seed + 2"] {
        let (parameter, initializer) =
            initialized_parameter(SOURCE, &parsed, file, initializer_text);
        assert!(context.store().type_node_links(initializer).is_some());
        let (_, bound) = context.file(file).unwrap();
        let symbol = bound.symbol(parameter).unwrap();
        assert_eq!(
            context
                .store()
                .value_symbol_links(symbol)
                .and_then(|links| links.resolved_type),
            Some(number),
            "the parameter body type must exclude the call-only undefined",
        );
    }

    let earlier_parameter_reads = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::Identifier(identifier) = &record.data else {
                return None;
            };
            let parent = record.parent.and_then(|parent| parsed.arena.get(parent))?;
            (identifier.text == "seed" && parent.kind == SyntaxKind::BinaryExpression)
                .then_some(NodeRef::new(parsed.arena.id(), file, node))
        })
        .collect::<Vec<_>>();
    assert_eq!(earlier_parameter_reads.len(), 2);
    for read in earlier_parameter_reads {
        assert_eq!(resolved_type(&context, read), number);
        assert!(
            context
                .store()
                .symbol_node_links(read)
                .is_some_and(|links| links.resolved_symbol.is_some())
        );
    }

    for name in [
        "omitted",
        "explicitUndefined",
        "supplied",
        "arrowOmitted",
        "wrongCall",
    ] {
        assert_eq!(
            resolved_type(&context, variable_initializer(&parsed, file, name)),
            number,
            "call result for {name}",
        );
    }

    let body_reads = parsed
        .arena
        .iter()
        .filter_map(|(_, record)| match &record.data {
            NodeData::ReturnStatement(statement) => statement.expression,
            NodeData::ArrowFunction(arrow)
                if parsed
                    .arena
                    .get(arrow.body)
                    .is_some_and(|body| body.kind == SyntaxKind::Identifier) =>
            {
                Some(arrow.body)
            }
            _ => None,
        })
        .map(|node| NodeRef::new(parsed.arena.id(), file, node))
        .collect::<Vec<_>>();
    assert_eq!(body_reads.len(), 3);
    assert!(
        body_reads
            .into_iter()
            .all(|body| resolved_type(&context, body) == number)
    );

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
fn unsupported_initializer_and_arrow_body_retries_do_not_publish_partial_state() {
    for (index, source) in [
        "function unsupported(seed: number, value: number = true ? seed : 0): number { return value; }",
        "const unsupported = (seed: number, value: number = seed): string => typeof value;",
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(10 + u32::try_from(index).unwrap());
        let mut context = context(&parsed, file);
        let before = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        );

        if index == 1 {
            let counts = |context: &CanonicalCheckerContext<'_>| {
                (
                    context.store().type_len(),
                    context.store().mapper_len(),
                    context.store().signature_len(),
                )
            };
            context.check_source_file(file).unwrap();
            let cold = counts(&context);
            assert!(cold.0 <= before.0 + 2);
            assert_eq!(cold.1, before.1);
            assert!(cold.2 <= before.2 + 1);
            assert!(context.diagnostics().is_empty());
            context.check_source_file(file).unwrap();
            assert_eq!(counts(&context), cold);
            assert!(context.diagnostics().is_empty());

            let callable = "(seed: number, value?: number) => string";
            let typeof_display = concat!(
                "\"bigint\" | \"boolean\" | \"function\" | \"number\" | ",
                "\"object\" | \"string\" | \"symbol\" | \"undefined\"",
            );
            for (kind, start, end, display, expected_symbol) in [
                (SyntaxKind::Identifier, 6, 17, callable, Some("unsupported")),
                (SyntaxKind::ArrowFunction, 20, 80, callable, None),
                (SyntaxKind::Parameter, 21, 33, "number", None),
                (SyntaxKind::Identifier, 21, 25, "number", Some("seed")),
                (SyntaxKind::Parameter, 35, 55, "number", None),
                (SyntaxKind::Identifier, 35, 40, "number", Some("value")),
                (SyntaxKind::Identifier, 51, 55, "number", Some("seed")),
                (SyntaxKind::TypeOfExpression, 68, 80, typeof_display, None),
                (SyntaxKind::Identifier, 75, 80, "number", Some("value")),
            ] {
                let node = parsed
                    .arena
                    .iter()
                    .find_map(|(node, record)| {
                        (record.kind == kind
                            && record.range.start.get() == start
                            && record.range.end.get() == end)
                            .then_some(NodeRef::new(parsed.arena.id(), file, node))
                    })
                    .unwrap();
                let type_ = context.get_type_at_location(node).unwrap();
                let symbol = context.get_symbol_at_location(node).unwrap();
                assert_eq!(context.type_to_string(type_).unwrap(), display);
                if kind != SyntaxKind::Parameter {
                    let symbol_name = symbol
                        .and_then(|symbol| context.store().symbol(symbol))
                        .and_then(|symbol| symbol.name().as_utf8());
                    assert_eq!(symbol_name, expected_symbol);
                }
                assert_eq!(context.get_type_at_location(node), Ok(type_));
                assert_eq!(context.get_symbol_at_location(node), Ok(symbol));
            }
            assert_eq!(counts(&context), cold);
            assert!(context.diagnostics().is_empty());
            continue;
        }

        let first = context.check_source_file(file).unwrap_err();
        assert!(matches!(first, SourceCheckError::Unsupported(_)));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
            ),
            before,
        );
        assert!(context.diagnostics().is_empty());

        let second = context.check_source_file(file).unwrap_err();
        assert_eq!(second, first);
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
            ),
            before,
        );
        assert!(context.diagnostics().is_empty());
    }
}

fn inferred_string_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/inferred-parameter-initializers.ts\""),
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
            no_implicit_any: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn inferred_parameter_reads(
    parsed: &ParseResult,
    file: FileId,
    parameter: NodeRef,
) -> Vec<NodeRef> {
    let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        panic!("expected a parameter declaration")
    };
    let NodeData::Identifier(name) = &parsed.arena.get(parameter.name).unwrap().data else {
        panic!("expected an identifier parameter")
    };
    parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            let NodeData::Identifier(identifier) = &record.data else {
                return None;
            };
            (node != parameter.name && identifier.text == name.text).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .collect()
}

fn assert_inferred_string_parameter(
    source: &str,
    parsed: &ParseResult,
    file: FileId,
    context: &mut CanonicalCheckerContext<'_>,
    initializer_text: &str,
    minimum_arguments: i32,
    parameter_count: usize,
) -> NodeRef {
    let (parameter, initializer) = initialized_parameter(source, parsed, file, initializer_text);
    let record = parsed.arena.get(parameter.node).unwrap();
    let NodeData::ParameterDeclaration(data) = &record.data else {
        panic!("expected a parameter declaration")
    };
    assert!(data.type_.is_none());
    let declaration = NodeRef::new(parsed.arena.id(), file, record.parent.unwrap());
    assert_eq!(
        parsed.arena.get(declaration.node).unwrap().kind,
        SyntaxKind::FunctionDeclaration
    );
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let symbol = context.file(file).unwrap().1.symbol(parameter).unwrap();
    assert_eq!(
        context
            .store()
            .value_symbol_links(symbol)
            .and_then(|links| links.resolved_type),
        Some(string),
    );
    let reads = inferred_parameter_reads(parsed, file, parameter);
    assert!(!reads.is_empty());
    for read in reads {
        assert_eq!(resolved_type(context, read), string);
        assert_eq!(context.get_type_at_location(read), Ok(string));
        assert_eq!(context.get_symbol_at_location(read), Ok(Some(symbol)));
    }

    let literal = resolved_type(context, initializer);
    assert_ne!(literal, string);
    assert_eq!(context.type_to_string(literal).unwrap(), initializer_text);
    assert_eq!(context.get_type_at_location(initializer), Ok(literal));
    let signature_id = context
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the declaration must retain its signature");
    let signature = context.store().signature(signature_id).unwrap();
    assert_eq!(signature.declaration(), Some(declaration));
    assert!(signature.parameters().contains(&symbol));
    assert_eq!(signature.parameters().len(), parameter_count);
    assert_eq!(signature.min_argument_count(), minimum_arguments);
    assert!(!signature.has_rest_parameter());
    declaration
}

fn assert_inferred_default_replay(
    parsed: &ParseResult,
    file: FileId,
    context: &mut CanonicalCheckerContext<'_>,
    queries: &[(NodeRef, TypeId)],
) {
    let nodes = parsed
        .arena
        .iter()
        .map(|(node, _)| NodeRef::new(parsed.arena.id(), file, node))
        .collect::<Vec<_>>();
    let mut symbols = Vec::new();
    for node in &nodes {
        if let Some(symbol) = context.file(file).unwrap().1.symbol(*node)
            && !symbols.contains(&symbol)
        {
            symbols.push(symbol);
        }
    }
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            (
                store.type_len(),
                store.mapper_len(),
                store.signature_len(),
                store.symbol_len(),
                store.symbol_store().symbol_table_len(),
                store.type_predicate_len(),
                store.index_info_len(),
                store.relation_state_snapshot(),
            ),
            nodes
                .iter()
                .map(|node| {
                    (
                        *node,
                        store.node_links(*node).cloned(),
                        store.type_node_links(*node).cloned(),
                        store.symbol_node_links(*node).cloned(),
                        store.signature_links(*node).cloned(),
                        store
                            .signature_links(*node)
                            .and_then(|links| links.resolved_signature.signature())
                            .and_then(|signature| store.signature(signature))
                            .map(|signature| {
                                (
                                    signature.declaration(),
                                    signature.parameters().to_vec(),
                                    signature.min_argument_count(),
                                    signature.resolved_min_argument_count(),
                                    signature.has_rest_parameter(),
                                    signature.resolved_return_type(),
                                )
                            }),
                    )
                })
                .collect::<Vec<_>>(),
            symbols
                .iter()
                .map(|symbol| (*symbol, store.value_symbol_links(*symbol).cloned()))
                .collect::<Vec<_>>(),
            store
                .source_file_links(context.source_file(file).unwrap())
                .cloned(),
            context.diagnostics().clone(),
        )
    };
    let before = snapshot(context);
    for _ in 0..2 {
        for (node, expected) in queries {
            assert_eq!(context.get_type_at_location(*node), Ok(*expected));
        }
        context.check_source_file(file).unwrap();
        assert_eq!(snapshot(context), before);
        context.recheck_source_file(file).unwrap();
        assert_eq!(snapshot(context), before);
    }
}

#[test]
fn inferred_string_defaults_keep_body_types_and_optional_calls() {
    let source = concat!(
        "function normalizeWindowsPath(input = \"\") { return input; }\n",
        "function hasTrailingSlash(path = \"/\") { return path === \"/\"; }\n",
        "const omitted: string = normalizeWindowsPath();\n",
        "const explicitUndefined: string = normalizeWindowsPath(undefined);\n",
        "const supplied: string = normalizeWindowsPath(\"x\");\n",
        "const omittedSlash: boolean = hasTrailingSlash();\n",
        "const undefinedSlash: boolean = hasTrailingSlash(undefined);\n",
        "const suppliedSlash: boolean = hasTrailingSlash(\"x\");\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_940);
    let (parameter, _) = initialized_parameter(source, &parsed, file, "\"\"");
    let reads = inferred_parameter_reads(&parsed, file, parameter);
    assert_eq!(reads.len(), 1);
    let first_call = variable_initializer(&parsed, file, "omitted");
    let declaration = NodeRef::new(
        parsed.arena.id(),
        file,
        parsed.arena.get(parameter.node).unwrap().parent.unwrap(),
    );
    for first_query in [None, Some(reads[0]), Some(first_call), Some(declaration)] {
        let mut context = inferred_string_context(&parsed, file);
        let cold = first_query.map(|node| (node, context.get_type_at_location(node).unwrap()));
        context.check_source_file(file).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let boolean = context.store().intrinsic_bootstrap().unwrap().boolean_type;
        let text_declaration =
            assert_inferred_string_parameter(source, &parsed, file, &mut context, "\"\"", 0, 1);
        let slash_declaration =
            assert_inferred_string_parameter(source, &parsed, file, &mut context, "\"/\"", 0, 1);
        let mut queries = vec![(reads[0], string)];
        for (name, expected, declaration) in [
            ("omitted", string, text_declaration),
            ("explicitUndefined", string, text_declaration),
            ("supplied", string, text_declaration),
            ("omittedSlash", boolean, slash_declaration),
            ("undefinedSlash", boolean, slash_declaration),
            ("suppliedSlash", boolean, slash_declaration),
        ] {
            let call = variable_initializer(&parsed, file, name);
            assert_eq!(resolved_type(&context, call), expected);
            assert_eq!(context.get_type_at_location(call), Ok(expected));
            assert_eq!(
                context
                    .store()
                    .signature_links(call)
                    .and_then(|links| links.resolved_signature.signature()),
                context
                    .store()
                    .signature_links(declaration)
                    .and_then(|links| links.resolved_signature.signature()),
            );
            queries.push((call, expected));
        }
        if let Some((node, expected)) = cold {
            assert_eq!(context.get_type_at_location(node), Ok(expected));
            queries.push((node, expected));
        }
        assert_inferred_default_replay(&parsed, file, &mut context, &queries);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the exact argument errors and replay checks together.
fn inferred_string_defaults_reject_number_and_null_arguments() {
    let source = concat!(
        "function text(input = \"\") { const body: number = input; return input; }\n",
        "const count: number = 1;\n",
        "const wrongNumber: string = text(count);\n",
        "const wrongNull: string = text(null);\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_941);
    let (parameter, _) = initialized_parameter(source, &parsed, file, "\"\"");
    let reads = inferred_parameter_reads(&parsed, file, parameter);
    assert_eq!(reads.len(), 2);
    let first_call = variable_initializer(&parsed, file, "wrongNumber");
    for first_query in [None, Some(reads[0]), Some(first_call)] {
        let mut context = inferred_string_context(&parsed, file);
        let cold = first_query.map(|node| (node, context.get_type_at_location(node).unwrap()));
        context.check_source_file(file).unwrap();
        assert_inferred_string_parameter(source, &parsed, file, &mut context, "\"\"", 0, 1);
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let mut actual = context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| {
                let node = diagnostic.node.unwrap();
                let range = diagnostic.range_override.map_or_else(
                    || parsed.arena.get(node.node).unwrap().range,
                    |range| range.range(),
                );
                assert!(diagnostic.related_information.is_empty());
                (
                    diagnostic.diagnostic.code(),
                    usize::try_from(range.start.get()).unwrap(),
                    usize::try_from(range.end.get()).unwrap(),
                    diagnostic
                        .diagnostic
                        .arguments
                        .iter()
                        .map(String::as_str)
                        .collect::<Vec<_>>(),
                    diagnostic.diagnostic.render().unwrap(),
                )
            })
            .collect::<Vec<_>>();
        actual.sort_by_key(|diagnostic| diagnostic.1);
        let body = source.find("body:").unwrap();
        let count = source.rfind("count)").unwrap();
        let null = source.find("null)").unwrap();
        assert_eq!(
            actual,
            [
                (
                    2322, body, body + 4, vec!["string", "number"],
                    "Type 'string' is not assignable to type 'number'.".to_owned(),
                ),
                (
                    2345, count, count + 5, vec!["number", "string | undefined"],
                    "Argument of type 'number' is not assignable to parameter of type 'string | undefined'.".to_owned(),
                ),
                (
                    2345, null, null + 4, vec!["null", "string | undefined"],
                    "Argument of type 'null' is not assignable to parameter of type 'string | undefined'.".to_owned(),
                ),
            ],
        );
        let mut queries = reads.iter().map(|read| (*read, string)).collect::<Vec<_>>();
        for name in ["wrongNumber", "wrongNull"] {
            let call = variable_initializer(&parsed, file, name);
            assert_eq!(resolved_type(&context, call), string);
            assert_eq!(context.get_type_at_location(call), Ok(string));
            queries.push((call, string));
        }
        if let Some((node, expected)) = cold {
            assert_eq!(expected, string);
            queries.push((node, expected));
        }
        assert_inferred_default_replay(&parsed, file, &mut context, &queries);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Arity, the related note, and replay share one declaration.
fn inferred_default_before_required_parameter_keeps_minimum_arity() {
    let source = concat!(
        "function join(prefix = \"/\", name: string): string { return prefix + name; }\n",
        "const supplied: string = join(\"root/\", \"name\");\n",
        "const placeholder: string = join(undefined, \"name\");\n",
        "const tooShort: string = join(\"name\");\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2_942);
    let (parameter, _) = initialized_parameter(source, &parsed, file, "\"/\"");
    let reads = inferred_parameter_reads(&parsed, file, parameter);
    assert_eq!(reads.len(), 1);
    let first_call = variable_initializer(&parsed, file, "supplied");
    for first_query in [None, Some(reads[0]), Some(first_call)] {
        let mut context = inferred_string_context(&parsed, file);
        let cold = first_query.map(|node| (node, context.get_type_at_location(node).unwrap()));
        context.check_source_file(file).unwrap();
        let declaration =
            assert_inferred_string_parameter(source, &parsed, file, &mut context, "\"/\"", 2, 2);
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        let NodeData::FunctionDeclaration(function) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            panic!("expected a function declaration")
        };
        let required = NodeRef::new(parsed.arena.id(), file, function.parameters.nodes[1]);
        let required_symbol = context.file(file).unwrap().1.symbol(required).unwrap();
        assert_eq!(
            context
                .store()
                .value_symbol_links(required_symbol)
                .and_then(|links| links.resolved_type),
            Some(string),
        );
        let required_reads = inferred_parameter_reads(&parsed, file, required);
        assert_eq!(required_reads.len(), 1);
        assert_eq!(resolved_type(&context, required_reads[0]), string);
        assert_eq!(context.get_type_at_location(required_reads[0]), Ok(string));
        assert_eq!(
            context.get_symbol_at_location(required_reads[0]),
            Ok(Some(required_symbol)),
        );
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!(
                "expected only the missing-argument error: {:?}",
                context.diagnostics()
            )
        };
        assert_eq!(diagnostic.diagnostic.code(), 2554);
        assert_eq!(diagnostic.diagnostic.arguments, ["2", "1"]);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Expected 2 arguments, but got 1."
        );
        let node = diagnostic.node.unwrap();
        let range = diagnostic.range_override.map_or_else(
            || parsed.arena.get(node.node).unwrap().range,
            |range| range.range(),
        );
        let start = source.rfind("join(").unwrap();
        assert_eq!(usize::try_from(range.start.get()).unwrap(), start);
        assert_eq!(usize::try_from(range.end.get()).unwrap(), start + 4);
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("expected the native missing-parameter note")
        };
        assert_eq!(related.diagnostic.code(), 6210);
        assert_eq!(related.diagnostic.arguments, ["name"]);
        assert_eq!(
            related.diagnostic.render().unwrap(),
            "An argument for 'name' was not provided."
        );
        assert_eq!(related.node, Some(required));
        assert_eq!(node_text(source, &parsed, required), "name: string");
        let required_range = parsed.arena.get(required.node).unwrap().range;
        let required_start = source.find("name: string").unwrap();
        assert_eq!(
            usize::try_from(required_range.start.get()).unwrap(),
            required_start,
        );
        assert_eq!(
            usize::try_from(required_range.end.get()).unwrap(),
            required_start + "name: string".len(),
        );
        let mut queries = vec![(reads[0], string), (required_reads[0], string)];
        for name in ["supplied", "placeholder", "tooShort"] {
            let call = variable_initializer(&parsed, file, name);
            assert_eq!(resolved_type(&context, call), string);
            assert_eq!(context.get_type_at_location(call), Ok(string));
            queries.push((call, string));
        }
        if let Some((node, expected)) = cold {
            assert_eq!(expected, string);
            queries.push((node, expected));
        }
        assert_inferred_default_replay(&parsed, file, &mut context, &queries);
    }
}
