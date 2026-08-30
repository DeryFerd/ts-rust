use ts_ast::{FileId, FlowFlags, FlowNodePayload, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
    type_records::LiteralValue,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_780);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/computed-arrow-bindings.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(FILE, &parsed.arena)].into_iter().collect(),
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

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn value_declaration(parsed: &ParseResult, expected: &str) -> NodeRef {
    let mut declarations = parsed.arena.iter().filter_map(|(id, record)| {
        let name = match &record.data {
            NodeData::VariableDeclaration(variable) => variable.name,
            NodeData::FunctionDeclaration(function) => function.name?,
            _ => return None,
        };
        let NodeData::Identifier(name) = &parsed.arena.get(name)?.data else {
            return None;
        };
        (name.text == expected).then_some(node(parsed, id))
    });
    let result = declarations
        .next()
        .unwrap_or_else(|| panic!("missing declaration {expected}"));
    assert!(declarations.next().is_none(), "duplicate {expected}");
    result
}

fn initializer(parsed: &ParseResult, name: &str) -> NodeRef {
    let declaration = value_declaration(parsed, name);
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected variable {name}")
    };
    node(parsed, variable.initializer.unwrap())
}

struct ArrowParts {
    arrow: NodeRef,
    variable: NodeRef,
    variable_name: NodeRef,
    parameter: NodeRef,
    contextual_parameter: NodeRef,
    contextual_return: NodeRef,
    element: NodeRef,
    name: NodeRef,
    key: NodeRef,
    key_read: NodeRef,
    body: NodeRef,
}

fn arrow_parts(parsed: &ParseResult) -> ArrowParts {
    let arrow = initializer(parsed, "read");
    let record = parsed.arena.get(arrow.node).unwrap();
    let NodeData::ArrowFunction(data) = &record.data else {
        panic!("read must retain its actual source arrow")
    };
    let variable = node(parsed, record.parent.unwrap());
    let NodeData::VariableDeclaration(variable_data) =
        &parsed.arena.get(variable.node).unwrap().data
    else {
        panic!("the arrow must keep its contextual variable")
    };
    let NodeData::FunctionTypeNode(target) =
        &parsed.arena.get(variable_data.type_.unwrap()).unwrap().data
    else {
        panic!("the variable must supply its contextual function type")
    };
    let [parameter] = data.parameters.nodes.as_slice() else {
        panic!("expected one real object parameter")
    };
    let [contextual_parameter] = target.parameters.nodes.as_slice() else {
        panic!("expected one contextual parameter")
    };
    let NodeData::ParameterDeclaration(contextual_parameter) =
        &parsed.arena.get(*contextual_parameter).unwrap().data
    else {
        unreachable!()
    };
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(*parameter).unwrap().data
    else {
        unreachable!()
    };
    assert!(parameter_data.type_.is_none());
    let pattern = parsed.arena.get(parameter_data.name).unwrap();
    assert_eq!(pattern.kind, SyntaxKind::ObjectBindingPattern);
    let NodeData::BindingPattern(pattern) = &pattern.data else {
        unreachable!()
    };
    let [element] = pattern.elements.nodes.as_slice() else {
        panic!("expected one computed binding")
    };
    let NodeData::BindingElement(binding) = &parsed.arena.get(*element).unwrap().data else {
        unreachable!()
    };
    let NodeData::ComputedPropertyName(property) = &parsed
        .arena
        .get(binding.property_name.unwrap())
        .unwrap()
        .data
    else {
        panic!("the original computed key must remain in the parameter")
    };
    let key = node(parsed, property.expression);
    let key_read = match &parsed.arena.get(key.node).unwrap().data {
        NodeData::Identifier(_) => key,
        NodeData::CallExpression(call) => {
            assert!(call.arguments.nodes.is_empty());
            node(parsed, call.expression)
        }
        _ => panic!("expected a captured identifier or zero-argument key call"),
    };
    ArrowParts {
        arrow,
        variable,
        variable_name: node(parsed, variable_data.name),
        parameter: node(parsed, *parameter),
        contextual_parameter: node(parsed, contextual_parameter.type_.unwrap()),
        contextual_return: node(parsed, target.type_.unwrap()),
        element: node(parsed, *element),
        name: node(parsed, binding.name.unwrap()),
        key,
        key_read,
        body: node(parsed, data.body),
    }
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn is_checked(context: &CanonicalCheckerContext<'_>) -> bool {
    context
        .store()
        .source_file_links(context.source_file(FILE).unwrap())
        .is_some_and(|links| links.type_checked)
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = context.store();
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

fn node_text<'source>(
    source: &'source str,
    parsed: &ParseResult,
    location: NodeRef,
) -> &'source str {
    let range = parsed.arena.get(location.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn assert_key_flow(context: &CanonicalCheckerContext<'_>, parts: &ArrowParts) {
    let (_, bound) = context.file(FILE).unwrap();
    let graph = bound.flow_graph();
    let start = graph.container_start(parts.arrow).unwrap();
    let start_record = graph.nodes().get(start).unwrap();
    assert!(start_record.flags.contains(FlowFlags::START));
    assert_eq!(
        start_record.payload,
        Some(FlowNodePayload::Ast(parts.arrow))
    );
    assert_eq!(start_record.antecedent, None);
    assert_eq!(bound.container(parts.key_read), Some(parts.arrow));
    assert_eq!(bound.flow_container(parts.key_read), Some(parts.arrow));
    assert_eq!(bound.flow_at(parts.key_read), Some(start));
    assert_eq!(bound.flow_container(parts.body), Some(parts.arrow));
    assert_ne!(bound.flow_container(parts.arrow), Some(parts.arrow));
    assert_ne!(bound.flow_at(parts.arrow), Some(start));
}

fn assert_binding(
    context: &mut CanonicalCheckerContext<'_>,
    parts: &ArrowParts,
    expected: TypeId,
) -> SemanticSymbolId {
    let parent = symbol(context, parts.parameter);
    let leaf = symbol(context, parts.element);
    assert_ne!(parent, leaf);
    let record = context.store().symbol(leaf).unwrap();
    assert_eq!(record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
    assert_eq!(record.declarations(), Some(&[parts.element][..]));
    assert_eq!(record.value_declaration(), Some(parts.element));
    for location in [parts.element, parts.name] {
        assert_eq!(context.get_type_at_location(location).unwrap(), expected);
        assert_eq!(
            context.get_symbol_at_location(location).unwrap(),
            Some(leaf)
        );
    }
    assert_eq!(
        context.get_symbol_declarations(leaf).unwrap(),
        &[parts.element]
    );
    leaf
}

fn assert_arrow(
    context: &mut CanonicalCheckerContext<'_>,
    parts: &ArrowParts,
    returned: TypeId,
) -> (TypeId, TypeId, TypeId) {
    let owner = symbol(context, parts.arrow);
    let variable = symbol(context, parts.variable);
    let parent = symbol(context, parts.parameter);
    assert_ne!(owner, variable);
    assert_ne!(owner, parent);
    let callable = context.get_type_at_location(parts.arrow).unwrap();
    let target = context.get_type_at_location(parts.variable_name).unwrap();
    let parent_type = context.get_type_at_location(parts.parameter).unwrap();
    assert_ne!(callable, target);
    assert_eq!(
        context.store().type_payload(callable).unwrap().symbol(),
        Some(owner)
    );
    assert_eq!(
        context
            .get_type_at_location(parts.contextual_parameter)
            .unwrap(),
        parent_type
    );
    assert_eq!(
        context.get_symbol_at_location(parts.parameter).unwrap(),
        Some(parent)
    );
    assert_eq!(
        context.get_symbol_declarations(parent).unwrap(),
        &[parts.parameter]
    );
    let signature = context
        .store()
        .signature_links(parts.arrow)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(parts.arrow));
    assert_eq!(record.parameters(), &[parent]);
    assert_eq!(record.min_argument_count(), 1);
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.resolved_return_type(), Some(returned));
    (callable, target, parent_type)
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parts: &ArrowParts,
    types: &[(NodeRef, TypeId)],
    symbols: &[(NodeRef, SemanticSymbolId)],
) {
    let before = counts(context);
    let diagnostics = context.diagnostics().clone();
    let signatures = [parts.arrow, parts.key]
        .map(|location| (location, context.store().signature_links(location).cloned()));
    for _ in 0..2 {
        context.check_source_file(FILE).unwrap();
        context.recheck_source_file(FILE).unwrap();
        for &(location, expected) in types {
            assert_eq!(context.get_type_at_location(location).unwrap(), expected);
        }
        for &(location, expected) in symbols {
            assert_eq!(
                context.get_symbol_at_location(location).unwrap(),
                Some(expected)
            );
        }
        for (location, expected) in &signatures {
            assert_eq!(
                context.store().signature_links(*location),
                expected.as_ref()
            );
        }
        assert_eq!(context.diagnostics(), &diagnostics);
        assert_eq!(counts(context), before);
        assert!(is_checked(context));
        assert_key_flow(context, parts);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep each source key, bound parameter, call, and replay together.
fn captured_computed_arrow_keys_keep_source_symbols_and_replay() {
    for (prefix, key, member, expected_key) in [
        ("const key = 'value';", "key", "value", "\"value\""),
        ("const key = 1;", "key", "1", "1"),
        (
            "function key(): 'value' { return 'value'; }",
            "key()",
            "value",
            "\"value\"",
        ),
    ] {
        let source = format!(
            "{prefix}\nconst read: (input: {{ {member}: number }}) => number = \
             ({{ [{key}]: chosen }}) => chosen;\nconst result = read({{ {member}: 1 }});",
        );
        for query_first in [false, true] {
            let parsed = parse_source_file(&source);
            let mut context = context(&parsed);
            let parts = arrow_parts(&parsed);
            let key_declaration = value_declaration(&parsed, "key");
            let key_symbol = symbol(&context, key_declaration);
            let parent = symbol(&context, parts.parameter);
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            assert!(!is_checked(&context));
            assert_key_flow(&context, &parts);
            if query_first {
                assert_eq!(context.get_type_at_location(parts.name).unwrap(), number);
            } else {
                context.check_source_file(FILE).unwrap();
            }
            assert!(is_checked(&context));
            let leaf = assert_binding(&mut context, &parts, number);
            let (callable, target, parent_type) = assert_arrow(&mut context, &parts, number);
            assert_ne!(key_symbol, parent);
            assert_ne!(key_symbol, leaf);
            assert_eq!(
                context.get_symbol_at_location(parts.key_read).unwrap(),
                Some(key_symbol)
            );
            assert_eq!(
                context.get_symbol_declarations(key_symbol).unwrap(),
                &[key_declaration]
            );
            assert_eq!(
                context.get_symbol_at_location(parts.body).unwrap(),
                Some(leaf)
            );
            let key_type = context.get_type_at_location(parts.key).unwrap();
            assert_eq!(context.type_to_string(key_type).unwrap(), expected_key);
            assert_eq!(node_text(&source, &parsed, parts.key), key);
            assert_eq!(
                context.type_to_string(callable).unwrap(),
                format!("({{ [{key}]: chosen }}: {{ {member}: number; }}) => number"),
            );
            let call = initializer(&parsed, "result");
            assert_eq!(context.get_type_at_location(parts.body).unwrap(), number);
            assert_eq!(context.get_type_at_location(call).unwrap(), number);
            assert_eq!(
                context
                    .get_type_at_location(parts.contextual_return)
                    .unwrap(),
                number
            );
            if key == "key()" {
                let selected = context
                    .store()
                    .signature_links(parts.key)
                    .and_then(|links| links.resolved_signature.signature())
                    .unwrap();
                let record = context.store().signature(selected).unwrap();
                assert_eq!(record.declaration(), Some(key_declaration));
                assert!(record.parameters().is_empty());
                assert_eq!(record.resolved_return_type(), Some(key_type));
            }
            assert!(context.diagnostics().is_empty());
            assert_replay(
                &mut context,
                &parts,
                &[
                    (parts.arrow, callable),
                    (parts.variable_name, target),
                    (parts.parameter, parent_type),
                    (parts.contextual_parameter, parent_type),
                    (parts.contextual_return, number),
                    (parts.element, number),
                    (parts.name, number),
                    (parts.key, key_type),
                    (parts.body, number),
                    (call, number),
                ],
                &[
                    (parts.parameter, parent),
                    (parts.element, leaf),
                    (parts.name, leaf),
                    (parts.key_read, key_symbol),
                    (parts.body, leaf),
                ],
            );
        }
    }
}

#[test]
fn computed_arrow_key_errors_keep_the_key_location_and_leaf_identity() {
    for (prefix, key_display, code, message) in [
        (
            "let key = 'value';",
            "string",
            2537,
            "Type '{ value: number; }' has no matching index signature for type 'string'.",
        ),
        (
            "const key = 'missing';",
            "\"missing\"",
            2339,
            "Property 'missing' does not exist on type '{ value: number; }'.",
        ),
    ] {
        let source = format!(
            "{prefix}\nconst read: (input: {{ value: number }}) => number = \
             ({{ [key]: chosen }}) => chosen;",
        );
        let parsed = parse_source_file(&source);
        let mut context = context(&parsed);
        let parts = arrow_parts(&parsed);
        context.check_source_file(FILE).unwrap();
        let error = context.store().intrinsic_bootstrap().unwrap().error_type;
        let leaf = assert_binding(&mut context, &parts, error);
        let key_type = context.get_type_at_location(parts.key).unwrap();
        let key_symbol = symbol(&context, value_declaration(&parsed, "key"));
        assert_eq!(context.type_to_string(key_type).unwrap(), key_display);
        assert_eq!(context.get_type_at_location(parts.body).unwrap(), error);
        assert_eq!(
            context.get_symbol_at_location(parts.body).unwrap(),
            Some(leaf)
        );
        assert_ne!(key_symbol, leaf);
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected only the computed binding key diagnostic: {source}")
        };
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.node, Some(parts.key));
        assert_eq!(node_text(&source, &parsed, parts.key), "key");
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        assert_replay(
            &mut context,
            &parts,
            &[
                (parts.element, error),
                (parts.name, error),
                (parts.body, error),
                (parts.key, key_type),
            ],
            &[
                (parts.element, leaf),
                (parts.name, leaf),
                (parts.body, leaf),
                (parts.key_read, key_symbol),
            ],
        );
    }
}

#[test]
fn computed_arrow_return_error_keeps_the_inferred_source_signature() {
    let source = concat!(
        "const key = 'value';\n",
        "const read: (input: { value: string }) => number = ",
        "({ [key]: chosen }) => chosen;",
    );
    let parsed = parse_source_file(source);
    let mut context = context(&parsed);
    let parts = arrow_parts(&parsed);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let string = bootstrap.string_type;
    assert!(!is_checked(&context));
    assert_eq!(context.get_type_at_location(parts.name).unwrap(), string);
    let leaf = assert_binding(&mut context, &parts, string);
    let (callable, target, parent_type) = assert_arrow(&mut context, &parts, string);
    assert_eq!(
        context
            .get_type_at_location(parts.contextual_return)
            .unwrap(),
        number
    );
    assert_eq!(context.get_type_at_location(parts.body).unwrap(), string);
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the inferred string return must fail the contextual number return")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.node, Some(parts.arrow));
    assert_eq!(
        node_text(source, &parsed, parts.arrow),
        "({ [key]: chosen }) => chosen"
    );
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type '({ [key]: chosen }: { value: string; }) => string' is not assignable to type '(input: { value: string; }) => number'.",
    );
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    assert_replay(
        &mut context,
        &parts,
        &[
            (parts.arrow, callable),
            (parts.variable_name, target),
            (parts.parameter, parent_type),
            (parts.contextual_return, number),
            (parts.element, string),
            (parts.name, string),
            (parts.body, string),
        ],
        &[
            (parts.element, leaf),
            (parts.name, leaf),
            (parts.body, leaf),
        ],
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Compare the deferred body with reads before and after the outer write.
fn computed_arrow_body_uses_deferred_capture_flow_without_changing_outer_flow() {
    let source = concat!(
        "const key = 'value';\n",
        "let captured: number | false = 1;\n",
        "const before = captured;\n",
        "const read: (input: { value: number }) => number | false = ",
        "({ [key]: chosen }) => captured;\n",
        "const during = captured;\n",
        "captured = false;\n",
        "const after = captured;\n",
        "const result = read({ value: 2 });\n",
    );
    let parsed = parse_source_file(source);
    let mut context = context(&parsed);
    let parts = arrow_parts(&parsed);
    let captured_declaration = value_declaration(&parsed, "captured");
    let captured = symbol(&context, captured_declaration);
    let key = symbol(&context, value_declaration(&parsed, "key"));
    assert_ne!(key, captured);
    assert_key_flow(&context, &parts);
    context.check_source_file(FILE).unwrap();
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let declared = context
        .store()
        .value_symbol_links(captured)
        .and_then(|links| links.resolved_type)
        .unwrap();
    assert!(matches!(
        context.store().type_payload(declared).unwrap().data(),
        TypeData::Union(_)
    ));
    let leaf = assert_binding(&mut context, &parts, number);
    assert_ne!(leaf, captured);
    assert_eq!(
        context.get_symbol_at_location(parts.body).unwrap(),
        Some(captured)
    );
    assert_eq!(context.get_type_at_location(parts.body).unwrap(), declared);
    assert_eq!(
        context
            .get_type_at_location(parts.contextual_return)
            .unwrap(),
        declared
    );
    let (callable, target, parent_type) = assert_arrow(&mut context, &parts, declared);
    let before = initializer(&parsed, "before");
    let during = initializer(&parsed, "during");
    let after = initializer(&parsed, "after");
    let call = initializer(&parsed, "result");
    assert_eq!(context.get_type_at_location(before).unwrap(), number);
    assert_eq!(context.get_type_at_location(during).unwrap(), number);
    assert_eq!(context.get_type_at_location(call).unwrap(), declared);
    let after_type = context.get_type_at_location(after).unwrap();
    let TypeData::Literal(literal) = context.store().type_payload(after_type).unwrap().data()
    else {
        panic!("the outer assignment must leave the later read at false")
    };
    assert_eq!(literal.value, LiteralValue::Boolean(false));
    assert_ne!(after_type, declared);
    assert_ne!(after_type, number);
    let (_, bound) = context.file(FILE).unwrap();
    for outside in [before, during, after] {
        assert_eq!(
            bound.flow_container(outside),
            Some(node(&parsed, parsed.source_file))
        );
        assert_ne!(
            bound.flow_container(outside),
            bound.flow_container(parts.key_read)
        );
    }
    assert!(context.diagnostics().is_empty());
    assert_replay(
        &mut context,
        &parts,
        &[
            (parts.arrow, callable),
            (parts.variable_name, target),
            (parts.parameter, parent_type),
            (parts.contextual_return, declared),
            (parts.element, number),
            (parts.name, number),
            (parts.body, declared),
            (before, number),
            (during, number),
            (after, after_type),
            (call, declared),
        ],
        &[
            (parts.element, leaf),
            (parts.name, leaf),
            (parts.key_read, key),
            (parts.body, captured),
            (before, captured),
            (during, captured),
            (after, captured),
        ],
    );
}
