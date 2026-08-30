use ts_ast::{FileId, NodeData, NodeFlags, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SignatureId, TypeData, TypeId,
    jsdoc::{JsDocCommentError, plan_javascript_source_jsdoc},
};
use ts_parser::{ParseResult, parse_javascript_source_file};

const FILE: FileId = FileId::new(8_220);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic-overloads.js\""),
                CanonicalSourceLanguage::JavaScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_javascript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    // jsDocGenericOverloads uses checkJs and noEmit, with no strict-option overrides.
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            no_emit: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind).then_some((
                record.range.start,
                NodeRef::new(parsed.arena.id(), FILE, node),
            ))
        })
        .collect::<Vec<_>>();
    nodes.sort_by_key(|(start, _)| *start);
    nodes.into_iter().map(|(_, node)| node).collect()
}

fn signatures(context: &CanonicalCheckerContext<'_>, callable: TypeId) -> Vec<SignatureId> {
    let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data() else {
        panic!("expected a canonical callable object")
    };
    let signatures = object.structured.signatures.as_ref().unwrap();
    assert_eq!(object.structured.call_signature_count, signatures.len());
    signatures.clone()
}

fn selected_signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the source node must retain its resolved signature")
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize) {
    (
        context.store().type_len(),
        context.store().symbol_len(),
        context.store().signature_len(),
        context.store().mapper_len(),
    )
}

#[derive(Debug, Eq, PartialEq)]
struct NamedSignatureSnapshot {
    owner: SemanticSymbolId,
    callable: TypeId,
    signature: SignatureId,
    template_symbol: SemanticSymbolId,
    template_type: TypeId,
    parameter_types: Vec<TypeId>,
    query_types: Vec<(NodeRef, TypeId)>,
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let symbol = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(symbol).unwrap()
}

fn assert_reparsed_named_source(parsed: &ParseResult) {
    let source_node = NodeRef::new(parsed.arena.id(), FILE, parsed.source_file);
    let plan = plan_javascript_source_jsdoc(&parsed.arena, source_node).unwrap();
    assert!(plan.diagnostics().is_empty());
    for declaration in nodes(parsed, SyntaxKind::FunctionDeclaration) {
        let NodeData::FunctionDeclaration(function) =
            &parsed.arena.get(declaration.node).unwrap().data
        else {
            unreachable!()
        };
        let documented = plan.declaration(declaration).unwrap();
        let [template] = function.type_parameters.as_ref().unwrap().nodes.as_slice() else {
            panic!("expected one reparsed template")
        };
        let template = parsed.arena.get(*template).unwrap();
        assert_eq!(template.flags, NodeFlags::REPARSED);
        assert_eq!(template.parent, Some(declaration.node));
        assert_eq!(template.range, documented.template_parameters()[0].range());
        for (&parameter, documented) in function
            .parameters
            .nodes
            .iter()
            .zip(documented.parameters())
        {
            let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter).unwrap().data
            else {
                panic!("expected a documented source parameter")
            };
            let annotation = parsed.arena.get(data.type_.unwrap()).unwrap();
            assert_eq!(annotation.flags, NodeFlags::REPARSED);
            assert_eq!(annotation.parent, Some(parameter));
            assert_eq!(annotation.range, documented.type_().unwrap().range());
        }
        let returned = parsed.arena.get(function.type_.unwrap()).unwrap();
        assert_eq!(returned.flags, NodeFlags::REPARSED);
        assert_eq!(returned.parent, Some(declaration.node));
        assert_eq!(returned.range, documented.return_type().unwrap().range());
    }
    let mut pending = vec![parsed.source_file];
    let mut reached = std::collections::HashSet::new();
    while let Some(node) = pending.pop() {
        assert!(reached.insert(node), "the source must remain a tree");
        parsed.arena.get(node).unwrap().for_each_child(|child| {
            assert_eq!(parsed.arena.get(child).unwrap().parent, Some(node));
            pending.push(child);
        });
    }
    assert_eq!(
        reached.len(),
        parsed.arena.len(),
        "no reparsed node may be detached"
    );
}

#[allow(clippy::too_many_lines)] // Check one source signature and its binder-owned types together.
fn named_signature_snapshot(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    declaration: NodeRef,
) -> NamedSignatureSnapshot {
    let NodeData::FunctionDeclaration(function) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected a named JavaScript function")
    };
    let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    let name = node_ref(function.name.unwrap());
    let owner = symbol(context, declaration);
    let callable = context.get_type_at_location(name).unwrap();
    assert_eq!(context.get_type_at_location(declaration).unwrap(), callable);
    assert_eq!(context.get_symbol_at_location(name).unwrap(), Some(owner));
    assert_eq!(
        context.get_symbol_declarations(owner).unwrap(),
        [declaration]
    );
    assert_eq!(
        context.store().type_payload(callable).unwrap().symbol(),
        Some(owner)
    );
    let signature = selected_signature(context, declaration);
    assert_eq!(signatures(context, callable), [signature]);
    let [template_node] = function.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("expected one source-owned JSDoc template")
    };
    let NodeData::TypeParameterDeclaration(template) =
        &parsed.arena.get(*template_node).unwrap().data
    else {
        panic!("expected the JSDoc template's declaration")
    };
    let template_symbol = symbol(context, node_ref(*template_node));
    let template_type = context
        .get_type_at_location(node_ref(template.name))
        .unwrap();
    assert_eq!(
        context
            .get_symbol_at_location(node_ref(template.name))
            .unwrap(),
        Some(template_symbol),
    );
    assert_eq!(
        context.get_symbol_declarations(template_symbol).unwrap(),
        [node_ref(*template_node)],
    );
    assert_eq!(
        context
            .store()
            .declared_type_links(template_symbol)
            .unwrap()
            .declared_type,
        Some(template_type),
    );
    let template_record = context.store().type_payload(template_type).unwrap();
    assert_eq!(template_record.symbol(), Some(template_symbol));
    let TypeData::TypeParameter(template_data) = template_record.data() else {
        panic!("JSDoc must publish a real type parameter")
    };
    assert_eq!(template_data.target, None);
    assert_eq!(template_data.mapper, None);
    let no_constraint = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .no_constraint_type;
    assert!(
        template_data
            .constraint
            .is_none_or(|constraint| constraint == no_constraint)
    );

    let mut query_types = vec![(name, callable), (node_ref(template.name), template_type)];
    let mut parameter_symbols = Vec::new();
    let mut parameter_types = Vec::new();
    for &parameter_node in &function.parameters.nodes {
        let NodeData::ParameterDeclaration(parameter) =
            &parsed.arena.get(parameter_node).unwrap().data
        else {
            panic!("expected a value parameter")
        };
        let parameter_symbol = symbol(context, node_ref(parameter_node));
        let annotation = node_ref(parameter.type_.unwrap());
        let parameter_type = context.get_type_from_type_node(annotation).unwrap();
        assert_eq!(
            context.get_type_at_location(annotation).unwrap(),
            parameter_type
        );
        assert_eq!(
            context
                .get_type_at_location(node_ref(parameter.name))
                .unwrap(),
            parameter_type
        );
        assert_eq!(
            context
                .get_symbol_at_location(node_ref(parameter.name))
                .unwrap(),
            Some(parameter_symbol),
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(parameter_symbol)
                .unwrap()
                .resolved_type,
            Some(parameter_type),
        );
        parameter_symbols.push(parameter_symbol);
        parameter_types.push(parameter_type);
        query_types.extend([
            (annotation, parameter_type),
            (node_ref(parameter.name), parameter_type),
        ]);
    }
    let returned = context.get_return_type_of_signature(signature).unwrap();
    let return_annotation = node_ref(function.type_.unwrap());
    assert_eq!(
        context.get_type_from_type_node(return_annotation).unwrap(),
        returned
    );
    query_types.push((return_annotation, returned));
    let signature_record = context.store().signature(signature).unwrap();
    assert_eq!(signature_record.declaration(), Some(declaration));
    assert_eq!(signature_record.type_parameters(), [template_type]);
    assert_eq!(signature_record.parameters(), parameter_symbols);
    assert_eq!(signature_record.target(), None);
    assert_eq!(signature_record.mapper(), None);
    let NodeData::Block(block) = &parsed.arena.get(function.body.unwrap()).unwrap().data else {
        panic!("expected the implementation body")
    };
    let [statement] = block.statements.nodes.as_slice() else {
        panic!("expected one checked return")
    };
    let NodeData::ReturnStatement(statement) = &parsed.arena.get(*statement).unwrap().data else {
        panic!("expected the implementation return")
    };
    let body = node_ref(statement.expression.unwrap());
    let body_type = context.get_type_at_location(body).unwrap();
    assert_eq!(body_type, parameter_types[0]);
    assert_eq!(
        context.get_symbol_at_location(body).unwrap(),
        Some(parameter_symbols[0])
    );
    query_types.push((body, body_type));

    NamedSignatureSnapshot {
        owner,
        callable,
        signature,
        template_symbol,
        template_type,
        parameter_types,
        query_types,
    }
}

#[test]
fn named_jsdoc_generics_keep_distinct_template_owners_and_inferred_calls_on_replay() {
    let parsed = parse_javascript_source_file(concat!(
        "/** @template T @param {T} value @param {number} count @returns {T} */\n",
        "function keep(value, count) { return value; }\n",
        "/** @template T @param {T} value @returns {T} */\n",
        "function echo(value) { return value; }\n",
        "keep('kept', 1);\n",
        "echo(2);\n",
        "keep(true, 3);\n",
    ));
    let declarations = nodes(&parsed, SyntaxKind::FunctionDeclaration);
    assert_eq!(declarations.len(), 2);
    assert_reparsed_named_source(&parsed);
    let annotations = nodes(&parsed, SyntaxKind::TypeReference);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 3);
    for query_first in [false, true] {
        let mut context = context(&parsed);
        let early = query_first.then(|| context.get_type_from_type_node(annotations[0]).unwrap());
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let states = declarations
            .iter()
            .map(|&declaration| named_signature_snapshot(&mut context, &parsed, declaration))
            .collect::<Vec<_>>();
        assert_ne!(states[0].owner, states[1].owner);
        assert_ne!(states[0].template_symbol, states[1].template_symbol);
        assert_ne!(states[0].template_type, states[1].template_type);
        assert_ne!(states[0].signature, states[1].signature);
        if let Some(early) = early {
            assert_eq!(early, states[0].template_type);
        }
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        assert_eq!(states[0].parameter_types, [states[0].template_type, number]);
        assert_eq!(states[1].parameter_types, [states[1].template_type]);
        for state in &states {
            assert_eq!(
                context
                    .get_return_type_of_signature(state.signature)
                    .unwrap(),
                state.template_type
            );
        }
        let call_results = calls
            .iter()
            .zip([(0, "\"kept\""), (1, "2"), (0, "true")])
            .map(|(&call, (owner, display))| {
                let result = context.get_type_at_location(call).unwrap();
                assert_eq!(context.type_to_string(result).unwrap(), display);
                let selected = selected_signature(&context, call);
                let selected_record = context.store().signature(selected).unwrap();
                assert_eq!(selected_record.target(), Some(states[owner].signature));
                assert!(selected_record.mapper().is_some());
                assert!(selected_record.type_parameters().is_empty());
                assert_eq!(selected_record.resolved_return_type(), Some(result));
                (call, result, selected)
            })
            .collect::<Vec<_>>();
        let before = counts(&context);
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            for (&declaration, state) in declarations.iter().zip(&states) {
                assert_eq!(
                    named_signature_snapshot(&mut context, &parsed, declaration),
                    *state
                );
                for &(node, expected) in &state.query_types {
                    assert_eq!(context.get_type_at_location(node).unwrap(), expected);
                }
            }
            for &(call, result, selected) in &call_results {
                assert_eq!(context.get_type_at_location(call).unwrap(), result);
                assert_eq!(selected_signature(&context, call), selected);
            }
            assert_eq!(counts(&context), before);
            assert!(context.diagnostics().is_empty());
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep both return-error directions and query orders together.
fn named_jsdoc_generic_returns_keep_exact_diagnostics_on_query_replay() {
    let parsed = parse_javascript_source_file(concat!(
        "/** @template T @param {T} value @returns {number} */\n",
        "function numeric(value) { return value; }\n",
        "/** @template T @param {string} value @returns {T} */\n",
        "function arbitrary(value) { return value; }\n",
        "numeric('text');\n",
    ));
    let declarations = nodes(&parsed, SyntaxKind::FunctionDeclaration);
    assert_eq!(declarations.len(), 2);
    let return_annotations = declarations
        .iter()
        .map(|declaration| {
            let NodeData::FunctionDeclaration(function) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                unreachable!()
            };
            NodeRef::new(parsed.arena.id(), FILE, function.type_.unwrap())
        })
        .collect::<Vec<_>>();
    let returns = nodes(&parsed, SyntaxKind::ReturnStatement);
    assert_eq!(returns.len(), 2);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    let [call] = calls.as_slice() else {
        panic!("expected one generic call")
    };
    for query_first in [false, true] {
        let mut context = context(&parsed);
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        if query_first {
            assert_eq!(
                context
                    .get_type_from_type_node(return_annotations[0])
                    .unwrap(),
                number
            );
            context
                .get_type_from_type_node(return_annotations[1])
                .unwrap();
            assert!(context.diagnostics().is_empty());
        }
        context.check_source_file(FILE).unwrap();
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        for ((diagnostic, &returned), expected) in diagnostics.iter().zip(&returns).zip([
            "Type 'T' is not assignable to type 'number'.",
            concat!(
                "Type 'string' is not assignable to type 'T'.\n",
                "  'T' could be instantiated with an arbitrary type which ",
                "could be unrelated to 'string'.",
            ),
        ]) {
            assert_eq!(diagnostic.diagnostic.code(), 2322);
            assert_eq!(diagnostic.diagnostic.render().unwrap(), expected);
            assert_eq!(diagnostic.node, Some(returned));
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.related_information.is_empty());
        }
        let states = declarations
            .iter()
            .map(|&declaration| named_signature_snapshot(&mut context, &parsed, declaration))
            .collect::<Vec<_>>();
        assert_eq!(
            context
                .get_return_type_of_signature(states[0].signature)
                .unwrap(),
            number
        );
        assert_eq!(
            context
                .get_return_type_of_signature(states[1].signature)
                .unwrap(),
            states[1].template_type,
        );
        assert_eq!(context.get_type_at_location(*call).unwrap(), number);
        let selected = selected_signature(&context, *call);
        assert_eq!(
            context.store().signature(selected).unwrap().target(),
            Some(states[0].signature)
        );
        let diagnostics = context.diagnostics().clone();
        let before = counts(&context);
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            for (&declaration, state) in declarations.iter().zip(&states) {
                assert_eq!(
                    named_signature_snapshot(&mut context, &parsed, declaration),
                    *state
                );
            }
            assert_eq!(context.get_type_at_location(*call).unwrap(), number);
            assert_eq!(selected_signature(&context, *call), selected);
            assert_eq!(context.diagnostics(), &diagnostics);
            assert_eq!(counts(&context), before);
        }
    }
}

#[test]
fn named_jsdoc_templates_preserve_empty_function_checking_and_explicit_returns() {
    let parsed = parse_javascript_source_file(concat!(
        "/** @template T */\n",
        "function noop() {}\n",
        "/** @template T @returns {number} */\n",
        "function count() { return 1; }\n",
    ));
    let declarations = nodes(&parsed, SyntaxKind::FunctionDeclaration);
    let [noop, count] = declarations.as_slice() else {
        panic!("expected the two zero-parameter functions")
    };
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(context.diagnostics().is_empty());
    let noop_signature = selected_signature(&context, *noop);
    let count_signature = selected_signature(&context, *count);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let (void, number) = (bootstrap.void_type, bootstrap.number_type);
    // This checks the existing template-only source behavior, not its generic signature.
    assert_eq!(
        context
            .get_return_type_of_signature(noop_signature)
            .unwrap(),
        void
    );
    assert_eq!(
        context
            .get_return_type_of_signature(count_signature)
            .unwrap(),
        number
    );
    let signature = context.store().signature(count_signature).unwrap();
    assert!(signature.parameters().is_empty());
    let [template_type] = signature.type_parameters() else {
        panic!("the explicit-return function must have a real generic signature")
    };
    let template_type = *template_type;
    assert!(matches!(
        context.store().type_payload(template_type).unwrap().data(),
        TypeData::TypeParameter(_)
    ));
    let NodeData::FunctionDeclaration(function) = &parsed.arena.get(count.node).unwrap().data
    else {
        unreachable!()
    };
    let [template_node] = function.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("the generic signature must have a source-owned template")
    };
    assert_eq!(
        context
            .store()
            .type_payload(template_type)
            .unwrap()
            .symbol(),
        Some(symbol(
            &context,
            NodeRef::new(parsed.arena.id(), FILE, *template_node)
        )),
    );
    let before = counts(&context);
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(selected_signature(&context, *noop), noop_signature);
        assert_eq!(selected_signature(&context, *count), count_signature);
        assert_eq!(
            context
                .get_return_type_of_signature(noop_signature)
                .unwrap(),
            void
        );
        assert_eq!(
            context
                .get_return_type_of_signature(count_signature)
                .unwrap(),
            number
        );
        assert_eq!(
            context
                .store()
                .signature(count_signature)
                .unwrap()
                .type_parameters(),
            [template_type]
        );
        assert_eq!(counts(&context), before);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the binder, signature, call, and replay checks together.
fn generic_jsdoc_arrow_ignores_overloads_and_replays_canonical_queries() {
    let parsed = parse_javascript_source_file(concat!(
        "/**\n",
        " * @template T\n",
        " * @param {T} value\n",
        " * @returns {T}\n",
        " * @overload\n",
        " * @param {number} value\n",
        " * @returns {number}\n",
        " * @overload\n",
        " * @param {number} value\n",
        " * @param {number} count\n",
        " * @returns {number}\n",
        " */\n",
        "const keep = value => value;\n",
        "keep('kept');\n",
        "keep(true);\n",
    ));
    let arrows = nodes(&parsed, SyntaxKind::ArrowFunction);
    let [arrow] = arrows.as_slice() else {
        panic!("expected one JavaScript arrow")
    };
    let NodeData::ArrowFunction(function) = &parsed.arena.get(arrow.node).unwrap().data else {
        unreachable!()
    };
    let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    let [type_parameter] = function.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("the host must retain one JSDoc template parameter")
    };
    let NodeData::TypeParameterDeclaration(template) =
        &parsed.arena.get(*type_parameter).unwrap().data
    else {
        panic!("expected the template's source declaration")
    };
    let [parameter] = function.parameters.nodes.as_slice() else {
        panic!("overload parameters must not enter the host signature")
    };
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(*parameter).unwrap().data
    else {
        panic!("expected the host value parameter")
    };
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 2);
    let mut context = context(&parsed);

    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let callable = context.get_type_at_location(*arrow).unwrap();
    let call_signatures = signatures(&context, callable);
    let [signature] = call_signatures.as_slice() else {
        panic!("Go ignores overload tags on an arrow")
    };
    assert_eq!(selected_signature(&context, *arrow), *signature);
    assert_eq!(
        context.type_to_string(callable).unwrap(),
        "<T>(value: T) => T"
    );
    let template_symbol = context
        .file(FILE)
        .unwrap()
        .1
        .symbol(node_ref(*type_parameter))
        .unwrap();
    let parameter_symbol = context
        .file(FILE)
        .unwrap()
        .1
        .symbol(node_ref(*parameter))
        .unwrap();
    let template_type = context
        .get_type_at_location(node_ref(template.name))
        .unwrap();
    let template_record = context.store().type_payload(template_type).unwrap();
    assert_eq!(template_record.symbol(), Some(template_symbol));
    let TypeData::TypeParameter(template_data) = template_record.data() else {
        panic!("the template must remain a type parameter, not a fallback type")
    };
    assert_eq!(template_data.target, None);
    assert_eq!(template_data.mapper, None);
    let no_constraint = context
        .store()
        .intrinsic_bootstrap()
        .unwrap()
        .no_constraint_type;
    assert!(
        template_data
            .constraint
            .is_none_or(|constraint| constraint == no_constraint)
    );
    let signature_record = context.store().signature(*signature).unwrap();
    assert_eq!(signature_record.declaration(), Some(*arrow));
    assert_eq!(signature_record.type_parameters(), [template_type]);
    assert_eq!(signature_record.parameters(), [parameter_symbol]);
    assert_eq!(signature_record.target(), None);
    assert_eq!(signature_record.mapper(), None);
    assert_eq!(
        context.get_return_type_of_signature(*signature).unwrap(),
        template_type
    );
    for node in [
        parameter_data.name,
        parameter_data.type_.unwrap(),
        function.type_.unwrap(),
        function.body,
    ] {
        assert_eq!(
            context.get_type_at_location(node_ref(node)).unwrap(),
            template_type
        );
    }
    assert_eq!(
        context
            .get_symbol_at_location(node_ref(function.body))
            .unwrap(),
        Some(parameter_symbol),
    );

    let call_results = calls
        .iter()
        .zip(["\"kept\"", "true"])
        .map(|(&call, display)| {
            let result = context.get_type_at_location(call).unwrap();
            assert_eq!(context.type_to_string(result).unwrap(), display);
            let selected = selected_signature(&context, call);
            let selected_record = context.store().signature(selected).unwrap();
            assert_eq!(selected_record.target(), Some(*signature));
            assert!(selected_record.mapper().is_some());
            assert!(selected_record.type_parameters().is_empty());
            assert_eq!(selected_record.resolved_return_type(), Some(result));
            (call, result, selected)
        })
        .collect::<Vec<_>>();
    let before = counts(&context);
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(context.get_type_at_location(*arrow).unwrap(), callable);
        assert_eq!(signatures(&context, callable), call_signatures);
        assert_eq!(
            context
                .get_type_at_location(node_ref(template.name))
                .unwrap(),
            template_type
        );
        for &(call, result, selected) in &call_results {
            assert_eq!(context.get_type_at_location(call).unwrap(), result);
            assert_eq!(selected_signature(&context, call), selected);
        }
        assert_eq!(counts(&context), before);
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the unchanged named input and the other declaration boundaries together.
fn jsdoc_named_generic_overloads_and_other_declaration_boundaries() {
    for (source, kind) in [
        (
            concat!(
                "/** @template T @param {T} value @returns {T}\n",
                " * @overload @param {T} value @returns {T} */\n",
                "function keep(value) { return value; }\n",
            ),
            SyntaxKind::FunctionDeclaration,
        ),
        (
            concat!(
                "class Box {\n",
                "/** @overload @param {number} value @returns {number} */\n",
                "read(value) { return value; }\n",
                "}",
            ),
            SyntaxKind::MethodDeclaration,
        ),
        (
            concat!(
                "class Box {\n",
                "/** @overload @param {number} value */\n",
                "constructor(value) {}\n",
                "}",
            ),
            SyntaxKind::Constructor,
        ),
    ] {
        let parsed = parse_javascript_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let declarations = nodes(&parsed, kind);
        let source_node = NodeRef::new(parsed.arena.id(), FILE, parsed.source_file);
        if kind != SyntaxKind::FunctionDeclaration {
            let [declaration] = declarations.as_slice() else {
                panic!("expected one declaration with an overload tag")
            };
            for _ in 0..2 {
                assert_eq!(
                    plan_javascript_source_jsdoc(&parsed.arena, source_node),
                    Err(JsDocCommentError::UnsupportedOverloadDeclaration(
                        *declaration
                    )),
                );
            }
            continue;
        }
        let [overload, implementation] = declarations.as_slice() else {
            panic!("expected one generic overload and its implementation")
        };
        let planned = plan_javascript_source_jsdoc(&parsed.arena, source_node).unwrap();
        assert!(planned.diagnostics().is_empty());
        let documented = planned.declaration(*implementation).unwrap();
        let mut context = context(&parsed);
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let owner = symbol(&context, *overload);
        assert_eq!(symbol(&context, *implementation), owner);
        assert_eq!(
            context.get_symbol_declarations(owner).unwrap(),
            declarations
        );
        assert_eq!(
            context.store().symbol(owner).unwrap().value_declaration(),
            Some(*overload)
        );
        let callable = context.get_type_at_location(*implementation).unwrap();
        let row_signatures = declarations
            .iter()
            .map(|&node| selected_signature(&context, node))
            .collect::<Vec<_>>();
        assert_eq!(signatures(&context, callable), [row_signatures[0]]);
        assert_ne!(row_signatures[0], row_signatures[1]);
        let mut template_symbols = Vec::new();
        let mut template_types = Vec::new();
        let mut parameter_symbols = Vec::new();
        let mut queries = Vec::new();
        for (&declaration, &signature) in declarations.iter().zip(&row_signatures) {
            let record = parsed.arena.get(declaration.node).unwrap();
            let NodeData::FunctionDeclaration(function) = &record.data else {
                unreachable!()
            };
            assert_eq!(function.body.is_some(), declaration == *implementation);
            if declaration == *overload {
                assert_eq!(record.flags, NodeFlags::REPARSED);
                let start = source.find("@overload").unwrap() + 1;
                assert_eq!(record.range.start.get() as usize, start);
                assert_eq!(record.range.end.get() as usize, start + "overload".len());
            }
            let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
            let templates = function.type_parameters.as_ref().unwrap();
            let [template] = templates.nodes.as_slice() else {
                panic!("the overload and host must each own one template")
            };
            assert_eq!(
                templates.range.start.get() as usize,
                source.find("@template").unwrap()
            );
            assert_eq!(
                templates.range.end.get() as usize,
                source.find("@param").unwrap()
            );
            let template_record = parsed.arena.get(*template).unwrap();
            assert_eq!(template_record.flags, NodeFlags::REPARSED);
            assert_eq!(template_record.parent, Some(declaration.node));
            assert_eq!(
                template_record.range,
                documented.template_parameters()[0].range()
            );
            let NodeData::TypeParameterDeclaration(template_data) = &template_record.data else {
                unreachable!()
            };
            let template_symbol = symbol(&context, node_ref(*template));
            let template_type = context
                .get_type_at_location(node_ref(template_data.name))
                .unwrap();
            assert_eq!(
                context
                    .store()
                    .type_payload(template_type)
                    .unwrap()
                    .symbol(),
                Some(template_symbol)
            );
            assert!(matches!(
                context.store().type_payload(template_type).unwrap().data(),
                TypeData::TypeParameter(_)
            ));
            assert_eq!(
                context.get_symbol_declarations(template_symbol).unwrap(),
                [node_ref(*template)]
            );
            let [parameter] = function.parameters.nodes.as_slice() else {
                panic!("the unchanged source has one value parameter")
            };
            let parameter_symbol = symbol(&context, node_ref(*parameter));
            let NodeData::ParameterDeclaration(parameter) =
                &parsed.arena.get(*parameter).unwrap().data
            else {
                unreachable!()
            };
            for node in [
                template_data.name,
                parameter.name,
                parameter.type_.unwrap(),
                function.type_.unwrap(),
            ] {
                let node = node_ref(node);
                assert_eq!(context.get_type_at_location(node).unwrap(), template_type);
                queries.push((node, template_type));
            }
            let record = context.store().signature(signature).unwrap();
            assert_eq!(record.declaration(), Some(declaration));
            assert_eq!(record.type_parameters(), [template_type]);
            assert_eq!(record.parameters(), [parameter_symbol]);
            assert_eq!(record.target(), None);
            assert_eq!(record.mapper(), None);
            assert_eq!(
                context.get_return_type_of_signature(signature).unwrap(),
                template_type
            );
            template_symbols.push(template_symbol);
            template_types.push(template_type);
            parameter_symbols.push(parameter_symbol);
        }
        assert_ne!(template_symbols[0], template_symbols[1]);
        assert_ne!(template_types[0], template_types[1]);
        assert_ne!(parameter_symbols[0], parameter_symbols[1]);
        let before = counts(&context);
        for _ in 0..2 {
            context.recheck_source_file(FILE).unwrap();
            assert_eq!(
                context.get_type_at_location(*implementation).unwrap(),
                callable
            );
            assert_eq!(signatures(&context, callable), [row_signatures[0]]);
            for (&declaration, (&signature, &type_)) in declarations
                .iter()
                .zip(row_signatures.iter().zip(&template_types))
            {
                assert_eq!(selected_signature(&context, declaration), signature);
                assert_eq!(
                    context.get_return_type_of_signature(signature).unwrap(),
                    type_
                );
            }
            for &(node, type_) in &queries {
                assert_eq!(context.get_type_at_location(node).unwrap(), type_);
            }
            assert_eq!(counts(&context), before);
            assert!(context.diagnostics().is_empty());
        }
    }
}
