use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeData, TypeId,
    signatures::SignatureFlags, type_records::LiteralValue,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(205_320);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/request-class.ts\""),
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
        vec![(FILE, &parsed.arena)],
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            strict_function_types: true,
            strict_property_initialization: true,
            no_implicit_any: true,
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2022,
                ..CanonicalNameResolverOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut found = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == kind).then_some((record.range.start, node(parsed, id)))
        })
        .collect::<Vec<_>>();
    found.sort_by_key(|(start, _)| *start);
    found.into_iter().map(|(_, node)| node).collect()
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn parameter_name(parsed: &ParseResult, declaration: NodeRef) -> NodeRef {
    let NodeData::ParameterDeclaration(parameter) =
        &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected a constructor parameter")
    };
    node(parsed, parameter.name)
}

fn replay(context: &mut CanonicalCheckerContext<'_>, locations: &[(NodeRef, TypeId)]) {
    let counts = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
        )
    };
    let warm_counts = counts(context);
    let diagnostics = context.diagnostics().clone();
    context.recheck_source_file(FILE).unwrap();
    for &(location, expected) in locations {
        assert_eq!(context.get_type_at_location(location).unwrap(), expected);
    }
    assert_eq!(counts(context), warm_counts);
    assert_eq!(context.diagnostics(), &diagnostics);
    assert!(
        context
            .store()
            .source_file_links(context.source_file(FILE).unwrap())
            .unwrap()
            .type_checked
    );
}

#[test]
#[allow(clippy::too_many_lines)] // Keep constructor types, body reads, calls, and replay together.
fn ordinary_constructor_literal_defaults_keep_body_types_and_call_arity() {
    let parsed = parse_source_file(concat!(
        "class RequestState {\n",
        "  method: string; path: string; index: number;\n",
        "  constructor(method: string, path: string = '/', index: number = 0) {\n",
        "    this.method = method; this.path = path; this.index = index;\n",
        "  }\n",
        "}\n",
        "new RequestState('GET');\n",
        "new RequestState('POST', '/users', 2);\n",
    ));
    let class = nodes(&parsed, SyntaxKind::ClassDeclaration)[0];
    let constructor = nodes(&parsed, SyntaxKind::Constructor)[0];
    let parameters = nodes(&parsed, SyntaxKind::Parameter);
    assert_eq!(parameters.len(), 3);
    for query_first in [false, true] {
        let mut context = context(&parsed);
        if query_first {
            context
                .get_type_at_location(parameter_name(&parsed, parameters[1]))
                .unwrap();
        }
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let class_symbol = symbol(&context, class);
        let members = context.get_nongeneric_class_members(class_symbol).unwrap();
        assert_eq!(members.declared_instance_properties().len(), 3);
        let instance = members.shells().instance_type();
        assert_eq!(
            context.get_declared_type_of_symbol(class_symbol).unwrap(),
            instance
        );
        let parameter_symbols = parameters
            .iter()
            .map(|&parameter| symbol(&context, parameter))
            .collect::<Vec<_>>();
        let signature = context
            .store()
            .signature(members.default_construct_signature())
            .unwrap();
        assert_eq!(signature.declaration(), Some(constructor));
        assert_eq!(signature.flags(), SignatureFlags::CONSTRUCT);
        assert_eq!(signature.parameters(), parameter_symbols.as_slice());
        assert_eq!(signature.min_argument_count(), 1);
        assert_eq!(signature.resolved_return_type(), Some(instance));
        let intrinsic = context.store().intrinsic_bootstrap().unwrap();
        let expected = [
            intrinsic.string_type,
            intrinsic.string_type,
            intrinsic.number_type,
        ];
        let mut checked = Vec::new();
        for ((&parameter, &symbol), expected) in parameters
            .iter()
            .zip(&parameter_symbols)
            .zip(expected)
        {
            let record = context.store().symbol(symbol).unwrap();
            assert_eq!(record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
            assert_eq!(record.declarations(), Some(&[parameter][..]));
            assert_eq!(record.value_declaration(), Some(parameter));
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(symbol)
                    .unwrap()
                    .resolved_type,
                Some(expected)
            );
            let NodeData::ParameterDeclaration(data) =
                &parsed.arena.get(parameter.node).unwrap().data
            else {
                unreachable!()
            };
            assert!(data.modifiers.is_none());
            let name = parameter_name(&parsed, parameter);
            assert_eq!(context.get_type_at_location(name).unwrap(), expected);
            assert_eq!(
                context
                    .get_type_from_type_node(node(&parsed, data.type_.unwrap()))
                    .unwrap(),
                expected
            );
            checked.push((name, expected));
            if let Some(initializer) = data.initializer {
                let initializer = node(&parsed, initializer);
                let literal_type = context.get_type_at_location(initializer).unwrap();
                let TypeData::Literal(literal) =
                    context.store().type_payload(literal_type).unwrap().data()
                else {
                    panic!("the written default must keep its literal type")
                };
                match parsed.arena.get(initializer.node).unwrap().kind {
                    SyntaxKind::StringLiteral => {
                        assert_eq!(literal.value, LiteralValue::String("/".to_owned()));
                    }
                    SyntaxKind::NumericLiteral => {
                        assert_eq!(
                            literal.value,
                            LiteralValue::Number(ts_jsnum::Number::new(0.0))
                        );
                    }
                    _ => panic!("the defaults are one string and one number"),
                }
                checked.push((initializer, literal_type));
            }
        }
        let assignments = nodes(&parsed, SyntaxKind::BinaryExpression);
        assert_eq!(assignments.len(), expected.len());
        for (assignment, expected) in assignments.into_iter().zip(expected) {
            let NodeData::BinaryExpression(data) = &parsed.arena.get(assignment.node).unwrap().data
            else {
                unreachable!()
            };
            let value = node(&parsed, data.right);
            assert_eq!(context.get_type_at_location(value).unwrap(), expected);
            checked.push((value, expected));
        }
        let calls = nodes(&parsed, SyntaxKind::NewExpression);
        assert_eq!(calls.len(), 2);
        for call in calls {
            assert_eq!(context.get_type_at_location(call).unwrap(), instance);
            checked.push((call, instance));
        }
        replay(&mut context, &checked);
    }
}

#[test]
fn ordinary_constructor_defaults_keep_native_assignment_argument_and_arity_errors() {
    let parsed = parse_source_file(concat!(
        "class RequestState {\n",
        "  path: string; index: number;\n",
        "  constructor(method: string, path: string = 0, index: number = '/') {\n",
        "    this.path = path; this.index = index;\n",
        "  }\n",
        "}\n",
        "const wrong: number = 1;\n",
        "new RequestState('GET', wrong);\n",
        "new RequestState();\n",
    ));
    let parameters = nodes(&parsed, SyntaxKind::Parameter);
    assert_eq!(parameters.len(), 3);
    let calls = nodes(&parsed, SyntaxKind::NewExpression);
    let NodeData::NewExpression(wrong_call) = &parsed.arena.get(calls[0].node).unwrap().data
    else {
        unreachable!()
    };
    let argument = node(&parsed, wrong_call.arguments.as_ref().unwrap().nodes[1]);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 4, "{diagnostics:?}");
    for (diagnostic, (code, location, arguments, message)) in diagnostics.iter().zip([
        (
            2322,
            parameter_name(&parsed, parameters[1]),
            ["number", "string"],
            "Type 'number' is not assignable to type 'string'.",
        ),
        (
            2322,
            parameter_name(&parsed, parameters[2]),
            ["string", "number"],
            "Type 'string' is not assignable to type 'number'.",
        ),
        (
            2345,
            argument,
            ["number", "string"],
            "Argument of type 'number' is not assignable to parameter of type 'string'.",
        ),
    ]) {
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(diagnostic.node, Some(location));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.arguments, arguments);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert!(diagnostic.related_information.is_empty());
    }
    let missing = &diagnostics[3];
    assert_eq!(missing.diagnostic.code(), 2554);
    assert_eq!(missing.node, Some(calls[1]));
    assert_eq!(missing.range_override, None);
    assert_eq!(missing.diagnostic.arguments, ["1-3", "0"]);
    assert_eq!(
        missing.diagnostic.render().unwrap(),
        "Expected 1-3 arguments, but got 0."
    );
    let [note] = missing.related_information.as_slice() else {
        panic!("the missing argument must point to the required parameter")
    };
    assert_eq!(note.node, Some(parameters[0]));
    assert_eq!(note.diagnostic.code(), 6210);
    assert_eq!(
        note.diagnostic.render().unwrap(),
        "An argument for 'method' was not provided."
    );
    let intrinsic = context.store().intrinsic_bootstrap().unwrap();
    let declared = [
        intrinsic.string_type,
        intrinsic.string_type,
        intrinsic.number_type,
    ];
    let mut checked = Vec::new();
    for (&parameter, expected) in parameters.iter().zip(declared) {
        let name = parameter_name(&parsed, parameter);
        assert_eq!(context.get_type_at_location(name).unwrap(), expected);
        checked.push((name, expected));
    }
    let class = nodes(&parsed, SyntaxKind::ClassDeclaration)[0];
    let class_symbol = symbol(&context, class);
    let instance = context.get_declared_type_of_symbol(class_symbol).unwrap();
    for call in calls {
        assert_eq!(context.get_type_at_location(call).unwrap(), instance);
        checked.push((call, instance));
    }
    replay(&mut context, &checked);
}
