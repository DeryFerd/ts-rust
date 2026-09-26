use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, TypeMapperKind, signatures::SignatureFlags, types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_741);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic-class-method-annotations.ts\""),
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
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            no_implicit_any: true,
            strict_function_types: true,
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

fn signature(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(declaration)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the actual method or call must retain its signature")
}

#[derive(Clone, Copy)]
struct Parameter {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
}

struct Method {
    class: NodeRef,
    declaration: NodeRef,
    name: NodeRef,
    formal: NodeRef,
    parameters: Vec<Parameter>,
    return_annotation: NodeRef,
    returned: NodeRef,
}

fn method(parsed: &ParseResult) -> Method {
    let declarations = nodes(parsed, SyntaxKind::MethodDeclaration);
    let [declaration] = declarations.as_slice() else {
        panic!("the source must have one real class method")
    };
    let record = parsed.arena.get(declaration.node).unwrap();
    let NodeData::MethodDeclaration(data) = &record.data else {
        unreachable!()
    };
    let class = node(parsed, record.parent.unwrap());
    let NodeData::ClassDeclaration(owner) = &parsed.arena.get(class.node).unwrap().data else {
        panic!("the method must belong to the written class")
    };
    assert!(owner.type_parameters.is_none());
    assert!(owner.members.nodes.contains(&declaration.node));
    let [formal] = data.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("the method must own its one type parameter")
    };
    assert_eq!(
        parsed.arena.get(*formal).unwrap().parent,
        Some(declaration.node)
    );
    assert!(data.parameters.has_trailing_comma);
    assert!(!data.parameters.nodes.is_empty());
    let parameters = data
        .parameters
        .nodes
        .iter()
        .map(|&id| {
            let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(id).unwrap().data
            else {
                panic!("the method must keep its written value parameters")
            };
            Parameter {
                declaration: node(parsed, id),
                name: node(parsed, parameter.name),
                annotation: node(parsed, parameter.type_.unwrap()),
            }
        })
        .collect();
    let NodeData::Block(body) = &parsed.arena.get(data.body.unwrap()).unwrap().data else {
        panic!("the method must keep its actual body")
    };
    let [statement] = body.statements.nodes.as_slice() else {
        panic!("the focused method must retain one return statement")
    };
    let NodeData::ReturnStatement(returned) = &parsed.arena.get(*statement).unwrap().data else {
        panic!("the method must return its actual value parameter")
    };
    Method {
        class,
        declaration: *declaration,
        name: node(parsed, data.name),
        formal: node(parsed, *formal),
        parameters,
        return_annotation: node(parsed, data.type_.unwrap()),
        returned: node(parsed, returned.expression.unwrap()),
    }
}

#[derive(Clone, Copy)]
enum FirstQuery {
    Source,
    Parameter,
    Name,
}

const ORDERS: [FirstQuery; 3] = [FirstQuery::Source, FirstQuery::Parameter, FirstQuery::Name];

fn prepare<'a>(
    parsed: &'a ParseResult,
    method: &Method,
    first: FirstQuery,
) -> CanonicalCheckerContext<'a> {
    let mut context = context(parsed);
    assert!(
        context
            .store()
            .signature_links(method.declaration)
            .is_none()
    );
    let annotation = method.parameters.last().unwrap().annotation;
    let early = match first {
        FirstQuery::Source => None,
        FirstQuery::Parameter => Some(context.get_type_from_type_node(annotation).unwrap()),
        FirstQuery::Name => Some(context.get_type_at_location(method.name).unwrap()),
    };
    context.check_source_file(FILE).unwrap();
    if let Some(early) = early {
        let repeated = match first {
            FirstQuery::Parameter => context.get_type_from_type_node(annotation).unwrap(),
            FirstQuery::Name => context.get_type_at_location(method.name).unwrap(),
            FirstQuery::Source => unreachable!(),
        };
        assert_eq!(repeated, early);
    }
    assert!(
        context
            .store()
            .source_file_links(context.source_file(FILE).unwrap())
            .unwrap()
            .type_checked
    );
    context
}

struct MethodTypes {
    callable: TypeId,
    signature: SignatureId,
    formal: TypeId,
    parameters: Vec<TypeId>,
    returned: TypeId,
}

fn assert_formal(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    declaration: NodeRef,
) -> TypeId {
    let owner = symbol(context, declaration);
    let type_ = context.get_declared_type_of_symbol(owner).unwrap();
    let NodeData::TypeParameterDeclaration(data) =
        &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("the formal must be an actual source type parameter")
    };
    let constraint = data
        .constraint
        .map(|id| context.get_type_from_type_node(node(parsed, id)).unwrap());
    let default = data
        .default_type
        .map(|id| context.get_type_from_type_node(node(parsed, id)).unwrap());
    let store = context.store();
    assert_eq!(
        store.symbol(owner).unwrap().flags(),
        SymbolFlags::TYPE_PARAMETER
    );
    assert_eq!(
        store.symbol(owner).unwrap().declarations(),
        Some(&[declaration][..])
    );
    assert_eq!(store.type_payload(type_).unwrap().symbol(), Some(owner));
    let TypeData::TypeParameter(formal) = store.type_payload(type_).unwrap().data() else {
        panic!("the source formal must not be erased")
    };
    assert_eq!(formal.target, None);
    assert_eq!(formal.mapper, None);
    assert_eq!(formal.constraint, constraint);
    assert_eq!(formal.resolved_default_type, default);
    type_
}

fn assert_nongeneric_class(context: &CanonicalCheckerContext<'_>, instance: TypeId) {
    let store = context.store();
    assert!(
        store
            .type_payload(instance)
            .unwrap()
            .object_flags()
            .contains(ObjectFlags::CLASS)
    );
    let TypeData::Interface(class_data) = store.type_payload(instance).unwrap().data() else {
        panic!("the method owner must remain its real class instance")
    };
    assert_eq!(class_data.outer_type_parameter_count, 0);
    assert!(
        class_data
            .reference
            .resolved_type_arguments
            .as_ref()
            .is_none_or(Vec::is_empty)
    );
}

fn assert_source_method(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    method: &Method,
) -> MethodTypes {
    let class = symbol(context, method.class);
    let owner = symbol(context, method.declaration);
    let instance = context.get_declared_type_of_symbol(class).unwrap();
    assert_nongeneric_class(context, instance);
    let callable = context.get_type_at_location(method.name).unwrap();
    assert_eq!(
        context.get_type_at_location(method.declaration),
        Ok(callable)
    );
    assert_eq!(
        context.get_symbol_at_location(method.name).unwrap(),
        Some(owner)
    );
    let formal = assert_formal(context, parsed, method.formal);
    let parameters = method
        .parameters
        .iter()
        .map(|parameter| {
            context
                .get_type_from_type_node(parameter.annotation)
                .unwrap()
        })
        .collect::<Vec<_>>();
    let returned = context
        .get_type_from_type_node(method.return_annotation)
        .unwrap();
    let declared = signature(context, method.declaration);
    assert_eq!(context.get_return_type_of_signature(declared), Ok(returned));
    assert_eq!(context.get_type_at_location(method.returned), Ok(returned));
    assert_eq!(
        context.get_symbol_at_location(method.returned).unwrap(),
        Some(symbol(
            context,
            method.parameters.last().unwrap().declaration
        ))
    );
    let store = context.store();
    assert_eq!(store.symbol(owner).unwrap().flags(), SymbolFlags::METHOD);
    assert_eq!(store.symbol(owner).unwrap().parent(), Some(class));
    assert_eq!(
        store.symbol(owner).unwrap().declarations(),
        Some(&[method.declaration][..])
    );
    assert_eq!(store.type_payload(callable).unwrap().symbol(), Some(owner));
    let TypeData::Object(object) = store.type_payload(callable).unwrap().data() else {
        panic!("the method must retain its source callable object")
    };
    assert_eq!(object.target, None);
    assert_eq!(object.mapper, None);
    assert_eq!(object.structured.call_signature_count, 1);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[declared][..])
    );
    let record = store.signature(declared).unwrap();
    assert_eq!(record.declaration(), Some(method.declaration));
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert_eq!(record.type_parameters(), [formal]);
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.this_parameter(), None);
    assert_eq!(record.resolved_return_type(), Some(returned));
    assert_eq!(
        record.min_argument_count(),
        i32::try_from(parameters.len()).unwrap()
    );
    assert_eq!(record.parameters().len(), method.parameters.len());
    for ((&parameter, syntax), &type_) in record
        .parameters()
        .iter()
        .zip(&method.parameters)
        .zip(&parameters)
    {
        assert_eq!(parameter, symbol(context, syntax.declaration));
        assert_eq!(
            store.symbol(parameter).unwrap().value_declaration(),
            Some(syntax.declaration)
        );
        let links = store.value_symbol_links(parameter).unwrap();
        assert_eq!(links.resolved_type, Some(type_));
        assert_eq!(links.target, None);
        assert_eq!(links.mapper, None);
    }
    MethodTypes {
        callable,
        signature: declared,
        formal,
        parameters,
        returned,
    }
}

fn callee(parsed: &ParseResult, call: NodeRef) -> NodeRef {
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected the actual method call")
    };
    node(parsed, data.expression)
}

fn argument(parsed: &ParseResult, call: NodeRef, index: usize) -> NodeRef {
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected the actual method call")
    };
    node(parsed, data.arguments.nodes[index])
}

#[allow(clippy::too_many_arguments)] // Check the declared formal, selected return, and value parameters together.
fn assert_call(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    call: NodeRef,
    source: &MethodTypes,
    type_argument: TypeId,
    returned: TypeId,
    parameters: &[TypeId],
    checked: bool,
) -> SignatureId {
    assert_eq!(
        context.get_type_at_location(callee(parsed, call)),
        Ok(source.callable)
    );
    assert_eq!(context.get_type_at_location(call), Ok(returned));
    let selected = signature(context, call);
    assert_eq!(context.get_return_type_of_signature(selected), Ok(returned));
    let store = context.store();
    let original = store.signature(source.signature).unwrap();
    let record = store.signature(selected).unwrap();
    assert_ne!(selected, source.signature);
    assert_eq!(record.declaration(), original.declaration());
    assert_eq!(record.target(), Some(source.signature));
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.min_argument_count(), original.min_argument_count());
    let mapper = record.mapper().unwrap();
    assert_eq!(store.mapper_kind(mapper), Some(TypeMapperKind::Simple));
    assert_eq!(store.map_type(mapper, source.formal), Some(type_argument));
    assert_eq!(record.parameters().len(), parameters.len());
    for ((&parameter, &target), &type_) in record
        .parameters()
        .iter()
        .zip(original.parameters())
        .zip(parameters)
    {
        assert_ne!(parameter, target);
        let links = store.value_symbol_links(parameter).unwrap();
        assert_eq!(links.target, Some(target));
        assert_eq!(links.mapper, Some(mapper));
        assert_eq!(links.resolved_type, checked.then_some(type_));
        assert_eq!(
            store.symbol(parameter).unwrap().declarations(),
            store.symbol(target).unwrap().declarations()
        );
        assert_eq!(
            store.symbol(parameter).unwrap().value_declaration(),
            store.symbol(target).unwrap().value_declaration()
        );
    }
    selected
}

fn snapshot(context: &CanonicalCheckerContext<'_>) -> String {
    format!("{:?}\n{:?}", context.store(), context.diagnostics())
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    method: &Method,
    source: &MethodTypes,
    calls: &[NodeRef],
) {
    let mut queries = vec![
        (method.name, source.callable),
        (method.declaration, source.callable),
        (method.returned, source.returned),
    ];
    for parameter in &method.parameters {
        queries.push((
            parameter.name,
            context.get_type_at_location(parameter.name).unwrap(),
        ));
    }
    let mut returns = vec![(source.signature, source.returned)];
    let mut selected = Vec::new();
    for &call in calls {
        for location in [callee(parsed, call), call] {
            queries.push((location, context.get_type_at_location(location).unwrap()));
        }
        let signature = signature(context, call);
        selected.push(signature);
        returns.push((
            signature,
            context.get_return_type_of_signature(signature).unwrap(),
        ));
    }
    let annotations = method
        .parameters
        .iter()
        .map(|parameter| parameter.annotation)
        .chain([method.return_annotation])
        .map(|annotation| {
            (
                annotation,
                context.get_type_from_type_node(annotation).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    let warm = snapshot(context);
    for recheck in [false, true, true] {
        if recheck {
            context.recheck_source_file(FILE).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        for &(location, expected) in &queries {
            assert_eq!(context.get_type_at_location(location), Ok(expected));
        }
        for &(annotation, expected) in &annotations {
            assert_eq!(context.get_type_from_type_node(annotation), Ok(expected));
        }
        for &(signature, expected) in &returns {
            assert_eq!(
                context.get_return_type_of_signature(signature),
                Ok(expected)
            );
        }
        assert_eq!(assert_formal(context, parsed, method.formal), source.formal);
        assert_eq!(
            calls
                .iter()
                .map(|&call| signature(context, call))
                .collect::<Vec<_>>(),
            selected
        );
        assert_eq!(snapshot(context), warm);
    }
}

#[test]
fn generic_class_methods_keep_real_formals_calls_and_query_order() {
    let parsed = parse_source_file(concat!(
        "class Service { read<T>(value: T,): T { return value; } }\n",
        "declare const service: Service;\n",
        "const text: string = service.read<string>('one');\n",
        "const number: number = service.read<number>(1);\n",
        "const inferred: 'two' = service.read('two');\n",
        "const repeated: string = service.read<string>('three');\n",
    ));
    let method = method(&parsed);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 4);
    for order in ORDERS {
        let mut context = prepare(&parsed, &method, order);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let source = assert_source_method(&mut context, &parsed, &method);
        assert_eq!(source.parameters, [source.formal]);
        assert_eq!(source.returned, source.formal);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (string, number) = (bootstrap.string_type, bootstrap.number_type);
        let inferred = context
            .get_type_at_location(argument(&parsed, calls[2], 0))
            .unwrap();
        let TypeData::Literal(literal) = context.store().type_payload(inferred).unwrap().data()
        else {
            panic!("the returned unconstrained formal must keep the actual fresh argument")
        };
        assert_eq!(literal.fresh_type, Some(inferred));
        assert_ne!(literal.regular_type, inferred);
        assert_eq!(context.type_to_string(inferred).unwrap(), "\"two\"");
        let expected = [string, number, inferred, string];
        let selected = calls
            .iter()
            .zip(expected)
            .map(|(&call, type_)| {
                assert_call(
                    &mut context,
                    &parsed,
                    call,
                    &source,
                    type_,
                    type_,
                    &[type_],
                    true,
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(selected[0], selected[3]);
        assert_ne!(selected[0], selected[1]);
        assert_ne!(selected[1], selected[2]);
        assert_replay(&mut context, &parsed, &method, &source, &calls);
    }
}

fn assert_alias_instance(
    context: &CanonicalCheckerContext<'_>,
    alias: SemanticSymbolId,
    formal: TypeId,
    argument: TypeId,
    type_: TypeId,
) {
    let store = context.store();
    let record = store.type_payload(type_).unwrap();
    let metadata = store.type_alias(record.alias().unwrap()).unwrap();
    assert_eq!(metadata.symbol(), Some(alias));
    assert_eq!(metadata.type_arguments(), Some(&[argument][..]));
    let TypeData::Object(object) = record.data() else {
        panic!("the dependent annotation must remain its real alias object")
    };
    let target = store.type_payload(object.target.unwrap()).unwrap();
    assert_eq!(target.symbol(), record.symbol());
    let metadata = store.type_alias(target.alias().unwrap()).unwrap();
    assert_eq!(metadata.symbol(), Some(alias));
    assert_eq!(metadata.type_arguments(), Some(&[formal][..]));
    let mapper = object.mapper.unwrap();
    assert_eq!(store.map_type(mapper, formal), Some(argument));
}

#[test]
fn generic_class_method_alias_annotations_keep_distinct_parameter_owners() {
    let parsed = parse_source_file(concat!(
        "type Box<T extends string = string> = { value: T };\n",
        "class Service { keep<T extends string>(value: Box<T>,): Box<T> { return value; } }\n",
        "declare const service: Service;\n",
        "declare const input: Box<string>;\n",
        "const result: Box<string> = service.keep<string>(input);\n",
        "const repeated: Box<string> = service.keep<string>(input);\n",
    ));
    let method = method(&parsed);
    let alias = nodes(&parsed, SyntaxKind::TypeAliasDeclaration)[0];
    let NodeData::TypeAliasDeclaration(alias_data) = &parsed.arena.get(alias.node).unwrap().data
    else {
        unreachable!()
    };
    let alias_formal = node(
        &parsed,
        alias_data.type_parameters.as_ref().unwrap().nodes[0],
    );
    assert_eq!(
        parsed.arena.get(alias_formal.node).unwrap().parent,
        Some(alias.node)
    );
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 2);
    for order in ORDERS {
        let mut context = prepare(&parsed, &method, order);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let source = assert_source_method(&mut context, &parsed, &method);
        let alias_parameter = assert_formal(&mut context, &parsed, alias_formal);
        assert_ne!(alias_parameter, source.formal);
        assert_ne!(
            symbol(&context, alias_formal),
            symbol(&context, method.formal)
        );
        assert_eq!(source.parameters, [source.returned]);
        let alias_symbol = symbol(&context, alias);
        assert_alias_instance(
            &context,
            alias_symbol,
            alias_parameter,
            source.formal,
            source.returned,
        );
        let input = context
            .get_type_at_location(argument(&parsed, calls[0], 0))
            .unwrap();
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert_alias_instance(&context, alias_symbol, alias_parameter, string, input);
        let selected = calls
            .iter()
            .map(|&call| {
                assert_call(
                    &mut context,
                    &parsed,
                    call,
                    &source,
                    string,
                    input,
                    &[input],
                    true,
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(selected[0], selected[1]);
        assert_replay(&mut context, &parsed, &method, &source, &calls);
    }
}

fn assert_diagnostics(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    method: &Method,
    calls: &[NodeRef],
) {
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 4, "{diagnostics:?}");
    for (diagnostic, call, index, expected) in [
        (
            &diagnostics[0],
            calls[2],
            0,
            "Argument of type 'string' is not assignable to parameter of type 'number'.",
        ),
        (
            &diagnostics[1],
            calls[3],
            1,
            "Argument of type 'number' is not assignable to parameter of type 'string'.",
        ),
    ] {
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.node, Some(argument(parsed, call, index)));
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), expected);
        assert!(diagnostic.related_information.is_empty());
    }
    let NodeData::CallExpression(bad_constraint) = &parsed.arena.get(calls[4].node).unwrap().data
    else {
        unreachable!()
    };
    let argument = node(
        parsed,
        bad_constraint.type_arguments.as_ref().unwrap().nodes[0],
    );
    let constraint = &diagnostics[2];
    assert_eq!(constraint.diagnostic.code(), 2344);
    assert_eq!(constraint.node, Some(argument));
    assert_eq!(constraint.range_override, None);
    assert_eq!(
        constraint.diagnostic.render().unwrap(),
        "Type 'number' does not satisfy the constraint 'string'."
    );
    assert!(constraint.related_information.is_empty());
    let missing = &diagnostics[3];
    assert_eq!(missing.diagnostic.code(), 2554);
    assert_eq!(missing.node, Some(callee(parsed, calls[5])));
    assert_eq!(missing.range_override, None);
    assert_eq!(
        missing.diagnostic.render().unwrap(),
        "Expected 2 arguments, but got 1."
    );
    let [related] = missing.related_information.as_slice() else {
        panic!("the missing argument must identify the original value parameter")
    };
    assert_eq!(related.diagnostic.code(), 6210);
    assert_eq!(related.node, Some(method.parameters[1].declaration));
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument for 'value' was not provided."
    );
}

#[test]
fn generic_class_methods_keep_constraints_and_exact_call_diagnostics() {
    let parsed = parse_source_file(concat!(
        "class Service { select<T extends string>(tag: number, value: T,): T { return value; } }\n",
        "declare const service: Service;\n",
        "const good: string = service.select<string>(1, 'ok');\n",
        "const inferred: 'yes' = service.select(1, 'yes');\n",
        "service.select<string>('wrong', 'ok');\n",
        "service.select<string>(1, 2);\n",
        "service.select<number>(1, 2);\n",
        "service.select<string>(1);\n",
    ));
    let method = method(&parsed);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 6);
    for order in ORDERS {
        let mut context = prepare(&parsed, &method, order);
        let source = assert_source_method(&mut context, &parsed, &method);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let (number, string) = (bootstrap.number_type, bootstrap.string_type);
        assert_eq!(source.parameters, [number, source.formal]);
        assert_eq!(source.returned, source.formal);
        let argument = context
            .get_type_at_location(argument(&parsed, calls[1], 1))
            .unwrap();
        let TypeData::Literal(literal) = context.store().type_payload(argument).unwrap().data()
        else {
            panic!("the inferred argument must retain its real string literal")
        };
        let inferred = literal.regular_type;
        assert_eq!(literal.fresh_type, Some(argument));
        assert_ne!(inferred, argument);
        assert_eq!(context.type_to_string(inferred).unwrap(), "\"yes\"");
        let expected = [string, inferred, string, string, number, string];
        let selected = calls
            .iter()
            .zip(expected)
            .enumerate()
            .map(|(index, (&call, type_))| {
                assert_call(
                    &mut context,
                    &parsed,
                    call,
                    &source,
                    type_,
                    type_,
                    &[number, type_],
                    index < 2,
                )
            })
            .collect::<Vec<_>>();
        for (index, recovery) in selected.iter().enumerate().skip(2) {
            assert!(!selected[..index].contains(recovery));
        }
        assert_diagnostics(&context, &parsed, &method, &calls);
        assert_replay(&mut context, &parsed, &method, &source, &calls);
    }
}
