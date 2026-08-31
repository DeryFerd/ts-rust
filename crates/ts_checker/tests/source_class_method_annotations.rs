use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnostics, CanonicalCheckerOptions,
    DeclaredTypeLinks, IntrinsicBootstrapOptions, SignatureId, SignatureLinks, SourceCheckError,
    SourceFileLinks, SymbolNodeLinks, TypeData, TypeId, TypeNodeLinks, UnsupportedSourceSyntax,
    ValueSymbolLinks, signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_605);

// These are direct annotation controls, not the full upstream fixture.
// privateIdentifierPropertyAccessDestructuringAssignmentES6.ts still needs its
// private object field, destructuring assignment, and imported-helper checks.
fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/class-method-annotations.ts\""),
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

fn reference(parsed: &ParseResult, node: ts_ast::NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, node)
}

fn nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
    let mut found = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == kind).then_some((record.range.start, reference(parsed, node)))
        })
        .collect::<Vec<_>>();
    found.sort_by_key(|(start, _)| *start);
    found.into_iter().map(|(_, node)| node).collect()
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap()
}

struct Method {
    class: NodeRef,
    declaration: NodeRef,
    name: NodeRef,
    parameter: NodeRef,
    parameter_name: NodeRef,
    annotation: NodeRef,
}

fn method(parsed: &ParseResult, expected: &str) -> Method {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::MethodDeclaration(method) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(method.name)?.data else {
                return None;
            };
            if name.text != expected {
                return None;
            }
            let [parameter] = method.parameters.nodes.as_slice() else {
                panic!("the method must keep its one written parameter")
            };
            let NodeData::ParameterDeclaration(data) = &parsed.arena.get(*parameter)?.data else {
                panic!("the method must keep its parameter declaration")
            };
            Some(Method {
                class: reference(parsed, record.parent.unwrap()),
                declaration: reference(parsed, node),
                name: reference(parsed, method.name),
                parameter: reference(parsed, *parameter),
                parameter_name: reference(parsed, data.name),
                annotation: reference(parsed, data.type_.unwrap()),
            })
        })
        .unwrap_or_else(|| panic!("missing method {expected}"))
}

fn returned(parsed: &ParseResult, method: &Method) -> (NodeRef, NodeRef) {
    let NodeData::MethodDeclaration(data) =
        &parsed.arena.get(method.declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let NodeData::Block(body) = &parsed.arena.get(data.body.unwrap()).unwrap().data else {
        panic!("the method must keep its written body")
    };
    let [statement] = body.statements.nodes.as_slice() else {
        panic!("the method must keep its single return")
    };
    let NodeData::ReturnStatement(returned) = &parsed.arena.get(*statement).unwrap().data else {
        panic!("the statement must remain a return")
    };
    (
        reference(parsed, *statement),
        reference(parsed, returned.expression.unwrap()),
    )
}

fn assert_nested_properties(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    annotation: NodeRef,
    type_: TypeId,
) -> [SemanticSymbolId; 2] {
    let mut current = (annotation, type_);
    let mut properties = Vec::new();
    for _ in 0..2 {
        let NodeData::TypeLiteralNode(literal) = &parsed.arena.get(current.0.node).unwrap().data
        else {
            panic!("the written parameter must keep both nested type literals")
        };
        let [declaration] = literal.members.nodes.as_slice() else {
            panic!("each nested object must keep its one property")
        };
        let NodeData::PropertyDeclaration(property) = &parsed.arena.get(*declaration).unwrap().data
        else {
            panic!("the property must keep its source signature")
        };
        let declaration = reference(parsed, *declaration);
        let property_annotation = reference(parsed, property.type_.unwrap());
        let owner = symbol(context, current.0);
        let property_symbol = symbol(context, declaration);
        let store = context.store();
        let record = store.type_payload(current.1).unwrap();
        assert_eq!(record.symbol(), Some(owner));
        let TypeData::Object(object) = record.data() else {
            panic!("a type literal parameter must remain an object type")
        };
        assert_eq!(
            object.structured.properties.as_deref(),
            Some(&[property_symbol][..])
        );
        let property_record = store.symbol(property_symbol).unwrap();
        assert_eq!(property_record.flags(), SymbolFlags::PROPERTY);
        assert_eq!(property_record.parent(), Some(owner));
        assert_eq!(property_record.declarations(), Some(&[declaration][..]));
        assert_eq!(property_record.value_declaration(), Some(declaration));
        let property_type = store
            .value_symbol_links(property_symbol)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(
            context.get_type_from_type_node(current.0).unwrap(),
            current.1
        );
        assert_eq!(
            context
                .get_type_from_type_node(property_annotation)
                .unwrap(),
            property_type
        );
        properties.push(property_symbol);
        current = (property_annotation, property_type);
    }
    assert_eq!(
        parsed.arena.get(current.0.node).unwrap().kind,
        SyntaxKind::NumberKeyword
    );
    assert_eq!(
        current.1,
        context.store().intrinsic_bootstrap().unwrap().number_type
    );
    properties.try_into().unwrap()
}

fn assert_method(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    method: &Method,
    return_type: TypeId,
) -> (SignatureId, TypeId) {
    let class = symbol(context, method.class);
    let owner = symbol(context, method.declaration);
    let parameter = symbol(context, method.parameter);
    let signature = signature(context, method.declaration);
    let store = context.store();
    let member = store.symbol(owner).unwrap();
    assert_eq!(member.flags(), SymbolFlags::METHOD);
    assert_eq!(member.parent(), Some(class));
    assert_eq!(member.declarations(), Some(&[method.declaration][..]));
    assert_eq!(member.value_declaration(), Some(method.declaration));
    assert_eq!(
        store.symbol(parameter).unwrap().declarations(),
        Some(&[method.parameter][..])
    );
    let record = store.signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(method.declaration));
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert_eq!(record.parameters(), &[parameter]);
    assert_eq!(record.min_argument_count(), 1);
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.resolved_return_type(), Some(return_type));
    let callable = store
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap();
    let callable_record = store.type_payload(callable).unwrap();
    assert_eq!(callable_record.symbol(), Some(owner));
    let TypeData::Object(object) = callable_record.data() else {
        panic!("the method must keep its callable object")
    };
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    let parameter_type = store
        .value_symbol_links(parameter)
        .unwrap()
        .resolved_type
        .unwrap();
    assert_eq!(resolved_type(context, method.annotation), parameter_type);
    let properties = assert_nested_properties(context, parsed, method.annotation, parameter_type);
    assert_eq!(
        context.get_type_at_location(method.parameter_name).unwrap(),
        parameter_type
    );
    assert_eq!(context.get_type_at_location(method.name).unwrap(), callable);
    assert_eq!(
        context.get_symbol_at_location(method.name).unwrap(),
        Some(owner)
    );
    assert_eq!(
        context
            .get_symbol_at_location(method.parameter_name)
            .unwrap(),
        Some(parameter)
    );
    let (_, expression) = returned(parsed, method);
    let NodeData::PropertyAccessExpression(outer) =
        &parsed.arena.get(expression.node).unwrap().data
    else {
        panic!("the return must keep the nested property read")
    };
    let NodeData::PropertyAccessExpression(inner) =
        &parsed.arena.get(outer.expression).unwrap().data
    else {
        panic!("the return must keep both property reads")
    };
    for (name, property) in [(inner.name, properties[0]), (outer.name, properties[1])] {
        assert_eq!(
            context
                .get_symbol_at_location(reference(parsed, name))
                .unwrap(),
            Some(property)
        );
    }
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(context.get_type_at_location(expression).unwrap(), number);
    (signature, parameter_type)
}

type NodePublication = (
    NodeRef,
    Option<TypeNodeLinks>,
    Option<SymbolNodeLinks>,
    Option<SignatureLinks>,
);
type SymbolPublication = (
    SemanticSymbolId,
    Option<DeclaredTypeLinks>,
    Option<ValueSymbolLinks>,
);

#[derive(Debug, Eq, PartialEq)]
struct Publication {
    counts: [usize; 7],
    nodes: Vec<NodePublication>,
    symbols: Vec<SymbolPublication>,
    source: Option<SourceFileLinks>,
    diagnostics: CanonicalCheckerDiagnostics,
}

fn publication(context: &CanonicalCheckerContext<'_>, parsed: &ParseResult) -> Publication {
    let store = context.store();
    Publication {
        counts: [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.type_alias_len(),
            store.index_info_len(),
            store.symbol_store().symbol_table_len(),
        ],
        nodes: parsed
            .arena
            .iter()
            .map(|(node, _)| {
                let node = reference(parsed, node);
                (
                    node,
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect(),
        symbols: store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| {
                (
                    symbol,
                    store.declared_type_links(symbol).cloned(),
                    store.value_symbol_links(symbol).cloned(),
                )
            })
            .collect(),
        source: store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        diagnostics: context.diagnostics().clone(),
    }
}

fn assert_replay(context: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) {
    let warm = publication(context, parsed);
    for _ in 0..2 {
        context.check_source_file(FILE).unwrap();
        assert_eq!(publication(context, parsed), warm);
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(publication(context, parsed), warm);
    }
}

#[test]
fn nested_method_annotations_keep_instance_static_and_query_identities() {
    let source = concat!(
        "class Receiver {\n",
        "  read(source: { value: { value: number } }): number { return source.value.value; }\n",
        "  static readStatic(source: { value: { value: number } }): number { return source.value.value; }\n",
        "}\n",
        "declare const input: { value: { value: number } };\n",
        "const receiver = new Receiver();\n",
        "const first: number = receiver.read(input);\n",
        "const second: number = Receiver.readStatic(input);\n",
    );
    for query_first in [false, true] {
        let parsed = parse_source_file(source);
        let methods = [method(&parsed, "read"), method(&parsed, "readStatic")];
        let mut context = context(&parsed);
        let queried = query_first.then(|| {
            methods
                .each_ref()
                .map(|method| context.get_type_from_type_node(method.annotation).unwrap())
        });
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let identities = methods
            .each_ref()
            .map(|method| assert_method(&mut context, &parsed, method, number));
        assert_ne!(identities[0].0, identities[1].0);
        assert_ne!(identities[0].1, identities[1].1);
        if let Some(queried) = queried {
            assert_eq!(identities.map(|(_, parameter)| parameter), queried);
        }
        let class = symbol(&context, methods[0].class);
        let instance_method = symbol(&context, methods[0].declaration);
        let static_method = symbol(&context, methods[1].declaration);
        let members = context.get_nongeneric_class_members(class).unwrap();
        assert_eq!(members.instance_properties(), &[instance_method]);
        assert_eq!(members.static_properties(), &[static_method]);
        let calls = nodes(&parsed, SyntaxKind::CallExpression);
        assert_eq!(calls.len(), 2);
        for (call, (expected, _)) in calls.into_iter().zip(identities) {
            assert_eq!(signature(&context, call), expected);
            assert_eq!(context.get_type_at_location(call).unwrap(), number);
        }
        assert_replay(&mut context, &parsed);
    }
}

#[test]
fn method_object_annotations_keep_exact_argument_and_body_errors() {
    let source = concat!(
        "class Receiver {\n",
        "  read(source: { value: { value: number } }): number { return source.value.value; }\n",
        "  wrong(source: { value: { value: number } }): string { return source.value.value; }\n",
        "}\n",
        "declare const text: string;\n",
        "const receiver = new Receiver();\n",
        "receiver.read(text);\n",
    );
    for query_first in [false, true] {
        let parsed = parse_source_file(source);
        let read = method(&parsed, "read");
        let wrong = method(&parsed, "wrong");
        let [call]: [NodeRef; 1] = nodes(&parsed, SyntaxKind::CallExpression)
            .try_into()
            .unwrap();
        let NodeData::CallExpression(invocation) = &parsed.arena.get(call.node).unwrap().data
        else {
            unreachable!()
        };
        let [argument] = invocation.arguments.nodes.as_slice() else {
            panic!("the wrong argument must keep its written identifier")
        };
        let argument = reference(&parsed, *argument);
        let mut context = context(&parsed);
        if query_first {
            for method in [&read, &wrong] {
                context.get_type_from_type_node(method.annotation).unwrap();
            }
        }
        context.check_source_file(FILE).unwrap();
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        assert_eq!(diagnostics[0].diagnostic.code(), 2322);
        assert_eq!(diagnostics[0].node, Some(returned(&parsed, &wrong).0));
        assert_eq!(
            diagnostics[0].diagnostic.render().unwrap(),
            "Type 'number' is not assignable to type 'string'."
        );
        assert_eq!(diagnostics[1].diagnostic.code(), 2345);
        assert_eq!(diagnostics[1].node, Some(argument));
        assert_eq!(
            diagnostics[1].diagnostic.render().unwrap(),
            "Argument of type 'string' is not assignable to parameter of type '{ value: { value: number; }; }'."
        );
        for diagnostic in diagnostics {
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.related_information.is_empty());
            assert!(diagnostic.diagnostic.details.is_empty());
        }
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let read_identity = assert_method(&mut context, &parsed, &read, number);
        let wrong_identity = assert_method(&mut context, &parsed, &wrong, string);
        assert_ne!(read_identity.0, wrong_identity.0);
        assert_eq!(signature(&context, call), read_identity.0);
        assert_eq!(context.get_type_at_location(call).unwrap(), number);
        assert_eq!(context.get_type_at_location(argument).unwrap(), string);
        assert_replay(&mut context, &parsed);
    }
}

fn assert_generic_annotation_property(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    method: &Method,
    formal: TypeId,
) -> TypeId {
    let NodeData::TypeLiteralNode(literal) =
        &parsed.arena.get(method.annotation.node).unwrap().data
    else {
        panic!("the original parameter must keep its inline type literal")
    };
    let [property] = literal.members.nodes.as_slice() else {
        panic!("the original parameter must keep its one property")
    };
    let NodeData::PropertyDeclaration(data) = &parsed.arena.get(*property).unwrap().data else {
        panic!("the property must keep its source declaration")
    };
    let declaration = reference(parsed, *property);
    let annotation = reference(parsed, data.type_.unwrap());
    let name = reference(parsed, data.name);
    let owner = symbol(context, method.annotation);
    let property = symbol(context, declaration);
    let type_ = context.get_type_from_type_node(method.annotation).unwrap();
    assert_eq!(context.get_type_from_type_node(annotation), Ok(formal));
    assert_eq!(context.get_type_at_location(name), Ok(formal));
    assert_eq!(
        context.get_symbol_at_location(name).unwrap(),
        Some(property)
    );
    assert_eq!(
        context.get_type_at_location(method.parameter_name),
        Ok(type_)
    );
    let store = context.store();
    let record = store.type_payload(type_).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("the inline annotation must keep its actual object type")
    };
    assert_eq!(
        object.structured.properties.as_deref(),
        Some(&[property][..])
    );
    let member = store.symbol(property).unwrap();
    assert_eq!(member.flags(), SymbolFlags::PROPERTY);
    assert_eq!(member.parent(), Some(owner));
    assert_eq!(member.declarations(), Some(&[declaration][..]));
    assert_eq!(member.value_declaration(), Some(declaration));
    assert_eq!(
        store.value_symbol_links(property),
        Some(&ValueSymbolLinks {
            resolved_type: Some(formal),
            ..ValueSymbolLinks::default()
        })
    );
    type_
}

fn assert_generic_annotation_signature(
    context: &mut CanonicalCheckerContext<'_>,
    method: &Method,
    formal: TypeId,
    parameter_type: TypeId,
    returned: TypeId,
) -> (TypeId, SignatureId) {
    let owner = symbol(context, method.declaration);
    let class = symbol(context, method.class);
    let parameter = symbol(context, method.parameter);
    let callable = context.get_type_at_location(method.name).unwrap();
    assert_eq!(
        context.get_type_at_location(method.declaration),
        Ok(callable)
    );
    let signature = signature(context, method.declaration);
    assert_eq!(
        context.get_return_type_of_signature(signature),
        Ok(returned)
    );
    let store = context.store();
    let member = store.symbol(owner).unwrap();
    assert_eq!(member.flags(), SymbolFlags::METHOD);
    assert_eq!(member.parent(), Some(class));
    assert_eq!(member.declarations(), Some(&[method.declaration][..]));
    assert_eq!(member.value_declaration(), Some(method.declaration));
    let record = store.signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(method.declaration));
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert_eq!(record.type_parameters(), [formal]);
    assert_eq!(record.parameters(), [parameter]);
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(record.resolved_return_type(), Some(returned));
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.this_parameter(), None);
    assert_eq!(
        store.value_symbol_links(parameter),
        Some(&ValueSymbolLinks {
            resolved_type: Some(parameter_type),
            ..ValueSymbolLinks::default()
        })
    );
    let record = store.type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("the method must keep its own callable type")
    };
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    (callable, signature)
}

fn assert_generic_annotation_formal(
    context: &mut CanonicalCheckerContext<'_>,
    formal_node: NodeRef,
) -> TypeId {
    let formal_symbol = symbol(context, formal_node);
    let formal = context.get_declared_type_of_symbol(formal_symbol).unwrap();
    let store = context.store();
    assert_eq!(
        store.symbol(formal_symbol).unwrap().flags(),
        SymbolFlags::TYPE_PARAMETER
    );
    assert_eq!(
        store.symbol(formal_symbol).unwrap().declarations(),
        Some(&[formal_node][..])
    );
    let record = store.type_payload(formal).unwrap();
    assert_eq!(record.symbol(), Some(formal_symbol));
    let TypeData::TypeParameter(data) = record.data() else {
        panic!("the inline member must use the method's real T")
    };
    assert!(!data.is_this_type);
    assert_eq!(data.target, None);
    assert_eq!(data.mapper, None);
    assert_eq!(data.constraint, None);
    assert_eq!(data.resolved_default_type, None);
    formal
}

fn assert_supported_generic_annotation_row(parsed: &ParseResult, method: &Method) {
    let NodeData::ClassDeclaration(class) = &parsed.arena.get(method.class.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(class.type_parameters.is_none());
    let NodeData::MethodDeclaration(data) =
        &parsed.arena.get(method.declaration.node).unwrap().data
    else {
        unreachable!()
    };
    let [formal] = data.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("the original method must keep its one formal")
    };
    let formal_node = reference(parsed, *formal);
    assert_eq!(
        parsed.arena.get(*formal).unwrap().parent,
        Some(method.declaration.node)
    );
    let return_annotation = reference(parsed, data.type_.unwrap());
    assert_eq!(
        parsed.arena.get(return_annotation.node).unwrap().kind,
        SyntaxKind::VoidKeyword
    );
    let NodeData::Block(body) = &parsed.arena.get(data.body.unwrap()).unwrap().data else {
        unreachable!()
    };
    assert!(body.statements.nodes.is_empty());
    for query_first in [false, true] {
        let mut context = context(parsed);
        let formal_symbol = symbol(&context, formal_node);
        assert!(context.store().declared_type_links(formal_symbol).is_none());
        assert!(
            context
                .store()
                .signature_links(method.declaration)
                .is_none()
        );
        let early =
            query_first.then(|| context.get_type_from_type_node(method.annotation).unwrap());
        context.check_source_file(FILE).unwrap();
        assert!(context.diagnostics().is_empty());
        assert!(
            context
                .store()
                .source_file_links(context.source_file(FILE).unwrap())
                .unwrap()
                .type_checked
        );
        let formal = assert_generic_annotation_formal(&mut context, formal_node);
        let returned = context.store().intrinsic_bootstrap().unwrap().void_type;
        assert_eq!(
            context.get_type_from_type_node(return_annotation),
            Ok(returned)
        );
        let parameter = assert_generic_annotation_property(&mut context, parsed, method, formal);
        if let Some(early) = early {
            assert_eq!(parameter, early);
        }
        let identity =
            assert_generic_annotation_signature(&mut context, method, formal, parameter, returned);
        let warm = publication(&context, parsed);
        assert_replay(&mut context, parsed);
        for _ in 0..2 {
            assert_eq!(
                assert_generic_annotation_formal(&mut context, formal_node),
                formal
            );
            assert_eq!(
                context.get_type_from_type_node(return_annotation),
                Ok(returned)
            );
            assert_eq!(
                assert_generic_annotation_property(&mut context, parsed, method, formal),
                parameter
            );
            assert_eq!(
                assert_generic_annotation_signature(
                    &mut context,
                    method,
                    formal,
                    parameter,
                    returned
                ),
                identity
            );
            assert_eq!(publication(&context, parsed), warm);
        }
    }
}

#[test]
fn method_object_annotations_keep_generic_identities_and_optional_rest_boundaries() {
    for (index, source) in [
        "class Receiver { read<T>(source: { value: T }): void {} }",
        "class Receiver { read(source?: { value: number }): void {} }",
        "class Receiver { read(...source: { value: number }[]): void {} }",
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        let method = method(&parsed, "read");
        if index == 0 {
            assert_supported_generic_annotation_row(&parsed, &method);
            continue;
        }
        let mut context = context(&parsed);
        let owner = symbol(&context, method.class);
        let cold = publication(&context, &parsed);
        let expected =
            SourceCheckError::Unsupported(UnsupportedSourceSyntax::Class(method.declaration));
        for _ in 0..2 {
            assert_eq!(context.check_source_file(FILE), Err(expected), "{source}");
            assert_eq!(publication(&context, &parsed), cold);
            assert_eq!(context.recheck_source_file(FILE), Err(expected), "{source}");
            assert_eq!(publication(&context, &parsed), cold);
            assert!(context.store().declared_type_links(owner).is_none());
            assert!(context.store().value_symbol_links(owner).is_none());
            assert!(context.diagnostics().is_empty());
        }
    }
}
