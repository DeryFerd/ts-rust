use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(203_276);

// These controls cover optional named method parameters, not the full WSContext class.
fn context(parsed: &ParseResult, exact: bool) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/optional-named-method-parameters.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::External,
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
                exact_optional_property_types: exact,
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

fn signature(context: &CanonicalCheckerContext<'_>, location: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(location)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the method or call must retain its signature")
}

struct Parameter {
    declaration: NodeRef,
    name: NodeRef,
    annotation: NodeRef,
}

struct Method {
    class: NodeRef,
    declaration: NodeRef,
    name: NodeRef,
    parameters: [Parameter; 2],
    return_annotation: NodeRef,
}

fn methods(parsed: &ParseResult) -> Vec<Method> {
    nodes(parsed, SyntaxKind::MethodDeclaration)
        .into_iter()
        .map(|declaration| {
            let record = parsed.arena.get(declaration.node).unwrap();
            let NodeData::MethodDeclaration(data) = &record.data else {
                unreachable!()
            };
            assert!(data.type_parameters.is_none());
            let [required, optional] = data.parameters.nodes.as_slice() else {
                panic!("the method must keep its two written parameters")
            };
            let parameters = [*required, *optional].map(|id| {
                let record = parsed.arena.get(id).unwrap();
                let NodeData::ParameterDeclaration(parameter) = &record.data else {
                    panic!("expected the written parameter")
                };
                assert_eq!(record.parent, Some(declaration.node));
                assert!(parameter.initializer.is_none());
                assert!(parameter.dot_dot_dot_token.is_none());
                assert_eq!(parameter.question_token.is_some(), id == *optional);
                if let Some(question) = parameter.question_token {
                    let token = parsed.arena.get(question).unwrap();
                    assert_eq!(token.kind, SyntaxKind::QuestionToken);
                    assert_eq!(token.parent, Some(id));
                    assert!(matches!(token.data, NodeData::Token(_)));
                }
                Parameter {
                    declaration: node(parsed, id),
                    name: node(parsed, parameter.name),
                    annotation: node(parsed, parameter.type_.unwrap()),
                }
            });
            assert_eq!(
                parsed.arena.get(parameters[1].annotation.node).unwrap().kind,
                SyntaxKind::TypeReference
            );
            Method {
                class: node(parsed, record.parent.unwrap()),
                declaration,
                name: node(parsed, data.name),
                parameters,
                return_annotation: node(parsed, data.type_.unwrap()),
            }
        })
        .collect()
}

fn prepare<'a>(
    parsed: &'a ParseResult,
    methods: &[Method],
    exact: bool,
    query_first: bool,
) -> CanonicalCheckerContext<'a> {
    let mut context = context(parsed, exact);
    let early = query_first.then(|| {
        methods
            .iter()
            .map(|method| {
                context
                    .get_type_from_type_node(method.parameters[1].annotation)
                    .unwrap()
            })
            .collect::<Vec<_>>()
    });
    context.check_source_file(FILE).unwrap();
    if let Some(early) = early {
        for (method, expected) in methods.iter().zip(early) {
            assert_eq!(
                context.get_type_from_type_node(method.parameters[1].annotation),
                Ok(expected)
            );
        }
    }
    context
}

fn assert_formal(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    class: NodeRef,
) -> TypeId {
    let NodeData::ClassDeclaration(data) = &parsed.arena.get(class.node).unwrap().data else {
        panic!("the method owner must be the written class")
    };
    let [formal] = data.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("the class must keep its one written type parameter")
    };
    let declaration = node(parsed, *formal);
    let owner = symbol(context, class);
    let parameter = symbol(context, declaration);
    let type_ = context.get_declared_type_of_symbol(parameter).unwrap();
    let instance = context.get_declared_type_of_symbol(owner).unwrap();
    let store = context.store();
    let record = store.symbol(parameter).unwrap();
    assert_eq!(record.flags(), SymbolFlags::TYPE_PARAMETER);
    assert_eq!(record.parent(), Some(owner));
    assert_eq!(record.declarations(), Some(&[declaration][..]));
    assert_eq!(store.type_payload(type_).unwrap().symbol(), Some(parameter));
    let TypeData::TypeParameter(formal) = store.type_payload(type_).unwrap().data() else {
        panic!("the class formal must not be erased")
    };
    assert_eq!(formal.target, None);
    assert_eq!(formal.mapper, None);
    assert_eq!(
        formal.resolved_default_type,
        Some(store.intrinsic_bootstrap().unwrap().unknown_type)
    );
    let TypeData::Interface(class) = store.type_payload(instance).unwrap().data() else {
        panic!("the generic class must retain its own instance type")
    };
    assert_eq!(class.reference.object.target, Some(instance));
    assert_eq!(
        class.reference.resolved_type_arguments.as_deref(),
        Some(&[type_][..])
    );
    type_
}

fn assert_method(context: &mut CanonicalCheckerContext<'_>, method: &Method) -> TypeId {
    let owner = symbol(context, method.declaration);
    let class = symbol(context, method.class);
    let callable = context.get_type_at_location(method.name).unwrap();
    assert_eq!(context.get_type_at_location(method.declaration), Ok(callable));
    assert_eq!(
        context.get_symbol_at_location(method.name).unwrap(),
        Some(owner)
    );
    let parameters = method.parameters.each_ref().map(|parameter| {
        let annotation = context
            .get_type_from_type_node(parameter.annotation)
            .unwrap();
        let value = context.get_type_at_location(parameter.name).unwrap();
        let symbol = symbol(context, parameter.declaration);
        assert_eq!(
            context
                .store()
                .type_node_links(parameter.annotation)
                .unwrap()
                .resolved_type,
            Some(annotation)
        );
        let record = context.store().symbol(symbol).unwrap();
        assert_eq!(record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
        assert_eq!(record.declarations(), Some(&[parameter.declaration][..]));
        assert_eq!(record.value_declaration(), Some(parameter.declaration));
        assert_eq!(record.parent(), None);
        let links = context.store().value_symbol_links(symbol).unwrap();
        assert_eq!(links.resolved_type, Some(value));
        assert_eq!(links.target, None);
        assert_eq!(links.mapper, None);
        (symbol, annotation, value)
    });
    assert_eq!(parameters[0].1, parameters[0].2);
    assert_ne!(parameters[1].1, parameters[1].2);
    let store = context.store();
    let TypeData::Union(optional) = store.type_payload(parameters[1].2).unwrap().data() else {
        panic!("the optional parameter value must include undefined")
    };
    let mut expected = [
        parameters[1].1,
        store.intrinsic_bootstrap().unwrap().undefined_type,
    ];
    expected.sort_unstable();
    assert_eq!(optional.union.types, expected);
    let returned = context
        .get_type_from_type_node(method.return_annotation)
        .unwrap();
    let declared = signature(context, method.declaration);
    assert_eq!(context.get_return_type_of_signature(declared), Ok(returned));
    let store = context.store();
    let record = store.signature(declared).unwrap();
    assert_eq!(record.declaration(), Some(method.declaration));
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert_eq!(record.parameters(), parameters.map(|parameter| parameter.0));
    assert_eq!(record.min_argument_count(), 1);
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    let member = store.symbol(owner).unwrap();
    assert_eq!(member.flags(), SymbolFlags::METHOD);
    assert_eq!(member.parent(), Some(class));
    assert_eq!(member.declarations(), Some(&[method.declaration][..]));
    let payload = store.type_payload(callable).unwrap();
    assert_eq!(payload.symbol(), Some(owner));
    let TypeData::Object(object) = payload.data() else {
        panic!("the method must retain its real callable object")
    };
    assert_eq!(object.structured.signatures.as_deref(), Some(&[declared][..]));
    assert_eq!(object.structured.call_signature_count, 1);
    parameters[1].1
}

fn callee(parsed: &ParseResult, call: NodeRef) -> NodeRef {
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected the actual call")
    };
    node(parsed, data.expression)
}

fn argument(parsed: &ParseResult, call: NodeRef, index: usize) -> NodeRef {
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected the actual call")
    };
    node(parsed, data.arguments.nodes[index])
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    methods: &[Method],
) {
    let mut annotations = Vec::new();
    let mut locations = Vec::new();
    let mut signatures = Vec::new();
    for method in methods {
        locations.extend([method.declaration, method.name]);
        signatures.push(method.declaration);
        annotations.push(method.return_annotation);
        for parameter in &method.parameters {
            annotations.push(parameter.annotation);
            locations.push(parameter.name);
        }
    }
    for call in nodes(parsed, SyntaxKind::CallExpression) {
        locations.extend([callee(parsed, call), call]);
        signatures.push(call);
    }
    let annotations = annotations
        .into_iter()
        .map(|node| (node, context.get_type_from_type_node(node).unwrap()))
        .collect::<Vec<_>>();
    let locations = locations
        .into_iter()
        .map(|node| (node, context.get_type_at_location(node).unwrap()))
        .collect::<Vec<_>>();
    let signatures = signatures
        .into_iter()
        .map(|node| {
            let signature = signature(context, node);
            (
                node,
                signature,
                context.get_return_type_of_signature(signature).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    let warm = format!("{:?}\n{:?}", context.store(), context.diagnostics());
    for recheck in [false, true, true] {
        if recheck {
            context.recheck_source_file(FILE).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        for &(node, expected) in &annotations {
            assert_eq!(context.get_type_from_type_node(node), Ok(expected));
        }
        for &(node, expected) in &locations {
            assert_eq!(context.get_type_at_location(node), Ok(expected));
        }
        for &(node, expected, returned) in &signatures {
            assert_eq!(signature(context, node), expected);
            assert_eq!(context.get_return_type_of_signature(expected), Ok(returned));
        }
        assert_eq!(
            format!("{:?}\n{:?}", context.store(), context.diagnostics()),
            warm
        );
    }
}

#[test]
fn optional_named_method_parameters_keep_types_owners_and_omitted_calls() {
    let parsed = parse_source_file(concat!(
        "export interface SendOptions { compress?: boolean; }\n",
        "export class Sender<T = unknown> {\n",
        "  send(source: T, options?: SendOptions): T { return source; }\n",
        "}\n",
        "declare const sender: Sender<string>;\n",
        "declare const options: SendOptions;\n",
        "const omitted: string = sender.send('one');\n",
        "const supplied: string = sender.send('two', options);\n",
        "const explicitUndefined: string = sender.send('three', undefined);\n",
    ));
    let methods = methods(&parsed);
    let [method] = methods.as_slice() else {
        panic!("expected one method")
    };
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 3);
    for exact in [false, true] {
        for query_first in [false, true] {
            let mut context = prepare(&parsed, &methods, exact, query_first);
            assert!(
                context.diagnostics().is_empty(),
                "{:?}",
                context.diagnostics()
            );
            let formal = assert_formal(&mut context, &parsed, method.class);
            assert_eq!(
                context.get_type_at_location(method.parameters[0].name),
                Ok(formal)
            );
            let annotation = assert_method(&mut context, method);
            let owner = symbol(&context, nodes(&parsed, SyntaxKind::InterfaceDeclaration)[0]);
            assert_eq!(context.get_declared_type_of_symbol(owner), Ok(annotation));
            assert_eq!(
                context.store().type_payload(annotation).unwrap().symbol(),
                Some(owner)
            );
            assert!(matches!(
                context.store().type_payload(annotation).unwrap().data(),
                TypeData::Interface(_)
            ));
            let string = context.store().intrinsic_bootstrap().unwrap().string_type;
            for &call in &calls {
                assert_eq!(context.get_type_at_location(call), Ok(string));
                let selected = signature(&context, call);
                let record = context.store().signature(selected).unwrap();
                assert_eq!(record.declaration(), Some(method.declaration));
                assert_eq!(record.parameters().len(), 2);
                assert_eq!(record.min_argument_count(), 1);
            }
            assert_replay(&mut context, &parsed, &methods);
        }
    }
}

#[test]
fn optional_named_method_parameters_preserve_body_and_call_diagnostics() {
    let parsed = parse_source_file(concat!(
        "interface SendOptions { compress?: boolean; }\n",
        "export class Sender {\n",
        "  send(source: string, options?: SendOptions): number { return source; }\n",
        "}\n",
        "declare const sender: Sender;\n",
        "sender.send(1);\n",
        "sender.send('null', null);\n",
        "sender.send();\n",
    ));
    let methods = methods(&parsed);
    let [method] = methods.as_slice() else {
        panic!("expected one method")
    };
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 3);
    for query_first in [false, true] {
        let mut context = prepare(&parsed, &methods, false, query_first);
        assert_method(&mut context, method);
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 4, "{diagnostics:?}");
        for (diagnostic, code, location, message) in [
            (
                &diagnostics[0],
                2322,
                nodes(&parsed, SyntaxKind::ReturnStatement)[0],
                "Type 'string' is not assignable to type 'number'.",
            ),
            (
                &diagnostics[1],
                2345,
                argument(&parsed, calls[0], 0),
                "Argument of type 'number' is not assignable to parameter of type 'string'.",
            ),
            (
                &diagnostics[2],
                2345,
                argument(&parsed, calls[1], 1),
                "Argument of type 'null' is not assignable to parameter of type 'SendOptions | undefined'.",
            ),
        ] {
            assert_eq!(diagnostic.diagnostic.code(), code);
            assert_eq!(diagnostic.node, Some(location));
            assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
            assert_eq!(diagnostic.range_override, None);
            assert!(diagnostic.related_information.is_empty());
            assert!(diagnostic.diagnostic.details.is_empty());
        }
        let missing = &diagnostics[3];
        assert_eq!(missing.diagnostic.code(), 2554);
        assert_eq!(missing.node, Some(callee(&parsed, calls[2])));
        assert_eq!(missing.range_override, None);
        assert_eq!(
            missing.diagnostic.render().unwrap(),
            "Expected 1-2 arguments, but got 0."
        );
        let [related] = missing.related_information.as_slice() else {
            panic!("the missing argument must point to the real required parameter")
        };
        assert_eq!(related.diagnostic.code(), 6210);
        assert_eq!(related.node, Some(method.parameters[0].declaration));
        assert_eq!(
            related.diagnostic.render().unwrap(),
            "An argument for 'source' was not provided."
        );
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        for &call in &calls {
            assert_eq!(context.get_type_at_location(call), Ok(number));
            let selected = signature(&context, call);
            assert_eq!(
                context.store().signature(selected).unwrap().declaration(),
                Some(method.declaration)
            );
        }
        assert_replay(&mut context, &parsed, &methods);
    }
}

#[test]
fn optional_named_method_annotations_keep_distinct_class_type_arguments() {
    let parsed = parse_source_file(concat!(
        "interface Packet<T> { value: T; }\n",
        "export class First<T = unknown> {\n",
        "  send(source: T, options?: Packet<T>): T { return source; }\n",
        "}\n",
        "export class Second<T = unknown> {\n",
        "  send(source: T, options?: Packet<T>): T { return source; }\n",
        "}\n",
        "declare const first: First<string>;\n",
        "declare const second: Second<number>;\n",
        "declare const text: Packet<string>;\n",
        "declare const count: Packet<number>;\n",
        "const stringResult: string = first.send('one', text);\n",
        "const numberResult: number = second.send(1, count);\n",
    ));
    let methods = methods(&parsed);
    assert_eq!(methods.len(), 2);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 2);
    for query_first in [false, true] {
        let mut context = prepare(&parsed, &methods, false, query_first);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let packet = symbol(&context, nodes(&parsed, SyntaxKind::InterfaceDeclaration)[0]);
        let target = context.get_declared_type_of_symbol(packet).unwrap();
        let mut formals = Vec::new();
        let mut annotations = Vec::new();
        for method in &methods {
            let formal = assert_formal(&mut context, &parsed, method.class);
            assert_eq!(
                context.get_type_at_location(method.parameters[0].name),
                Ok(formal)
            );
            let annotation = assert_method(&mut context, method);
            let TypeData::TypeReference(reference) =
                context.store().type_payload(annotation).unwrap().data()
            else {
                panic!("the optional annotation must keep its applied Packet reference")
            };
            assert_eq!(reference.object.target, Some(target));
            assert_eq!(
                reference.resolved_type_arguments.as_deref(),
                Some(&[formal][..])
            );
            formals.push(formal);
            annotations.push(annotation);
        }
        assert_ne!(formals[0], formals[1]);
        assert_ne!(annotations[0], annotations[1]);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let expected = [bootstrap.string_type, bootstrap.number_type];
        for ((&call, method), returned) in calls.iter().zip(&methods).zip(expected) {
            assert_eq!(context.get_type_at_location(call), Ok(returned));
            let selected = signature(&context, call);
            let record = context.store().signature(selected).unwrap();
            assert_eq!(record.declaration(), Some(method.declaration));
            assert_eq!(record.min_argument_count(), 1);
        }
        assert_replay(&mut context, &parsed, &methods);
    }
}
