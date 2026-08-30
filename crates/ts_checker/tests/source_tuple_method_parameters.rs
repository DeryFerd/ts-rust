use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerDiagnosticRange, CanonicalCheckerOptions,
    IntrinsicBootstrapOptions, SignatureId, SourceCheckError, TypeData, TypeId,
    UnsupportedSourceSyntax,
    signatures::{ElementFlags, SignatureFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(0);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/tuple-method-parameters.ts\""),
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

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize, usize) {
    let store = context.store();
    (
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.symbol_store().symbol_table_len(),
    )
}

struct MethodParts {
    declaration: NodeRef,
    name: NodeRef,
    parameter: NodeRef,
    parameter_name: NodeRef,
    annotation: NodeRef,
}

fn method(parsed: &ParseResult, expected: &str) -> MethodParts {
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
                panic!("the method has one tuple parameter")
            };
            let parameter_node = *parameter;
            let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(parameter_node)?.data
            else {
                panic!("the method parameter keeps its declaration")
            };
            let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
            Some(MethodParts {
                declaration: node_ref(node),
                name: node_ref(method.name),
                parameter: node_ref(parameter_node),
                parameter_name: node_ref(parameter.name),
                annotation: node_ref(parameter.type_?),
            })
        })
        .unwrap_or_else(|| panic!("missing method {expected}"))
}

fn tuple_parameter(
    context: &mut CanonicalCheckerContext<'_>,
    method: &MethodParts,
) -> (SignatureId, TypeId) {
    let owner = symbol(context, method.declaration);
    let parameter = symbol(context, method.parameter);
    let signature = context
        .store()
        .signature_links(method.declaration)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the method publishes its declared signature");
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(method.declaration));
    assert_eq!(record.flags(), SignatureFlags::NONE);
    assert_eq!(record.parameters(), &[parameter]);
    assert_eq!(record.min_argument_count(), 1);
    assert!(record.type_parameters().is_empty());
    let callable = context
        .store()
        .value_symbol_links(owner)
        .unwrap()
        .resolved_type
        .unwrap();
    let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data() else {
        panic!("the method has a callable object")
    };
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    assert_eq!(object.structured.call_signature_count, 1);
    let tuple_type = context
        .store()
        .value_symbol_links(parameter)
        .unwrap()
        .resolved_type
        .unwrap();
    let TypeData::TypeReference(reference) =
        context.store().type_payload(tuple_type).unwrap().data()
    else {
        panic!("the parameter must retain a tuple reference")
    };
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[bootstrap.number_type, bootstrap.string_type][..]),
    );
    let target = reference.object.target.unwrap();
    let TypeData::Tuple(tuple) = context.store().type_payload(target).unwrap().data() else {
        panic!("the reference must target a tuple, not an array")
    };
    assert_eq!(tuple.metadata.element_flags(), [ElementFlags::REQUIRED; 2]);
    assert_eq!(tuple.metadata.min_length(), 2);
    assert_eq!(tuple.metadata.fixed_length(), 2);
    assert!(!tuple.metadata.is_readonly());
    assert_eq!(
        context.get_type_from_type_node(method.annotation).unwrap(),
        tuple_type,
    );
    assert_eq!(
        context.get_type_at_location(method.annotation).unwrap(),
        tuple_type
    );
    assert_eq!(
        context.get_type_at_location(method.parameter_name).unwrap(),
        tuple_type
    );
    assert_eq!(
        context
            .get_symbol_at_location(method.parameter_name)
            .unwrap(),
        Some(parameter)
    );
    assert_eq!(
        context.get_symbol_at_location(method.name).unwrap(),
        Some(owner)
    );
    (signature, tuple_type)
}

#[test]
fn tuple_method_parameters_keep_canonical_types_across_source_and_query_replay() {
    let source = concat!(
        "class Receiver { take(pair: [number, string]): void {} }\n",
        "declare const pair: [number, string];\n",
        "const receiver = new Receiver();\n",
        "receiver.take(pair);\n",
    );
    for query_first in [false, true] {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let method = method(&parsed, "take");
        let calls = nodes(&parsed, SyntaxKind::CallExpression);
        let [call] = calls.as_slice() else {
            panic!("the source has one method call")
        };
        let mut context = context(&parsed);
        let queried =
            query_first.then(|| context.get_type_from_type_node(method.annotation).unwrap());
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let identities = tuple_parameter(&mut context, &method);
        if let Some(queried) = queried {
            assert_eq!(identities.1, queried);
        }
        let void_type = context.store().intrinsic_bootstrap().unwrap().void_type;
        assert_eq!(context.get_type_at_location(*call).unwrap(), void_type);
        assert_eq!(
            context
                .store()
                .signature_links(*call)
                .unwrap()
                .resolved_signature
                .signature(),
            Some(identities.0),
        );
        let warm = (counts(&context), context.diagnostics().clone());
        context.check_source_file(FILE).unwrap();
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(tuple_parameter(&mut context, &method), identities);
        assert_eq!(context.get_type_at_location(*call).unwrap(), void_type);
        assert_eq!((counts(&context), context.diagnostics().clone()), warm);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // The source checks tuple reads and both arity errors together.
fn tuple_method_reads_and_calls_report_exact_element_and_arity_errors() {
    let parsed = parse_source_file(concat!(
        "class Receiver {\n",
        "  first(pair: [number, string]): number { return pair[0]; }\n",
        "  wrong(pair: [number, string]): number { return pair[1]; }\n",
        "}\n",
        "declare const pair: [number, string];\n",
        "const receiver = new Receiver();\n",
        "const result: number = receiver.first(pair);\n",
        "receiver.first();\n",
        "receiver.first(pair, pair);\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let first = method(&parsed, "first");
    let wrong = method(&parsed, "wrong");
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    let elements = nodes(&parsed, SyntaxKind::ElementAccessExpression);
    let returns = nodes(&parsed, SyntaxKind::ReturnStatement);
    assert_eq!(calls.len(), 3);
    assert_eq!(elements.len(), 2);
    assert_eq!(returns.len(), 2);
    let NodeData::CallExpression(missing) = &parsed.arena.get(calls[1].node).unwrap().data else {
        panic!("expected the missing-argument call")
    };
    let NodeData::PropertyAccessExpression(access) =
        &parsed.arena.get(missing.expression).unwrap().data
    else {
        panic!("the call keeps its method receiver")
    };
    let missing_name = NodeRef::new(parsed.arena.id(), FILE, access.name);
    let NodeData::CallExpression(extra) = &parsed.arena.get(calls[2].node).unwrap().data else {
        panic!("expected the extra-argument call")
    };
    let extra_argument = parsed.arena.get(extra.arguments.nodes[1]).unwrap().range;
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 3, "{diagnostics:?}");
    assert_eq!(diagnostics[0].diagnostic.code(), 2322);
    assert_eq!(diagnostics[0].node, Some(returns[1]));
    assert_eq!(diagnostics[0].range_override, None);
    assert_eq!(
        diagnostics[0].diagnostic.render().unwrap(),
        "Type 'string' is not assignable to type 'number'."
    );
    assert!(diagnostics[0].related_information.is_empty());
    assert_eq!(diagnostics[1].diagnostic.code(), 2554);
    assert_eq!(diagnostics[1].node, Some(missing_name));
    assert_eq!(diagnostics[1].range_override, None);
    assert_eq!(
        diagnostics[1].diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 0."
    );
    let [related] = diagnostics[1].related_information.as_slice() else {
        panic!("the missing argument must point to its tuple parameter")
    };
    assert_eq!(related.diagnostic.code(), 6210);
    assert_eq!(related.node, Some(first.parameter));
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument for 'pair' was not provided."
    );
    assert_eq!(diagnostics[2].diagnostic.code(), 2554);
    assert_eq!(diagnostics[2].node, Some(calls[2]));
    assert_eq!(
        diagnostics[2].range_override,
        Some(CanonicalCheckerDiagnosticRange::new(
            calls[2],
            extra_argument
        ))
    );
    assert_eq!(
        diagnostics[2].diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 2."
    );
    assert!(diagnostics[2].related_information.is_empty());

    let first_identities = tuple_parameter(&mut context, &first);
    let wrong_identities = tuple_parameter(&mut context, &wrong);
    assert_eq!(first_identities.1, wrong_identities.1);
    assert_ne!(first_identities.0, wrong_identities.0);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let string = bootstrap.string_type;
    for (element, expected) in [(elements[0], number), (elements[1], string)] {
        assert_eq!(context.get_type_at_location(element).unwrap(), expected);
    }
    for call in &calls {
        assert_eq!(context.get_type_at_location(*call).unwrap(), number);
        assert_eq!(
            context
                .store()
                .signature_links(*call)
                .unwrap()
                .resolved_signature
                .signature(),
            Some(first_identities.0),
        );
    }
    let warm = (counts(&context), context.diagnostics().clone());
    context.check_source_file(FILE).unwrap();
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(tuple_parameter(&mut context, &first), first_identities);
    assert_eq!(tuple_parameter(&mut context, &wrong), wrong_identities);
    for (element, expected) in [(elements[0], number), (elements[1], string)] {
        assert_eq!(context.get_type_at_location(element).unwrap(), expected);
    }
    assert_eq!((counts(&context), context.diagnostics().clone()), warm);
}

#[test]
fn tuple_methods_compare_class_and_interface_members_without_implements() {
    let parsed = parse_source_file(concat!(
        "interface Matching { take(pair: [number, string]): void; }\n",
        "interface Different { take(pair: [string, string]): void; }\n",
        "class Receiver { take(pair: [number, string]): void {} }\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let classes = nodes(&parsed, SyntaxKind::ClassDeclaration);
    let interfaces = nodes(&parsed, SyntaxKind::InterfaceDeclaration);
    assert_eq!(classes.len(), 1);
    assert_eq!(interfaces.len(), 2);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let owner = symbol(&context, classes[0]);
    let matching = symbol(&context, interfaces[0]);
    let different = symbol(&context, interfaces[1]);
    let receiver = context.get_declared_type_of_symbol(owner).unwrap();
    let matching = context.get_declared_type_of_symbol(matching).unwrap();
    let different = context.get_declared_type_of_symbol(different).unwrap();
    assert_ne!(receiver, matching);
    assert_ne!(matching, different);
    assert!(context.is_type_assignable_to(receiver, matching).unwrap());
    assert!(context.is_type_assignable_to(matching, receiver).unwrap());
    assert!(!context.is_type_assignable_to(receiver, different).unwrap());
    assert!(!context.is_type_assignable_to(different, receiver).unwrap());

    let warm = (counts(&context), context.diagnostics().clone());
    context.check_source_file(FILE).unwrap();
    context.recheck_source_file(FILE).unwrap();
    assert_eq!(
        context.get_declared_type_of_symbol(owner).unwrap(),
        receiver
    );
    assert!(context.is_type_assignable_to(receiver, matching).unwrap());
    assert!(context.is_type_assignable_to(matching, receiver).unwrap());
    assert!(!context.is_type_assignable_to(receiver, different).unwrap());
    assert!(!context.is_type_assignable_to(different, receiver).unwrap());
    assert_eq!((counts(&context), context.diagnostics().clone()), warm);
}

#[test]
#[allow(clippy::too_many_lines)] // Keep both method ownership proofs and replay with the unchanged source.
fn tuple_method_implements_keeps_real_signatures_and_canonical_parameter() {
    let parsed = parse_source_file(concat!(
        "interface Shape { take(pair: [number, string]): void; } ",
        "class Receiver implements Shape { take(pair: [number, string]): void {} }",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let classes = nodes(&parsed, SyntaxKind::ClassDeclaration);
    let interfaces = nodes(&parsed, SyntaxKind::InterfaceDeclaration);
    let required_methods = nodes(&parsed, SyntaxKind::MethodSignature);
    let annotations = nodes(&parsed, SyntaxKind::TupleType);
    assert_eq!(classes.len(), 1);
    assert_eq!(interfaces.len(), 1);
    assert_eq!(required_methods.len(), 1);
    assert_eq!(annotations.len(), 2);
    let method = method(&parsed, "take");
    let mut context = context(&parsed);
    let owner = symbol(&context, classes[0]);
    let contract = symbol(&context, interfaces[0]);
    let member = symbol(&context, method.declaration);
    let required = symbol(&context, required_methods[0]);
    assert_ne!(member, required);
    assert!(context.store().declared_type_links(owner).is_none());
    assert!(context.store().value_symbol_links(owner).is_none());
    let cold = counts(&context);

    context.check_source_file(FILE).unwrap();

    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let identities = tuple_parameter(&mut context, &method);
    let receiver = context.get_declared_type_of_symbol(owner).unwrap();
    let shape = context.get_declared_type_of_symbol(contract).unwrap();
    assert_ne!(receiver, shape);
    for (type_, owner, member) in [(receiver, owner, member), (shape, contract, required)] {
        let record = context.store().type_payload(type_).unwrap();
        assert_eq!(record.symbol(), Some(owner));
        assert_eq!(
            record.data().structured().unwrap().properties.as_deref(),
            Some(&[member][..]),
        );
        let symbol = context.store().symbol(member).unwrap();
        assert_eq!(symbol.parent(), Some(owner));
        let members = context.store().symbol(owner).unwrap().members().unwrap();
        assert_eq!(
            context
                .store()
                .symbol_table(members)
                .unwrap()
                .get(symbol.name()),
            Some(member),
        );
    }
    let required_signature = context
        .store()
        .signature_links(required_methods[0])
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    assert_ne!(required_signature, identities.0);
    let signature = context.store().signature(required_signature).unwrap();
    assert_eq!(signature.declaration(), Some(required_methods[0]));
    assert_eq!(signature.flags(), SignatureFlags::NONE);
    assert_eq!(signature.min_argument_count(), 1);
    assert!(signature.type_parameters().is_empty());
    let NodeData::MethodSignatureDeclaration(required_method) =
        &parsed.arena.get(required_methods[0].node).unwrap().data
    else {
        panic!("the interface retains its method declaration")
    };
    let [parameter] = required_method.parameters.nodes.as_slice() else {
        panic!("the interface method keeps its one source parameter")
    };
    let parameter = NodeRef::new(parsed.arena.id(), FILE, *parameter);
    let parameter_symbol = symbol(&context, parameter);
    assert_eq!(signature.parameters(), &[parameter_symbol]);
    assert_eq!(
        context
            .store()
            .symbol(parameter_symbol)
            .unwrap()
            .declarations(),
        Some(&[parameter][..])
    );
    assert_eq!(
        context
            .store()
            .value_symbol_links(parameter_symbol)
            .unwrap()
            .resolved_type,
        Some(identities.1),
    );
    for annotation in &annotations {
        assert_eq!(
            context.get_type_from_type_node(*annotation).unwrap(),
            identities.1
        );
    }
    let void_type = context.store().intrinsic_bootstrap().unwrap().void_type;
    assert_eq!(
        context
            .get_return_type_of_signature(required_signature)
            .unwrap(),
        void_type
    );
    assert_eq!(
        context.get_return_type_of_signature(identities.0).unwrap(),
        void_type
    );
    assert!(context.is_type_assignable_to(receiver, shape).unwrap());
    assert!(counts(&context).0 > cold.0);
    assert!(counts(&context).2 > cold.2);
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        (
            counts(context),
            context.diagnostics().clone(),
            [owner, contract, member, required].map(|symbol| {
                (
                    context.store().declared_type_links(symbol).cloned(),
                    context.store().value_symbol_links(symbol).cloned(),
                )
            }),
            [method.declaration, required_methods[0]]
                .map(|node| context.store().signature_links(node).cloned()),
        )
    };
    let warm = snapshot(&context);
    for _ in 0..2 {
        context.check_source_file(FILE).unwrap();
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(
            context.get_declared_type_of_symbol(owner).unwrap(),
            receiver
        );
        assert_eq!(
            context.get_declared_type_of_symbol(contract).unwrap(),
            shape
        );
        assert_eq!(tuple_parameter(&mut context, &method), identities);
        for annotation in &annotations {
            assert_eq!(
                context.get_type_at_location(*annotation).unwrap(),
                identities.1
            );
        }
        assert_eq!(
            context
                .get_return_type_of_signature(required_signature)
                .unwrap(),
            void_type
        );
        assert!(context.is_type_assignable_to(receiver, shape).unwrap());
        assert_eq!(snapshot(&context), warm);
    }
}

#[test]
fn later_tuple_method_forms_keep_explicit_class_boundaries() {
    // Ambient overloads, tuple-union rest parameters, and generic methods remain outside this slice.
    let cases = [
        "class GenericMethod { take<T>(pair: [T, string]): void {} }",
        concat!(
            "declare class Overloaded { ",
            "take(pair: [number, string]): void; ",
            "take(pair: [string, number]): void; }",
        ),
        "declare class RestUnion { take(...args: [number] | [number, string]): void; }",
    ];
    for source in cases {
        let parsed = parse_source_file(source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
        let declarations = nodes(&parsed, SyntaxKind::ClassDeclaration);
        let [declaration] = declarations.as_slice() else {
            panic!("each boundary has one class")
        };
        let unsupported = method(&parsed, "take").declaration;
        let mut context = context(&parsed);
        let owner = symbol(&context, *declaration);
        let cold = counts(&context);
        for _ in 0..2 {
            assert_eq!(
                context.check_source_file(FILE),
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Class(unsupported)
                )),
                "{source}",
            );
            assert_eq!(counts(&context), cold, "{source}");
            assert!(context.store().declared_type_links(owner).is_none());
            assert!(context.store().value_symbol_links(owner).is_none());
            assert!(context.diagnostics().is_empty());
        }
    }
}
