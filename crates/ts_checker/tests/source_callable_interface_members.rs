use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, InternalSymbolName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SignatureId, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_620);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/callable-interfaces.ts\""),
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
        CanonicalCheckerOptions::default(),
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

fn callee(parsed: &ParseResult, call: NodeRef) -> NodeRef {
    let NodeData::CallExpression(call) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected a call expression")
    };
    NodeRef::new(parsed.arena.id(), FILE, call.expression)
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the call or declaration must retain its signature")
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 6] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

struct DeclaredCallable {
    target: TypeId,
    signature: SignatureId,
    parameter: SemanticSymbolId,
    type_parameter: TypeId,
    annotations: [NodeRef; 2],
}

fn declared_callable(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> DeclaredCallable {
    let declaration = nodes(parsed, SyntaxKind::InterfaceDeclaration)[0];
    let call = nodes(parsed, SyntaxKind::CallSignature)[0];
    let type_parameter = nodes(parsed, SyntaxKind::TypeParameter)[0];
    let parameter = nodes(parsed, SyntaxKind::Parameter)[0];
    let owner = symbol(context, declaration);
    let call_owner = symbol(context, call);
    let parameter_owner = symbol(context, parameter);
    let type_parameter_owner = symbol(context, type_parameter);
    let target = context.get_declared_type_of_symbol(owner).unwrap();
    let type_parameter = context
        .get_declared_type_of_symbol(type_parameter_owner)
        .unwrap();
    let declared = signature(context, call);

    let store = context.store();
    assert_eq!(store.get_parent_of_symbol(call_owner), Some(owner));
    let members = store.symbol(owner).unwrap().members().unwrap();
    assert_eq!(
        store
            .symbol_table(members)
            .unwrap()
            .get(InternalSymbolName::Call.as_ref()),
        Some(call_owner),
    );
    assert_eq!(
        store.symbol(call_owner).unwrap().declarations(),
        Some(&[call][..])
    );
    assert_eq!(
        store.type_payload(type_parameter).unwrap().symbol(),
        Some(type_parameter_owner),
    );
    let TypeData::Interface(interface) = store.type_payload(target).unwrap().data() else {
        panic!("the declaration must retain its generic interface target")
    };
    assert!(interface.declared_members_resolved);
    assert_eq!(
        interface.declared_call_signatures.as_deref(),
        Some(&[declared][..])
    );
    let record = store.signature(declared).unwrap();
    assert_eq!(record.declaration(), Some(call));
    assert_eq!(record.parameters(), [parameter_owner]);
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(
        store
            .value_symbol_links(parameter_owner)
            .unwrap()
            .resolved_type,
        Some(type_parameter),
    );

    let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        panic!("expected a parameter declaration")
    };
    let NodeData::CallSignatureDeclaration(call) = &parsed.arena.get(call.node).unwrap().data
    else {
        panic!("expected an interface call signature")
    };
    let annotations = [parameter.type_.unwrap(), call.type_.unwrap()]
        .map(|node| NodeRef::new(parsed.arena.id(), FILE, node));
    assert_eq!(
        context.get_type_from_type_node(annotations[0]),
        Ok(type_parameter)
    );
    let return_type = context.get_type_from_type_node(annotations[1]).unwrap();
    assert_eq!(
        context.get_return_type_of_signature(declared),
        Ok(return_type)
    );

    DeclaredCallable {
        target,
        signature: declared,
        parameter: parameter_owner,
        type_parameter,
        annotations,
    }
}

fn assert_specialized_call(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    call: NodeRef,
    declared: &DeclaredCallable,
    argument_type: TypeId,
    return_type: TypeId,
) -> SignatureId {
    assert_eq!(context.get_type_at_location(call), Ok(return_type));
    let callable = context.get_type_at_location(callee(parsed, call)).unwrap();
    let selected = signature(context, call);
    assert_eq!(
        context.get_return_type_of_signature(selected),
        Ok(return_type)
    );
    let store = context.store();
    let TypeData::TypeReference(reference) = store.type_payload(callable).unwrap().data() else {
        panic!("the callable must retain its specialized interface type")
    };
    assert_eq!(reference.object.target, Some(declared.target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[argument_type][..])
    );
    assert_eq!(reference.object.structured.call_signature_count, 1);
    assert_eq!(
        reference.object.structured.signatures.as_deref(),
        Some(&[selected][..])
    );
    let record = store.signature(selected).unwrap();
    assert_eq!(record.target(), Some(declared.signature));
    assert_eq!(
        record.declaration(),
        store.signature(declared.signature).unwrap().declaration()
    );
    assert!(record.mapper().is_some());
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.resolved_return_type(), Some(return_type));
    let [parameter] = record.parameters() else {
        panic!("the call must retain one specialized parameter")
    };
    assert_ne!(*parameter, declared.parameter);
    let links = store.value_symbol_links(*parameter).unwrap();
    assert_eq!(links.target, Some(declared.parameter));
    assert_eq!(links.mapper, record.mapper());
    assert_eq!(links.resolved_type, Some(argument_type));
    selected
}

fn assert_argument_errors(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    expected: &[(NodeRef, &str)],
) {
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), expected.len(), "{diagnostics:?}");
    for (diagnostic, &(call, message)) in diagnostics.iter().zip(expected) {
        let NodeData::CallExpression(call) = &parsed.arena.get(call.node).unwrap().data else {
            panic!("expected a call expression")
        };
        let argument = NodeRef::new(parsed.arena.id(), FILE, call.arguments.nodes[0]);
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(diagnostic.node, Some(argument));
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
    }
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    calls: &[NodeRef],
    annotations: &[NodeRef],
) {
    let expected_calls = calls
        .iter()
        .map(|&call| {
            (
                context.get_type_at_location(callee(parsed, call)).unwrap(),
                context.get_type_at_location(call).unwrap(),
                signature(context, call),
            )
        })
        .collect::<Vec<_>>();
    let expected_annotations = annotations
        .iter()
        .map(|&node| context.get_type_from_type_node(node).unwrap())
        .collect::<Vec<_>>();
    let warm = (counts(context), context.diagnostics().clone());
    for _ in 0..2 {
        context.recheck_source_file(FILE).unwrap();
        for (&call, &(callable, return_type, selected)) in calls.iter().zip(&expected_calls) {
            assert_eq!(
                context.get_type_at_location(callee(parsed, call)),
                Ok(callable)
            );
            assert_eq!(context.get_type_at_location(call), Ok(return_type));
            assert_eq!(signature(context, call), selected);
            assert_eq!(
                context.get_return_type_of_signature(selected),
                Ok(return_type)
            );
        }
        for (&node, &expected) in annotations.iter().zip(&expected_annotations) {
            assert_eq!(context.get_type_from_type_node(node), Ok(expected));
        }
        assert_eq!((counts(context), context.diagnostics().clone()), warm);
    }
}

#[test]
fn generic_interface_calls_keep_distinct_parameter_and_return_specializations() {
    let parsed = parse_source_file(concat!(
        "interface Callable<T> { (value: T): T; }\n",
        "declare const text: Callable<string>;\n",
        "declare const numeric: Callable<number>;\n",
        "const first: string = text('ok');\n",
        "const second: number = numeric(1);\n",
        "text(true);\n",
        "numeric('bad');\n",
    ));
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 4);
    for query_first in [false, true] {
        let mut context = context(&parsed);
        let early = query_first.then(|| {
            [calls[0], calls[1]]
                .map(|call| context.get_type_at_location(callee(&parsed, call)).unwrap())
        });
        context.check_source_file(FILE).unwrap();
        let declared = declared_callable(&mut context, &parsed);
        assert_eq!(
            context.get_return_type_of_signature(declared.signature),
            Ok(declared.type_parameter)
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let expected = [bootstrap.string_type, bootstrap.number_type];
        let selected = calls
            .iter()
            .enumerate()
            .map(|(index, &call)| {
                let type_ = expected[index % 2];
                assert_specialized_call(&mut context, &parsed, call, &declared, type_, type_)
            })
            .collect::<Vec<_>>();
        assert_eq!(selected[0], selected[2]);
        assert_eq!(selected[1], selected[3]);
        assert_ne!(selected[0], selected[1]);
        if let Some(early) = early {
            for (call, expected) in [calls[0], calls[1]].into_iter().zip(early) {
                assert_eq!(
                    context.get_type_at_location(callee(&parsed, call)),
                    Ok(expected)
                );
            }
        }
        assert_argument_errors(
            &context,
            &parsed,
            &[
                (
                    calls[2],
                    "Argument of type 'boolean' is not assignable to parameter of type 'string'.",
                ),
                (
                    calls[3],
                    "Argument of type 'string' is not assignable to parameter of type 'number'.",
                ),
            ],
        );
        assert_replay(&mut context, &parsed, &calls, &declared.annotations);
    }
}

#[test]
fn recursive_callable_property_does_not_replace_the_outer_call_signature() {
    let parsed = parse_source_file(concat!(
        "interface Callable<Value> { (value: Value): Value; field: Callable<boolean>; }\n",
        "declare const text: Callable<string>;\n",
        "const nested: boolean = text.field(true);\n",
        "const outer: string = text('ok');\n",
        "text(false);\n",
        "text.field('bad');\n",
    ));
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 4);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let declared = declared_callable(&mut context, &parsed);
    assert_eq!(
        context.get_return_type_of_signature(declared.signature),
        Ok(declared.type_parameter)
    );
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let expected = [
        bootstrap.boolean_type,
        bootstrap.string_type,
        bootstrap.string_type,
        bootstrap.boolean_type,
    ];
    let selected = calls
        .iter()
        .zip(expected)
        .map(|(&call, type_)| {
            assert_specialized_call(&mut context, &parsed, call, &declared, type_, type_)
        })
        .collect::<Vec<_>>();
    assert_eq!(selected[0], selected[3]);
    assert_eq!(selected[1], selected[2]);
    assert_ne!(selected[0], selected[1]);
    assert_argument_errors(
        &context,
        &parsed,
        &[
            (
                calls[2],
                "Argument of type 'boolean' is not assignable to parameter of type 'string'.",
            ),
            (
                calls[3],
                "Argument of type 'string' is not assignable to parameter of type 'boolean'.",
            ),
        ],
    );
    assert_replay(&mut context, &parsed, &calls, &declared.annotations);
}

#[test]
fn generic_interface_void_calls_keep_the_missing_argument_declaration() {
    let parsed = parse_source_file(concat!(
        "interface Sink<Item> { (value: Item): void; }\n",
        "declare const sink: Sink<number>;\n",
        "sink(1);\n",
        "sink();\n",
    ));
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 2);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let declared = declared_callable(&mut context, &parsed);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let void = bootstrap.void_type;
    assert_eq!(
        context.get_return_type_of_signature(declared.signature),
        Ok(void)
    );
    let selected = calls
        .iter()
        .map(|&call| assert_specialized_call(&mut context, &parsed, call, &declared, number, void))
        .collect::<Vec<_>>();
    assert_eq!(selected[0], selected[1]);
    let diagnostics = context.diagnostics().as_slice();
    let [diagnostic] = diagnostics else {
        panic!("expected one missing-argument diagnostic, got {diagnostics:?}")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2554);
    assert_eq!(diagnostic.node, Some(callee(&parsed, calls[1])));
    assert_eq!(diagnostic.range_override, None);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 0."
    );
    let [related] = diagnostic.related_information.as_slice() else {
        panic!("the diagnostic must identify the original parameter")
    };
    assert_eq!(related.diagnostic.code(), 6210);
    assert_eq!(related.node, Some(nodes(&parsed, SyntaxKind::Parameter)[0]));
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument for 'value' was not provided."
    );
    assert_replay(&mut context, &parsed, &calls, &declared.annotations);
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the original source case and check both levels of signature mapping.
fn call_owned_type_parameters_keep_signature_owners_and_replay() {
    let parsed = parse_source_file(concat!(
        "interface Callable<T> { <U>(value: U): T; }\n",
        "declare const callable: Callable<number>;\n",
        "callable('value');\n",
    ));
    let declaration = nodes(&parsed, SyntaxKind::CallSignature)[0];
    let call = nodes(&parsed, SyntaxKind::CallExpression)[0];
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(context.diagnostics().is_empty());
    let parameters = nodes(&parsed, SyntaxKind::TypeParameter)
        .into_iter()
        .map(|parameter| symbol(&context, parameter))
        .collect::<Vec<_>>();
    assert_eq!(parameters.len(), 2);
    assert_ne!(parameters[0], parameters[1]);
    let outer = context.get_declared_type_of_symbol(parameters[0]).unwrap();
    let inner = context.get_declared_type_of_symbol(parameters[1]).unwrap();
    assert_ne!(outer, inner);
    let interface = nodes(&parsed, SyntaxKind::InterfaceDeclaration)[0];
    let owner = symbol(&context, interface);
    let target = context.get_declared_type_of_symbol(owner).unwrap();
    let declared = signature(&context, declaration);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let string = bootstrap.string_type;
    assert_eq!(context.get_return_type_of_signature(declared), Ok(outer));
    assert_eq!(context.get_type_at_location(call), Ok(number));
    let instance = context.get_type_at_location(callee(&parsed, call)).unwrap();
    let TypeData::TypeReference(reference) = context.store().type_payload(instance).unwrap().data()
    else {
        panic!("the callable must retain its generic interface instance")
    };
    assert_eq!(reference.object.target, Some(target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[number][..])
    );
    assert_eq!(reference.object.structured.call_signature_count, 1);
    let [copied] = reference.object.structured.signatures.as_deref().unwrap() else {
        panic!("the instance must retain its one copied call signature")
    };
    let copied = *copied;
    assert_ne!(copied, declared);
    assert_eq!(context.get_return_type_of_signature(copied), Ok(number));
    let selected = signature(&context, call);
    assert_ne!(selected, copied);
    assert_eq!(context.get_return_type_of_signature(selected), Ok(number));
    let NodeData::CallSignatureDeclaration(call_data) =
        &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected the original call declaration")
    };
    let parameter = NodeRef::new(parsed.arena.id(), FILE, call_data.parameters.nodes[0]);
    let parameter_owner = symbol(&context, parameter);
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        panic!("expected the original value parameter")
    };
    let annotations = [parameter_data.type_.unwrap(), call_data.type_.unwrap()]
        .map(|node| NodeRef::new(parsed.arena.id(), FILE, node));
    assert_eq!(context.get_type_from_type_node(annotations[0]), Ok(inner));
    assert_eq!(context.get_type_from_type_node(annotations[1]), Ok(outer));
    let store = context.store();
    let original = store.signature(declared).unwrap();
    assert_eq!(original.declaration(), Some(declaration));
    assert_eq!(original.type_parameters(), [inner]);
    assert_eq!(original.parameters(), [parameter_owner]);
    assert_eq!(original.target(), None);
    assert_eq!(original.mapper(), None);
    let copy = store.signature(copied).unwrap();
    assert_eq!(copy.target(), Some(declared));
    assert_eq!(copy.declaration(), Some(declaration));
    assert_eq!(copy.min_argument_count(), 1);
    let [fresh] = copy.type_parameters() else {
        panic!("owner substitution must retain a fresh call-owned parameter")
    };
    let fresh = *fresh;
    assert_ne!(fresh, inner);
    assert_ne!(fresh, outer);
    let copy_mapper = copy.mapper().unwrap();
    let TypeData::TypeParameter(data) = store.type_payload(fresh).unwrap().data() else {
        panic!("the copied type parameter must retain its source identity")
    };
    assert_eq!(
        store.type_payload(fresh).unwrap().symbol(),
        Some(parameters[1])
    );
    assert_eq!(data.target, Some(inner));
    assert_eq!(data.mapper, Some(copy_mapper));
    let copied_parameter = copy.parameters()[0];
    assert_ne!(copied_parameter, parameter_owner);
    let links = store.value_symbol_links(copied_parameter).unwrap();
    assert_eq!(links.target, Some(parameter_owner));
    assert_eq!(links.mapper, Some(copy_mapper));
    assert_eq!(links.resolved_type, Some(fresh));
    let instantiated = store.signature(selected).unwrap();
    assert_eq!(instantiated.target(), Some(copied));
    assert_eq!(instantiated.declaration(), Some(declaration));
    assert!(instantiated.type_parameters().is_empty());
    let call_mapper = instantiated.mapper().unwrap();
    assert_ne!(call_mapper, copy_mapper);
    assert_eq!(store.map_type(call_mapper, fresh), Some(string));
    assert_eq!(store.map_type(call_mapper, inner), Some(inner));
    assert_eq!(store.map_type(call_mapper, outer), Some(outer));
    let selected_parameter = instantiated.parameters()[0];
    assert_ne!(selected_parameter, copied_parameter);
    assert_ne!(selected_parameter, parameter_owner);
    let links = store.value_symbol_links(selected_parameter).unwrap();
    assert_eq!(links.target, Some(parameter_owner));
    assert_eq!(links.resolved_type, Some(string));
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            [outer, inner, fresh].map(|type_| {
                let TypeData::TypeParameter(data) = store.type_payload(type_).unwrap().data()
                else {
                    panic!("source and copied type parameters must stay present")
                };
                (
                    type_,
                    store.type_payload(type_).unwrap().symbol(),
                    data.clone(),
                )
            }),
            [declared, copied, selected].map(|signature| {
                let record = store.signature(signature).unwrap();
                (
                    record.type_parameters().to_vec(),
                    record.target(),
                    record.mapper(),
                    record.resolved_return_type(),
                    record
                        .parameters()
                        .iter()
                        .map(|&parameter| (parameter, store.value_symbol_links(parameter).cloned()))
                        .collect::<Vec<_>>(),
                )
            }),
        )
    };
    let warm = snapshot(&context);
    assert_replay(&mut context, &parsed, &[call], &annotations);
    assert_eq!(snapshot(&context), warm);
    assert!(context.store().type_resolution_is_empty());
}
