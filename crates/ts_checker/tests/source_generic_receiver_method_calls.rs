use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SignatureId, TypeData, TypeId, TypeMapperId,
    TypeMapperKind,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_710);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic-receiver-method-calls.ts\""),
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

fn symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the source declaration or checked call must retain its signature")
}

fn callee(parsed: &ParseResult, call: NodeRef) -> NodeRef {
    let NodeData::CallExpression(call) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected a call expression")
    };
    NodeRef::new(parsed.arena.id(), FILE, call.expression)
}

fn argument(parsed: &ParseResult, call: NodeRef, index: usize) -> NodeRef {
    let NodeData::CallExpression(call) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected a call expression")
    };
    NodeRef::new(parsed.arena.id(), FILE, call.arguments.nodes[index])
}

struct SourceMethod {
    declaration: NodeRef,
    name: NodeRef,
    symbol: SemanticSymbolId,
    receiver: TypeId,
    callable: TypeId,
    signature: SignatureId,
    outer: TypeId,
    inner: TypeId,
    parameter_types: Vec<TypeId>,
    annotations: Vec<NodeRef>,
}

#[allow(clippy::too_many_lines)] // Keep the two source parameter owners and the method record together.
fn source_method(context: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) -> SourceMethod {
    let interface = nodes(parsed, SyntaxKind::InterfaceDeclaration)[0];
    let declaration = nodes(parsed, SyntaxKind::MethodSignature)[0];
    let parameters = nodes(parsed, SyntaxKind::TypeParameter);
    let [outer, inner] = parameters.as_slice() else {
        panic!("the source must have one receiver parameter and one method parameter")
    };
    assert_eq!(
        parsed.arena.get(outer.node).unwrap().parent,
        Some(interface.node)
    );
    assert_eq!(
        parsed.arena.get(inner.node).unwrap().parent,
        Some(declaration.node)
    );
    let owner = symbol(context, interface);
    let method = symbol(context, declaration);
    let outer_symbol = symbol(context, *outer);
    let inner_symbol = symbol(context, *inner);
    assert_ne!(outer_symbol, inner_symbol);
    let receiver = context.get_declared_type_of_symbol(owner).unwrap();
    let outer = context.get_declared_type_of_symbol(outer_symbol).unwrap();
    let inner = context.get_declared_type_of_symbol(inner_symbol).unwrap();
    assert_ne!(outer, inner);
    let NodeData::MethodSignatureDeclaration(data) =
        &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected a method signature")
    };
    let name = NodeRef::new(parsed.arena.id(), FILE, data.name);
    let callable = context.get_type_at_location(name).unwrap();
    assert_eq!(context.get_type_at_location(declaration), Ok(callable));
    let declared = signature(context, declaration);
    let mut annotations = Vec::new();
    let mut parameter_symbols = Vec::new();
    let mut parameter_types = Vec::new();
    for &parameter in &data.parameters.nodes {
        let parameter = NodeRef::new(parsed.arena.id(), FILE, parameter);
        parameter_symbols.push(symbol(context, parameter));
        let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
        else {
            panic!("expected a method value parameter")
        };
        let annotation = NodeRef::new(parsed.arena.id(), FILE, data.type_.unwrap());
        parameter_types.push(context.get_type_from_type_node(annotation).unwrap());
        annotations.push(annotation);
    }
    let return_annotation = NodeRef::new(parsed.arena.id(), FILE, data.type_.unwrap());
    assert_eq!(
        context.get_type_from_type_node(return_annotation),
        Ok(inner)
    );
    assert_eq!(context.get_return_type_of_signature(declared), Ok(inner));
    annotations.push(return_annotation);

    let store = context.store();
    assert_eq!(store.get_parent_of_symbol(outer_symbol), Some(owner));
    assert_eq!(store.get_parent_of_symbol(method), Some(owner));
    assert!(store.symbol(inner_symbol).unwrap().parent().is_none());
    assert_eq!(
        store.symbol(method).unwrap().declarations(),
        Some(&[declaration][..])
    );
    assert_eq!(
        store.type_payload(outer).unwrap().symbol(),
        Some(outer_symbol)
    );
    assert_eq!(
        store.type_payload(inner).unwrap().symbol(),
        Some(inner_symbol)
    );
    for (type_, symbol) in [(outer, outer_symbol), (inner, inner_symbol)] {
        assert_eq!(
            store.declared_type_links(symbol).unwrap().declared_type,
            Some(type_)
        );
        let TypeData::TypeParameter(parameter) = store.type_payload(type_).unwrap().data() else {
            panic!("both declared parameters must retain their source types")
        };
        assert_eq!(parameter.target, None);
        assert_eq!(parameter.mapper, None);
    }
    let record = store.signature(declared).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(record.type_parameters(), [inner]);
    assert!(!record.type_parameters().contains(&outer));
    assert_eq!(record.parameters(), parameter_symbols);
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    let TypeData::Object(object) = store.type_payload(callable).unwrap().data() else {
        panic!("the source method must retain its callable object")
    };
    assert_eq!(object.target, None);
    assert_eq!(object.mapper, None);
    assert_eq!(object.structured.call_signature_count, 1);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[declared][..])
    );
    SourceMethod {
        declaration,
        name,
        symbol: method,
        receiver,
        callable,
        signature: declared,
        outer,
        inner,
        parameter_types,
        annotations,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ReceiverMethod {
    receiver: TypeId,
    callable: TypeId,
    signature: SignatureId,
    inner: TypeId,
    mapper: TypeMapperId,
}

#[allow(clippy::too_many_lines)] // Check the actual receiver, copied signature, and fresh method parameter.
fn receiver_method(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    call: NodeRef,
    source: &SourceMethod,
    outer_argument: TypeId,
) -> ReceiverMethod {
    let access = callee(parsed, call);
    let NodeData::PropertyAccessExpression(access_data) =
        &parsed.arena.get(access.node).unwrap().data
    else {
        panic!("the method call must have an actual interface receiver")
    };
    let receiver_node = NodeRef::new(parsed.arena.id(), FILE, access_data.expression);
    let receiver = context.get_type_at_location(receiver_node).unwrap();
    let callable = context.get_type_at_location(access).unwrap();
    let store = context.store();
    let TypeData::TypeReference(reference) = store.type_payload(receiver).unwrap().data() else {
        panic!("the receiver must be a real generic interface instance")
    };
    assert_eq!(reference.object.target, Some(source.receiver));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[outer_argument][..])
    );
    let record = store.type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(source.symbol));
    let TypeData::Object(object) = record.data() else {
        panic!("the method lookup must retain its copied callable")
    };
    assert_ne!(callable, source.callable);
    assert_eq!(object.target, Some(source.callable));
    let owner_mapper = object.mapper.unwrap();
    assert_eq!(
        store.map_type(owner_mapper, source.outer),
        Some(outer_argument)
    );
    assert_eq!(object.structured.call_signature_count, 1);
    let [copied] = object.structured.signatures.as_deref().unwrap() else {
        panic!("the receiver must retain the one copied method signature")
    };
    let copied = *copied;
    let record = store.signature(copied).unwrap();
    assert_ne!(copied, source.signature);
    assert_eq!(record.target(), Some(source.signature));
    assert_eq!(record.declaration(), Some(source.declaration));
    let [inner] = record.type_parameters() else {
        panic!("receiver mapping must retain a fresh method type parameter")
    };
    let inner = *inner;
    assert_ne!(inner, source.inner);
    assert_ne!(inner, source.outer);
    let mapper = record.mapper().unwrap();
    assert_ne!(mapper, owner_mapper);
    assert_eq!(store.mapper_kind(mapper), Some(TypeMapperKind::Unknown));
    let TypeData::TypeParameter(parameter) = store.type_payload(inner).unwrap().data() else {
        panic!("the copied method parameter must retain its original target and mapper")
    };
    assert_eq!(parameter.target, Some(source.inner));
    assert_eq!(parameter.mapper, Some(mapper));
    assert_eq!(
        store.type_payload(inner).unwrap().symbol(),
        store.type_payload(source.inner).unwrap().symbol()
    );
    let TypeData::TypeParameter(original_parameter) =
        store.type_payload(source.inner).unwrap().data()
    else {
        panic!("the original method parameter must remain present")
    };
    assert_eq!(parameter.constraint, original_parameter.constraint);
    let original = store.signature(source.signature).unwrap();
    assert_eq!(record.parameters().len(), original.parameters().len());
    for ((&parameter, &target), &template) in record
        .parameters()
        .iter()
        .zip(original.parameters())
        .zip(&source.parameter_types)
    {
        assert_ne!(parameter, target);
        let links = store.value_symbol_links(parameter).unwrap();
        assert_eq!(links.target, Some(target));
        assert_eq!(links.mapper, Some(mapper));
        let expected = if template == source.outer {
            outer_argument
        } else {
            assert_eq!(template, source.inner);
            inner
        };
        assert_eq!(links.resolved_type, Some(expected));
    }
    assert_eq!(context.get_return_type_of_signature(copied), Ok(inner));
    assert_eq!(
        context.get_return_type_of_signature(source.signature),
        Ok(source.inner)
    );
    ReceiverMethod {
        receiver,
        callable,
        signature: copied,
        inner,
        mapper,
    }
}

fn assert_call(
    context: &mut CanonicalCheckerContext<'_>,
    call: NodeRef,
    source: &SourceMethod,
    receiver: ReceiverMethod,
    result: TypeId,
    checked: bool,
) -> SignatureId {
    assert_eq!(context.get_type_at_location(call), Ok(result));
    let selected = signature(context, call);
    assert_eq!(context.get_return_type_of_signature(selected), Ok(result));
    let store = context.store();
    let record = store.signature(selected).unwrap();
    assert_ne!(selected, receiver.signature);
    assert_eq!(record.target(), Some(receiver.signature));
    assert_eq!(record.declaration(), Some(source.declaration));
    assert!(record.type_parameters().is_empty());
    let mapper = record.mapper().unwrap();
    assert_eq!(store.mapper_kind(mapper), Some(TypeMapperKind::Simple));
    assert_eq!(store.map_type(mapper, receiver.inner), Some(result));
    assert_eq!(store.map_type(mapper, source.inner), Some(source.inner));
    assert_eq!(store.map_type(mapper, source.outer), Some(source.outer));
    let original = store.signature(source.signature).unwrap();
    let copied = store.signature(receiver.signature).unwrap();
    assert_eq!(record.parameters().len(), original.parameters().len());
    for (index, &parameter) in record.parameters().iter().enumerate() {
        let source_parameter = original.parameters()[index];
        let receiver_parameter = copied.parameters()[index];
        let links = store.value_symbol_links(parameter).unwrap();
        if source.parameter_types[index] == source.outer {
            assert_eq!(parameter, receiver_parameter);
            assert_eq!(links.target, Some(source_parameter));
            assert_eq!(links.mapper, Some(receiver.mapper));
            assert!(links.resolved_type.is_some());
        } else {
            assert_eq!(source.parameter_types[index], source.inner);
            assert_ne!(parameter, receiver_parameter);
            assert_ne!(parameter, source_parameter);
            assert_eq!(links.target, Some(source_parameter));
            let composed = links.mapper.unwrap();
            assert_ne!(composed, receiver.mapper);
            assert_ne!(composed, mapper);
            assert!(store.mapper_payload(composed).is_some());
            assert_eq!(store.mapper_kind(composed), Some(TypeMapperKind::Unknown));
            assert_eq!(links.resolved_type, checked.then_some(result));
        }
    }
    selected
}

fn snapshot(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl std::fmt::Debug + PartialEq + use<> {
    let store = context.store();
    let nodes = parsed
        .arena
        .iter()
        .map(|(node, _)| NodeRef::new(parsed.arena.id(), FILE, node))
        .collect::<Vec<_>>();
    (
        [
            store.type_len(),
            store.symbol_len(),
            store.signature_len(),
            store.mapper_len(),
            store.index_info_len(),
            store.type_alias_len(),
            store.symbol_store().symbol_table_len(),
        ],
        nodes
            .iter()
            .map(|&node| {
                (
                    store.type_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .signatures()
            .map(|(id, record)| {
                (
                    id,
                    record.declaration(),
                    record.flags(),
                    record.min_argument_count(),
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
            })
            .collect::<Vec<_>>(),
        store
            .types()
            .filter_map(|(id, record)| {
                if let TypeData::TypeParameter(data) = record.data() {
                    Some((id, record.symbol(), data.clone()))
                } else {
                    None
                }
            })
            .collect::<Vec<_>>(),
        store
            .types()
            .filter_map(|(id, record)| {
                record
                    .data()
                    .structured()
                    .map(|data| (id, record.object_flags(), data.clone()))
            })
            .collect::<Vec<_>>(),
        store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        context.diagnostics().clone(),
    )
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    source: &SourceMethod,
    calls: &[NodeRef],
    receivers: &[ReceiverMethod],
) {
    let mut queries = vec![
        (source.declaration, source.callable),
        (source.name, source.callable),
    ];
    let mut returns = vec![(source.signature, source.inner)];
    let mut selected = Vec::new();
    for &call in calls {
        for node in [callee(parsed, call), call] {
            queries.push((node, context.get_type_at_location(node).unwrap()));
        }
        let signature = signature(context, call);
        selected.push(signature);
        returns.push((
            signature,
            context.get_return_type_of_signature(signature).unwrap(),
        ));
    }
    for receiver in receivers {
        returns.push((receiver.signature, receiver.inner));
    }
    let annotations = source
        .annotations
        .iter()
        .map(|&node| (node, context.get_type_from_type_node(node).unwrap()))
        .collect::<Vec<_>>();
    let warm = snapshot(context, parsed);
    for recheck in [false, true, true] {
        if recheck {
            context.recheck_source_file(FILE).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        for &(node, expected) in &queries {
            assert_eq!(context.get_type_at_location(node), Ok(expected));
        }
        for &(signature, expected) in &returns {
            assert_eq!(
                context.get_return_type_of_signature(signature),
                Ok(expected)
            );
        }
        for &(node, expected) in &annotations {
            assert_eq!(context.get_type_from_type_node(node), Ok(expected));
        }
        for (&call, &expected) in calls.iter().zip(&selected) {
            assert_eq!(signature(context, call), expected);
        }
        assert_eq!(snapshot(context, parsed), warm);
        assert!(context.store().type_resolution_is_empty());
    }
}

#[test]
fn generic_receiver_method_calls_select_on_choice_any_and_demand_the_copied_return() {
    let parsed = parse_source_file(concat!(
        "interface Choice<T> { select<U>(value: U): U; }\n",
        "declare const choice: Choice<any>;\n",
        "const selected: string = choice.select<string>('x');\n",
    ));
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 1);
    for query_first in [false, true] {
        let mut context = context(&parsed);
        let early = query_first.then(|| {
            let callable = context
                .get_type_at_location(callee(&parsed, calls[0]))
                .unwrap();
            let copied = context
                .store()
                .type_payload(callable)
                .unwrap()
                .data()
                .structured()
                .unwrap()
                .signatures
                .as_ref()
                .unwrap()[0];
            let return_type = context.get_return_type_of_signature(copied).unwrap();
            (callable, copied, return_type)
        });
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let source = source_method(&mut context, &parsed);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let any = bootstrap.any_type;
        let string = bootstrap.string_type;
        let receiver = receiver_method(&mut context, &parsed, calls[0], &source, any);
        assert_call(&mut context, calls[0], &source, receiver, string, true);
        if let Some(early) = early {
            assert_eq!(
                early,
                (receiver.callable, receiver.signature, receiver.inner)
            );
        }
        assert_replay(&mut context, &parsed, &source, &calls, &[receiver]);
    }
}

#[test]
fn generic_receiver_method_calls_keep_outer_and_inner_specializations_separate() {
    let parsed = parse_source_file(concat!(
        "interface Choice<T> { select<U>(outer: T, value: U): U; }\n",
        "declare const text: Choice<string>;\n",
        "declare const numeric: Choice<number>;\n",
        "const first: number = text.select<number>('outer', 1);\n",
        "const inferred: 'x' = text.select('outer', 'x');\n",
        "const second: string = numeric.select<string>(1, 'inner');\n",
        "const inferredNumber: 2 = numeric.select(1, 2);\n",
        "const repeated: number = text.select<number>('again', 3);\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let source = source_method(&mut context, &parsed);
    assert_eq!(source.parameter_types, [source.outer, source.inner]);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 5);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let string = bootstrap.string_type;
    let number = bootstrap.number_type;
    let text = receiver_method(&mut context, &parsed, calls[0], &source, string);
    let numeric = receiver_method(&mut context, &parsed, calls[2], &source, number);
    assert_ne!(text.receiver, numeric.receiver);
    assert_ne!(text.callable, numeric.callable);
    assert_ne!(text.signature, numeric.signature);
    assert_ne!(text.inner, numeric.inner);
    assert_ne!(text.mapper, numeric.mapper);
    let inferred_text = context
        .get_type_at_location(argument(&parsed, calls[1], 1))
        .unwrap();
    let inferred_number = context
        .get_type_at_location(argument(&parsed, calls[3], 1))
        .unwrap();
    assert_eq!(context.type_to_string(inferred_text).unwrap(), "\"x\"");
    assert_eq!(context.type_to_string(inferred_number).unwrap(), "2");
    let results = [number, inferred_text, string, inferred_number, number];
    let receivers = [text, text, numeric, numeric, text];
    let selected = calls
        .iter()
        .zip(receivers)
        .zip(results)
        .map(|((&call, receiver), result)| {
            assert_call(&mut context, call, &source, receiver, result, true)
        })
        .collect::<Vec<_>>();
    assert_eq!(selected[0], selected[4]);
    assert_ne!(selected[0], selected[1]);
    assert_ne!(selected[2], selected[3]);
    assert_replay(&mut context, &parsed, &source, &calls, &receivers);
}

#[test]
#[allow(clippy::too_many_lines)] // Exact diagnostics and lazy recovery records belong to the same calls.
fn generic_receiver_method_calls_keep_constraints_and_exact_argument_diagnostics() {
    let parsed = parse_source_file(concat!(
        "interface Choice<T> { select<U extends string>(outer: T, value: U): U; }\n",
        "declare const choice: Choice<number>;\n",
        "const good: string = choice.select<string>(1, 'ok');\n",
        "const inferred: 'yes' = choice.select(1, 'yes');\n",
        "choice.select<string>('wrong', 'ok');\n",
        "choice.select<string>(1, 2);\n",
        "choice.select<number>(1, 2);\n",
        "choice.select<string>(1);\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let source = source_method(&mut context, &parsed);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 6);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let string = bootstrap.string_type;
    let number = bootstrap.number_type;
    let receiver = receiver_method(&mut context, &parsed, calls[0], &source, number);
    for parameter in [source.inner, receiver.inner] {
        let TypeData::TypeParameter(parameter) =
            context.store().type_payload(parameter).unwrap().data()
        else {
            panic!("the string constraint must stay on both source and copied method parameters")
        };
        assert_eq!(parameter.constraint, Some(string));
    }
    let inferred_argument = context
        .get_type_at_location(argument(&parsed, calls[1], 1))
        .unwrap();
    let TypeData::Literal(literal) = context
        .store()
        .type_payload(inferred_argument)
        .unwrap()
        .data()
    else {
        panic!("the inferred argument must be the real source string literal")
    };
    let inferred = literal.regular_type;
    assert_eq!(context.type_to_string(inferred).unwrap(), "\"yes\"");
    let results = [string, inferred, string, string, number, string];
    let selected = calls
        .iter()
        .zip(results)
        .enumerate()
        .map(|(index, (&call, result))| {
            assert_call(&mut context, call, &source, receiver, result, index < 2)
        })
        .collect::<Vec<_>>();
    for &recovery in &selected[2..] {
        assert_ne!(recovery, selected[0]);
    }
    assert_ne!(selected[2], selected[3]);
    assert_ne!(selected[3], selected[5]);
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 4, "{diagnostics:?}");
    for (diagnostic, call, index, message) in [
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
        assert_eq!(diagnostic.node, Some(argument(&parsed, call, index)));
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
    }
    let NodeData::CallExpression(bad_constraint) = &parsed.arena.get(calls[4].node).unwrap().data
    else {
        panic!("expected the explicit constraint failure")
    };
    let type_argument = NodeRef::new(
        parsed.arena.id(),
        FILE,
        bad_constraint.type_arguments.as_ref().unwrap().nodes[0],
    );
    assert_eq!(diagnostics[2].diagnostic.code(), 2344);
    assert_eq!(diagnostics[2].node, Some(type_argument));
    assert_eq!(diagnostics[2].range_override, None);
    assert!(diagnostics[2].related_information.is_empty());
    assert_eq!(
        diagnostics[2].diagnostic.render().unwrap(),
        "Type 'number' does not satisfy the constraint 'string'."
    );
    let missing = &diagnostics[3];
    assert_eq!(missing.diagnostic.code(), 2554);
    assert_eq!(missing.node, Some(callee(&parsed, calls[5])));
    assert_eq!(missing.range_override, None);
    assert_eq!(
        missing.diagnostic.render().unwrap(),
        "Expected 2 arguments, but got 1."
    );
    let [related] = missing.related_information.as_slice() else {
        panic!("the missing argument must identify the original method parameter")
    };
    assert_eq!(related.diagnostic.code(), 6210);
    assert_eq!(related.node, Some(nodes(&parsed, SyntaxKind::Parameter)[1]));
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument for 'value' was not provided."
    );
    assert_replay(&mut context, &parsed, &source, &calls, &[receiver]);
}
