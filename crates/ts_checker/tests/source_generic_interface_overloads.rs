use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, InternalSymbolName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SignatureFlags, SignatureId,
    SourceCheckError, TypeData, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_621);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/generic-interface-overloads.ts\""),
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
        .expect("the source declaration or checked call must retain its signature")
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

struct DeclaredOverloads {
    target: TypeId,
    type_parameter: TypeId,
    signatures: Vec<SignatureId>,
    return_types: Vec<TypeId>,
    annotations: Vec<NodeRef>,
}

#[allow(clippy::too_many_lines)] // Check the complete source declaration and its shared Call symbol.
fn declared_overloads(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    declaration: NodeRef,
) -> DeclaredOverloads {
    let NodeData::InterfaceDeclaration(interface) =
        &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected a generic interface declaration")
    };
    let [parameter] = interface.type_parameters.as_ref().unwrap().nodes.as_slice() else {
        panic!("the fixture must have one enclosing type parameter")
    };
    let parameter = NodeRef::new(parsed.arena.id(), FILE, *parameter);
    let owner = symbol(context, declaration);
    let target = context.get_declared_type_of_symbol(owner).unwrap();
    let parameter_owner = symbol(context, parameter);
    let type_parameter = context
        .get_declared_type_of_symbol(parameter_owner)
        .unwrap();
    let declarations = interface
        .members
        .nodes
        .iter()
        .map(|&node| NodeRef::new(parsed.arena.id(), FILE, node))
        .collect::<Vec<_>>();
    assert_eq!(declarations.len(), 2);
    let signatures = declarations
        .iter()
        .map(|&node| signature(context, node))
        .collect::<Vec<_>>();
    let call_owner = symbol(context, declarations[0]);
    let mut annotations = Vec::new();
    let mut return_types = Vec::new();
    for (&node, &signature) in declarations.iter().zip(&signatures) {
        let NodeData::CallSignatureDeclaration(call) = &parsed.arena.get(node.node).unwrap().data
        else {
            panic!("every member must be an interface call signature")
        };
        assert_eq!(symbol(context, node), call_owner);
        let mut parameters = Vec::new();
        for &parameter in &call.parameters.nodes {
            let parameter = NodeRef::new(parsed.arena.id(), FILE, parameter);
            let parameter_owner = symbol(context, parameter);
            let NodeData::ParameterDeclaration(parameter) =
                &parsed.arena.get(parameter.node).unwrap().data
            else {
                panic!("expected a declared call parameter")
            };
            let annotation = NodeRef::new(parsed.arena.id(), FILE, parameter.type_.unwrap());
            let type_ = context.get_type_from_type_node(annotation).unwrap();
            assert_eq!(
                context
                    .store()
                    .value_symbol_links(parameter_owner)
                    .unwrap()
                    .resolved_type,
                Some(type_),
            );
            parameters.push(parameter_owner);
            annotations.push(annotation);
        }
        let annotation = NodeRef::new(parsed.arena.id(), FILE, call.type_.unwrap());
        let return_type = context.get_type_from_type_node(annotation).unwrap();
        assert_eq!(
            context.get_return_type_of_signature(signature),
            Ok(return_type)
        );
        annotations.push(annotation);
        return_types.push(return_type);
        let record = context.store().signature(signature).unwrap();
        assert_eq!(record.declaration(), Some(node));
        assert_eq!(record.parameters(), parameters);
        assert!(record.type_parameters().is_empty());
        assert_eq!(record.target(), None);
        assert_eq!(record.mapper(), None);
    }

    let store = context.store();
    assert_eq!(store.get_parent_of_symbol(call_owner), Some(owner));
    assert_eq!(
        store.symbol(owner).unwrap().declarations(),
        Some(&[declaration][..])
    );
    let members = store.symbol(owner).unwrap().members().unwrap();
    let members = store.symbol_table(members).unwrap();
    assert_eq!(members.len(), 2);
    assert_eq!(
        members.get(InternalSymbolName::Call.as_ref()),
        Some(call_owner)
    );
    assert_eq!(
        store.symbol(call_owner).unwrap().declarations(),
        Some(declarations.as_slice()),
    );
    assert_eq!(
        store.type_payload(type_parameter).unwrap().symbol(),
        Some(parameter_owner)
    );
    let TypeData::Interface(interface) = store.type_payload(target).unwrap().data() else {
        panic!("the declaration must retain its generic interface target")
    };
    assert!(interface.declared_members_resolved);
    assert_eq!(
        interface.declared_call_signatures.as_deref(),
        Some(signatures.as_slice())
    );

    DeclaredOverloads {
        target,
        type_parameter,
        signatures,
        return_types,
        annotations,
    }
}

fn specialized_signatures(
    context: &mut CanonicalCheckerContext<'_>,
    declared: &DeclaredOverloads,
    instance: TypeId,
    argument: TypeId,
) -> Vec<SignatureId> {
    let TypeData::TypeReference(reference) = context.store().type_payload(instance).unwrap().data()
    else {
        panic!("the call must use a specialized generic interface")
    };
    assert_eq!(reference.object.target, Some(declared.target));
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[argument][..])
    );
    assert_eq!(
        reference.object.structured.call_signature_count,
        declared.signatures.len()
    );
    let signatures = reference.object.structured.signatures.clone().unwrap();
    assert_eq!(signatures.len(), declared.signatures.len());
    let substitute = |type_| {
        if type_ == declared.type_parameter {
            argument
        } else {
            type_
        }
    };
    for (&signature, &return_type) in signatures.iter().zip(&declared.return_types) {
        assert_eq!(
            context.get_return_type_of_signature(signature),
            Ok(substitute(return_type))
        );
    }
    let store = context.store();
    let mapper = store.signature(signatures[0]).unwrap().mapper().unwrap();
    assert_eq!(
        store.map_type(mapper, declared.type_parameter),
        Some(argument)
    );
    for (&copy, &original) in signatures.iter().zip(&declared.signatures) {
        assert_ne!(copy, original);
        let copy = store.signature(copy).unwrap();
        let original_record = store.signature(original).unwrap();
        assert_eq!(copy.target(), Some(original));
        assert_eq!(copy.mapper(), Some(mapper));
        assert_eq!(copy.declaration(), original_record.declaration());
        assert_eq!(copy.flags(), original_record.flags());
        assert_eq!(
            copy.min_argument_count(),
            original_record.min_argument_count()
        );
        assert!(copy.type_parameters().is_empty());
        assert_eq!(copy.parameters().len(), original_record.parameters().len());
        for (&parameter, &source) in copy.parameters().iter().zip(original_record.parameters()) {
            let links = store.value_symbol_links(parameter).unwrap();
            let source_type = store
                .value_symbol_links(source)
                .unwrap()
                .resolved_type
                .unwrap();
            if source_type == declared.type_parameter {
                assert_ne!(parameter, source);
                assert_eq!(links.target, Some(source));
                assert_eq!(links.mapper, Some(mapper));
            } else {
                assert_eq!(parameter, source);
                assert_eq!(links.target, None);
                assert_eq!(links.mapper, None);
            }
            assert_eq!(links.resolved_type, Some(substitute(source_type)));
        }
    }
    signatures
}

#[allow(clippy::too_many_lines)] // Replay all declaration, candidate, parameter, and diagnostic state.
fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    calls: &[NodeRef],
    declared: &[&DeclaredOverloads],
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
    let expected_annotations = declared
        .iter()
        .flat_map(|declared| &declared.annotations)
        .map(|&node| (node, context.get_type_from_type_node(node).unwrap()))
        .collect::<Vec<_>>();
    let types = declared
        .iter()
        .map(|declared| declared.target)
        .chain(expected_calls.iter().map(|&(type_, _, _)| type_))
        .collect::<Vec<_>>();
    let signatures = declared
        .iter()
        .flat_map(|declared| declared.signatures.iter().copied())
        .chain(expected_calls.iter().flat_map(|&(type_, _, _)| {
            context
                .store()
                .type_payload(type_)
                .unwrap()
                .data()
                .structured()
                .unwrap()
                .signatures
                .as_ref()
                .unwrap()
                .iter()
                .copied()
        }))
        .collect::<Vec<_>>();
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            counts(context),
            context.diagnostics().clone(),
            types
                .iter()
                .map(|&type_| {
                    let record = store.type_payload(type_).unwrap();
                    (record.object_flags(), record.data().structured().cloned())
                })
                .collect::<Vec<_>>(),
            signatures
                .iter()
                .map(|&signature| {
                    let record = store.signature(signature).unwrap();
                    (
                        record.declaration(),
                        record.flags(),
                        record.min_argument_count(),
                        record.target(),
                        record.mapper(),
                        record.resolved_return_type(),
                        record
                            .parameters()
                            .iter()
                            .map(|&parameter| {
                                (parameter, store.value_symbol_links(parameter).cloned())
                            })
                            .collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>(),
        )
    };
    let warm = snapshot(context);
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
        for &(annotation, type_) in &expected_annotations {
            assert_eq!(context.get_type_from_type_node(annotation), Ok(type_));
        }
        assert_eq!(snapshot(context), warm);
    }
}

#[test]
fn generic_interface_overloads_keep_arity_specialization_and_replay_identity() {
    let parsed = parse_source_file(concat!(
        "interface Callable<T> { (value: T): T; (value: T, other: T): T; }\n",
        "declare const text: Callable<string>;\n",
        "declare const numeric: Callable<number>;\n",
        "const first: string = text('one');\n",
        "const second: string = text('one', 'two');\n",
        "const third: number = numeric(1);\n",
        "const fourth: number = numeric(1, 2);\n",
    ));
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 4);
    for query_first in [false, true] {
        let mut context = context(&parsed);
        let early = query_first.then(|| {
            [calls[0], calls[2]]
                .map(|call| context.get_type_at_location(callee(&parsed, call)).unwrap())
        });
        context.check_source_file(FILE).unwrap();
        assert!(context.diagnostics().is_empty());
        let declared = declared_overloads(
            &mut context,
            &parsed,
            nodes(&parsed, SyntaxKind::InterfaceDeclaration)[0],
        );
        assert_eq!(declared.return_types, [declared.type_parameter; 2]);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let arguments = [bootstrap.string_type, bootstrap.number_type];
        let instances = [calls[0], calls[2]]
            .map(|call| context.get_type_at_location(callee(&parsed, call)).unwrap());
        assert_ne!(instances[0], instances[1]);
        let specialized = instances
            .iter()
            .zip(arguments)
            .map(|(&instance, argument)| {
                specialized_signatures(&mut context, &declared, instance, argument)
            })
            .collect::<Vec<_>>();
        assert_ne!(specialized[0], specialized[1]);
        for (index, &call) in calls.iter().enumerate() {
            assert_eq!(signature(&context, call), specialized[index / 2][index % 2]);
            assert_eq!(context.get_type_at_location(call), Ok(arguments[index / 2]));
        }
        if let Some(early) = early {
            assert_eq!(instances, early);
        }
        assert_replay(&mut context, &parsed, &calls, &[&declared]);
    }
}

#[test]
fn generic_interface_overloads_choose_literals_without_reordering_stored_rows() {
    let parsed = parse_source_file(concat!(
        "interface Specialized<T> { (value: T): 'general'; (value: 'key'): 'literal'; }\n",
        "interface Ordered<T> { (value: T): 'first'; (value: T): 'second'; }\n",
        "declare const specialized: Specialized<string>;\n",
        "declare const ordered: Ordered<string>;\n",
        "const literal: 'literal' = specialized('key');\n",
        "const broad: 'general' = specialized('other');\n",
        "const first: 'first' = ordered('key');\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    assert!(context.diagnostics().is_empty());
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 3);
    let declarations = nodes(&parsed, SyntaxKind::InterfaceDeclaration);
    let specialized = declared_overloads(&mut context, &parsed, declarations[0]);
    let ordered = declared_overloads(&mut context, &parsed, declarations[1]);
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let instances = [calls[0], calls[2]]
        .map(|call| context.get_type_at_location(callee(&parsed, call)).unwrap());
    let specialized_copies =
        specialized_signatures(&mut context, &specialized, instances[0], string);
    let ordered_copies = specialized_signatures(&mut context, &ordered, instances[1], string);
    for (index, &signature) in specialized.signatures.iter().enumerate() {
        assert_eq!(
            context
                .store()
                .signature(signature)
                .unwrap()
                .flags()
                .contains(SignatureFlags::HAS_LITERAL_TYPES),
            index == 1,
        );
    }
    assert!(ordered.signatures.iter().all(|&signature| {
        !context
            .store()
            .signature(signature)
            .unwrap()
            .flags()
            .contains(SignatureFlags::HAS_LITERAL_TYPES)
    }));
    assert_ne!(specialized.return_types[0], specialized.return_types[1]);
    assert_ne!(ordered.return_types[0], ordered.return_types[1]);
    for ((&call, selected), return_type) in calls
        .iter()
        .zip([
            specialized_copies[1],
            specialized_copies[0],
            ordered_copies[0],
        ])
        .zip([
            specialized.return_types[1],
            specialized.return_types[0],
            ordered.return_types[0],
        ])
    {
        assert_eq!(signature(&context, call), selected);
        assert_eq!(context.get_type_at_location(call), Ok(return_type));
    }
    assert_replay(&mut context, &parsed, &calls, &[&specialized, &ordered]);
}

#[test]
fn generic_interface_overloads_report_the_only_matching_arity_argument_error() {
    let parsed = parse_source_file(concat!(
        "interface Recovery<T> { (value: T, other: T): T; (value: T): T; }\n",
        "declare const recovery: Recovery<string>;\n",
        "const good: string = recovery('one', 'two');\n",
        "const bad: string = recovery(true);\n",
    ));
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 2);
    let declared = declared_overloads(
        &mut context,
        &parsed,
        nodes(&parsed, SyntaxKind::InterfaceDeclaration)[0],
    );
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let instance = context
        .get_type_at_location(callee(&parsed, calls[0]))
        .unwrap();
    let copies = specialized_signatures(&mut context, &declared, instance, string);
    assert_eq!(signature(&context, calls[0]), copies[0]);
    assert_eq!(signature(&context, calls[1]), copies[1]);
    for &call in &calls {
        assert_eq!(context.get_type_at_location(call), Ok(string));
    }
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one argument diagnostic")
    };
    let NodeData::CallExpression(bad_call) = &parsed.arena.get(calls[1].node).unwrap().data else {
        panic!("expected the bad call")
    };
    let argument = NodeRef::new(parsed.arena.id(), FILE, bad_call.arguments.nodes[0]);
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(diagnostic.node, Some(argument));
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'boolean' is not assignable to parameter of type 'string'.",
    );
    assert_replay(&mut context, &parsed, &calls, &[&declared]);
}

#[test]
fn generic_interface_overloads_keep_original_parameter_notes_for_arity_errors() {
    let source = concat!(
        "interface Recovery<T> { (text: T): T; (count: number): T; }\n",
        "declare const recovery: Recovery<string>;\n",
        "recovery('ready');\n",
        "recovery();\n",
        "recovery('ready', true);\n",
    );
    let parsed = parse_source_file(source);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 3);
    let declared = declared_overloads(
        &mut context,
        &parsed,
        nodes(&parsed, SyntaxKind::InterfaceDeclaration)[0],
    );
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let instance = context
        .get_type_at_location(callee(&parsed, calls[0]))
        .unwrap();
    let copies = specialized_signatures(&mut context, &declared, instance, string);
    for &call in &calls {
        assert_eq!(signature(&context, call), copies[0]);
        assert_eq!(context.get_type_at_location(call), Ok(string));
    }
    let [missing, extra] = context.diagnostics().as_slice() else {
        panic!("expected the missing and extra argument diagnostics")
    };
    assert_eq!(missing.diagnostic.code(), 2554);
    assert_eq!(missing.node, Some(callee(&parsed, calls[1])));
    assert_eq!(missing.range_override, None);
    assert_eq!(
        missing.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 0."
    );
    let [related] = missing.related_information.as_slice() else {
        panic!("the missing argument must identify the original first-overload parameter")
    };
    let parameter = nodes(&parsed, SyntaxKind::Parameter)[0];
    assert_eq!(related.diagnostic.code(), 6210);
    assert_eq!(related.node, Some(parameter));
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument for 'text' was not provided."
    );
    assert_eq!(extra.diagnostic.code(), 2554);
    assert_eq!(extra.node, Some(calls[2]));
    assert_eq!(
        extra.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 2."
    );
    assert!(extra.related_information.is_empty());
    let range = extra.range_override.unwrap().range();
    assert_eq!(
        &source[usize::try_from(range.start.get()).unwrap()
            ..usize::try_from(range.end.get()).unwrap()],
        "true",
    );
    assert_replay(&mut context, &parsed, &calls, &[&declared]);
}

#[test]
fn generic_interface_overloads_keep_multiple_argument_failures_unselected() {
    let parsed = parse_source_file(concat!(
        "interface Choice<T> { (value: T): T; (value: number): T; }\n",
        "declare const choose: Choice<string>;\n",
        "const good: string = choose('ready');\n",
        "choose(true);\n",
    ));
    let mut context = context(&parsed);
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 2);
    let error = SourceCheckError::Call(calls[1]);
    assert_eq!(context.check_source_file(FILE), Err(error));
    assert!(context.diagnostics().is_empty());
    let declared = declared_overloads(
        &mut context,
        &parsed,
        nodes(&parsed, SyntaxKind::InterfaceDeclaration)[0],
    );
    let variable = nodes(&parsed, SyntaxKind::VariableDeclaration)[0];
    let NodeData::VariableDeclaration(variable) = &parsed.arena.get(variable.node).unwrap().data
    else {
        panic!("expected the ambient callable declaration")
    };
    let annotation = NodeRef::new(parsed.arena.id(), FILE, variable.type_.unwrap());
    let instance = context.get_type_from_type_node(annotation).unwrap();
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let copies = specialized_signatures(&mut context, &declared, instance, string);
    assert_eq!(signature(&context, calls[0]), copies[0]);
    assert_eq!(
        context
            .store()
            .type_node_links(calls[0])
            .unwrap()
            .resolved_type,
        Some(string),
    );
    assert!(context.store().signature_links(calls[1]).is_none());
    assert!(context.store().type_node_links(calls[1]).is_none());
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        (
            counts(context),
            context.diagnostics().clone(),
            context.store().type_node_links(calls[0]).cloned(),
            context.store().signature_links(calls[0]).cloned(),
            context.store().type_node_links(annotation).cloned(),
            context
                .store()
                .type_payload(instance)
                .unwrap()
                .data()
                .structured()
                .cloned(),
        )
    };
    let warm = snapshot(&context);
    for _ in 0..2 {
        assert_eq!(context.check_source_file(FILE), Err(error));
        assert_eq!(context.get_type_from_type_node(annotation), Ok(instance));
        assert_eq!(
            specialized_signatures(&mut context, &declared, instance, string),
            copies
        );
        assert_eq!(signature(&context, calls[0]), copies[0]);
        assert!(context.store().signature_links(calls[1]).is_none());
        assert!(context.store().type_node_links(calls[1]).is_none());
        assert_eq!(snapshot(&context), warm);
    }
}
