use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, InternalSymbolName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SignatureId, TypeData, TypeId,
    signatures::{ElementFlags, SignatureFlags},
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_960);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/handler-call-signatures.ts\""),
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

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .unwrap()
        .resolved_signature
        .signature()
        .expect("the source declaration or call must retain its signature")
}

fn pair_type(context: &CanonicalCheckerContext<'_>, type_: TypeId, element: TypeId) -> TypeId {
    let store = context.store();
    let TypeData::TypeReference(reference) = store.type_payload(type_).unwrap().data() else {
        panic!("the rest parameter must retain its tuple reference")
    };
    assert_eq!(
        reference.resolved_type_arguments.as_deref(),
        Some(&[element, element][..]),
    );
    let target = reference.object.target.unwrap();
    let TypeData::Tuple(tuple) = store.type_payload(target).unwrap().data() else {
        panic!("the rest parameter must target a tuple")
    };
    assert_eq!(tuple.metadata.element_flags(), [ElementFlags::REQUIRED; 2]);
    assert_eq!(tuple.metadata.min_length(), 2);
    assert_eq!(tuple.metadata.fixed_length(), 2);
    assert!(!tuple.metadata.is_readonly());
    target
}

fn replay(
    context: &mut CanonicalCheckerContext<'_>,
    annotations: &[(NodeRef, TypeId)],
    values: &[(NodeRef, TypeId)],
    declarations: &[(SemanticSymbolId, TypeId)],
    signatures: &[(Option<NodeRef>, SignatureId, TypeId)],
) {
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        let store = context.store();
        (
            [
                store.type_len(),
                store.symbol_len(),
                store.signature_len(),
                store.mapper_len(),
                store.index_info_len(),
                store.symbol_store().symbol_table_len(),
            ],
            context.diagnostics().clone(),
            declarations
                .iter()
                .filter_map(|&(_, type_)| {
                    let record = store.type_payload(type_).unwrap();
                    let TypeData::TypeParameter(data) = record.data() else {
                        return None;
                    };
                    Some((type_, record.symbol(), data.clone()))
                })
                .collect::<Vec<_>>(),
            signatures
                .iter()
                .map(|&(_, signature, _)| {
                    let record = store.signature(signature).unwrap();
                    (
                        signature,
                        record.declaration(),
                        record.flags(),
                        record
                            .type_parameters()
                            .iter()
                            .map(|&type_| {
                                let parameter = store.type_payload(type_).unwrap();
                                let TypeData::TypeParameter(data) = parameter.data() else {
                                    panic!("signature formals must keep their canonical types")
                                };
                                (type_, parameter.symbol(), data.clone())
                            })
                            .collect::<Vec<_>>(),
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
        for &(node, expected) in annotations {
            assert_eq!(context.get_type_from_type_node(node), Ok(expected));
        }
        for &(node, expected) in values {
            assert_eq!(context.get_type_at_location(node), Ok(expected));
        }
        for &(owner, expected) in declarations {
            assert_eq!(context.get_declared_type_of_symbol(owner), Ok(expected));
        }
        for &(node, expected, return_type) in signatures {
            if let Some(node) = node {
                assert_eq!(signature(context, node), expected);
            }
            assert_eq!(
                context.get_return_type_of_signature(expected),
                Ok(return_type)
            );
        }
        context.recheck_source_file(FILE).unwrap();
        assert_eq!(snapshot(context), warm);
        assert!(context.store().type_resolution_is_empty());
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Check overload owners, copied formals, and replay together.
fn generic_handler_overloads_keep_call_formals_and_tuple_rest_signatures() {
    let parsed = parse_source_file(concat!(
        "interface Route<Outer> {\n",
        "  <Item extends Outer = Outer>(item: Item): Item;\n",
        "  <Item extends Outer = Outer>(...items: [Item, Item]): Item;\n",
        "  value: Outer;\n",
        "}\n",
        "declare const text: Route<string>;\n",
        "declare const numeric: Route<number>;\n",
        "text.value;\n",
        "numeric.value;\n",
    ));
    let interface = nodes(&parsed, SyntaxKind::InterfaceDeclaration)[0];
    let calls = nodes(&parsed, SyntaxKind::CallSignature);
    let formals = nodes(&parsed, SyntaxKind::TypeParameter);
    let parameters = nodes(&parsed, SyntaxKind::Parameter);
    let tuple = nodes(&parsed, SyntaxKind::TupleType)[0];
    let properties = nodes(&parsed, SyntaxKind::PropertyAccessExpression);
    assert_eq!(calls.len(), 2);
    assert_eq!(formals.len(), 3);
    assert_eq!(parameters.len(), 2);
    assert_eq!(properties.len(), 2);

    for query_first in [false, true] {
        let mut context = context(&parsed);
        let early = query_first.then(|| context.get_type_from_type_node(tuple).unwrap());
        context.check_source_file(FILE).unwrap();
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let interface_owner = symbol(&context, interface);
        let interface_type = context.get_declared_type_of_symbol(interface_owner).unwrap();
        let outer_owner = symbol(&context, formals[0]);
        let outer = context.get_declared_type_of_symbol(outer_owner).unwrap();
        let call_owner = symbol(&context, calls[0]);
        assert_eq!(symbol(&context, calls[1]), call_owner);
        assert_eq!(
            context.store().get_parent_of_symbol(call_owner),
            Some(interface_owner)
        );
        assert_eq!(
            context.store().get_parent_of_symbol(outer_owner),
            Some(interface_owner)
        );
        assert_eq!(
            context.store().symbol(call_owner).unwrap().declarations(),
            Some(calls.as_slice()),
        );
        let members = context
            .store()
            .symbol(interface_owner)
            .unwrap()
            .members()
            .unwrap();
        assert_eq!(
            context
                .store()
                .symbol_table(members)
                .unwrap()
                .get(InternalSymbolName::Call.as_ref()),
            Some(call_owner),
        );

        let mut annotations = Vec::new();
        let mut declarations = vec![(interface_owner, interface_type), (outer_owner, outer)];
        let mut signatures = Vec::new();
        let mut tuple_target = None;
        for index in 0..2 {
            let call = calls[index];
            let formal = formals[index + 1];
            let parameter = parameters[index];
            for child in [formal, parameter] {
                assert_eq!(
                    parsed.arena.get(child.node).unwrap().parent,
                    Some(call.node)
                );
            }
            let formal_owner = symbol(&context, formal);
            let inner = context.get_declared_type_of_symbol(formal_owner).unwrap();
            assert_ne!(formal_owner, outer_owner);
            assert_ne!(inner, outer);
            assert!(!declarations.iter().any(|&(_, type_)| type_ == inner));
            let locals = context.file(FILE).unwrap().1.locals(call).unwrap();
            assert_eq!(
                context.store().symbol_table(locals).unwrap().get_source("Item"),
                Some(formal_owner),
            );
            let TypeData::TypeParameter(data) =
                context.store().type_payload(inner).unwrap().data()
            else {
                panic!("the call formal must retain its canonical type")
            };
            assert_eq!(
                context.store().type_payload(inner).unwrap().symbol(),
                Some(formal_owner)
            );
            assert_eq!(data.constraint, Some(outer));
            assert_eq!(data.resolved_default_type, Some(outer));
            assert_eq!(data.target, None);
            assert_eq!(data.mapper, None);
            let NodeData::TypeParameterDeclaration(formal_data) =
                &parsed.arena.get(formal.node).unwrap().data
            else {
                panic!("expected a call-owned formal")
            };
            annotations.extend(
                [
                    formal_data.constraint.unwrap(),
                    formal_data.default_type.unwrap(),
                ]
                .map(|node| (NodeRef::new(parsed.arena.id(), FILE, node), outer)),
            );
            let parameter_owner = symbol(&context, parameter);
            let parameter_type = context
                .store()
                .value_symbol_links(parameter_owner)
                .unwrap()
                .resolved_type
                .unwrap();
            if index == 0 {
                assert_eq!(parameter_type, inner);
            } else {
                tuple_target = Some(pair_type(&context, parameter_type, inner));
                if let Some(early) = early {
                    assert_eq!(parameter_type, early);
                }
            }
            let NodeData::ParameterDeclaration(parameter_data) =
                &parsed.arena.get(parameter.node).unwrap().data
            else {
                panic!("expected a declared call parameter")
            };
            let NodeData::CallSignatureDeclaration(call_data) =
                &parsed.arena.get(call.node).unwrap().data
            else {
                panic!("expected a call signature")
            };
            annotations.extend([
                (
                    NodeRef::new(parsed.arena.id(), FILE, parameter_data.type_.unwrap()),
                    parameter_type,
                ),
                (
                    NodeRef::new(parsed.arena.id(), FILE, call_data.type_.unwrap()),
                    inner,
                ),
            ]);
            let signature = signature(&context, call);
            let record = context.store().signature(signature).unwrap();
            assert_eq!(record.declaration(), Some(call));
            assert_eq!(record.parameters(), [parameter_owner]);
            assert_eq!(record.type_parameters(), [inner]);
            assert_eq!(record.resolved_return_type(), Some(inner));
            assert_eq!(record.target(), None);
            assert_eq!(record.mapper(), None);
            assert_eq!(
                record.flags().contains(SignatureFlags::HAS_REST_PARAMETER),
                index == 1
            );
            assert_eq!(record.min_argument_count(), if index == 0 { 1 } else { 0 });
            declarations.push((formal_owner, inner));
            signatures.push((Some(call), signature, inner));
        }
        let TypeData::Interface(data) =
            context.store().type_payload(interface_type).unwrap().data()
        else {
            panic!("the source interface must retain its declared call set")
        };
        assert!(data.declared_members_resolved);
        assert_eq!(
            data.declared_call_signatures.as_deref(),
            Some(&[signatures[0].1, signatures[1].1][..])
        );
        let originals = signatures.clone();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let expected_types = [bootstrap.string_type, bootstrap.number_type];
        let mut values = Vec::new();
        let mut copies = Vec::new();
        for (&property, expected) in properties.iter().zip(expected_types) {
            let NodeData::PropertyAccessExpression(property_data) =
                &parsed.arena.get(property.node).unwrap().data
            else {
                panic!("the property read must demand the instance's members")
            };
            let receiver = NodeRef::new(parsed.arena.id(), FILE, property_data.expression);
            let instance = context.get_type_at_location(receiver).unwrap();
            assert_eq!(context.get_type_at_location(property), Ok(expected));
            let TypeData::TypeReference(reference) =
                context.store().type_payload(instance).unwrap().data()
            else {
                panic!("the receiver must retain its specialized interface type")
            };
            assert_eq!(reference.object.target, Some(interface_type));
            assert_eq!(
                reference.resolved_type_arguments.as_deref(),
                Some(&[expected][..])
            );
            assert_eq!(reference.object.structured.call_signature_count, 2);
            let instance_calls = reference.object.structured.signatures.clone().unwrap();
            assert_eq!(instance_calls.len(), 2);
            for (index, (&copied, &(_, original, inner))) in
                instance_calls.iter().zip(&originals).enumerate()
            {
                let store = context.store();
                let source = store.signature(original).unwrap();
                let copy = store.signature(copied).unwrap();
                assert_ne!(copied, original);
                assert_eq!(copy.target(), Some(original));
                assert_eq!(copy.declaration(), source.declaration());
                assert_eq!(copy.flags(), source.flags());
                assert_eq!(copy.min_argument_count(), source.min_argument_count());
                let [fresh] = copy.type_parameters() else {
                    panic!("each overload copy must keep one fresh call formal")
                };
                let fresh = *fresh;
                assert_ne!(fresh, inner);
                assert_ne!(fresh, outer);
                let mapper = copy.mapper().unwrap();
                let parameter = store.type_payload(fresh).unwrap();
                let TypeData::TypeParameter(data) = parameter.data() else {
                    panic!("the copied formal must keep its source owner and mapper")
                };
                assert_eq!(
                    parameter.symbol(),
                    store.type_payload(inner).unwrap().symbol()
                );
                assert_eq!(data.target, Some(inner));
                assert_eq!(data.mapper, Some(mapper));
                assert_eq!(data.constraint, Some(expected));
                assert_eq!(data.resolved_default_type, Some(expected));
                assert_eq!(copy.resolved_return_type(), Some(fresh));
                let [copied_parameter] = copy.parameters() else {
                    panic!("each copied overload must keep one value parameter")
                };
                let original_parameter = source.parameters()[0];
                assert_ne!(*copied_parameter, original_parameter);
                let links = store.value_symbol_links(*copied_parameter).unwrap();
                assert_eq!(links.target, Some(original_parameter));
                assert_eq!(links.mapper, Some(mapper));
                let parameter_type = links.resolved_type.unwrap();
                if index == 0 {
                    assert_eq!(parameter_type, fresh);
                } else {
                    assert_eq!(
                        Some(pair_type(&context, parameter_type, fresh)),
                        tuple_target
                    );
                }
                signatures.push((None, copied, fresh));
            }
            copies.push(instance_calls);
            values.extend([(receiver, instance), (property, expected)]);
        }
        assert_ne!(copies[0][0], copies[0][1]);
        assert_ne!(copies[0][0], copies[1][0]);
        assert_ne!(copies[0][1], copies[1][1]);
        replay(&mut context, &annotations, &values, &declarations, &signatures);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Check tuple substitutions, argument errors, and arity together.
fn generic_interface_tuple_rest_calls_keep_argument_diagnostics_and_replay() {
    let parsed = parse_source_file(concat!(
        "interface Pair<Outer> { (...items: [Outer, Outer]): Outer; }\n",
        "declare const text: Pair<string>;\n",
        "declare const numeric: Pair<number>;\n",
        "text('one', 'two');\n",
        "numeric(1, 2);\n",
        "text('one', 3);\n",
        "numeric(1, 'bad');\n",
        "text('one');\n",
    ));
    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    let declaration = nodes(&parsed, SyntaxKind::CallSignature)[0];
    let parameter = nodes(&parsed, SyntaxKind::Parameter)[0];
    let interface = nodes(&parsed, SyntaxKind::InterfaceDeclaration)[0];
    let formal = nodes(&parsed, SyntaxKind::TypeParameter)[0];
    assert_eq!(calls.len(), 5);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let outer_owner = symbol(&context, formal);
    let outer = context.get_declared_type_of_symbol(outer_owner).unwrap();
    let owner = symbol(&context, interface);
    let interface_type = context.get_declared_type_of_symbol(owner).unwrap();
    let original = signature(&context, declaration);
    let parameter_owner = symbol(&context, parameter);
    let parameter_type = context
        .store()
        .value_symbol_links(parameter_owner)
        .unwrap()
        .resolved_type
        .unwrap();
    let tuple_target = pair_type(&context, parameter_type, outer);
    let original_record = context.store().signature(original).unwrap();
    assert_eq!(original_record.flags(), SignatureFlags::HAS_REST_PARAMETER);
    assert_eq!(original_record.parameters(), [parameter_owner]);
    assert!(original_record.type_parameters().is_empty());
    assert_eq!(original_record.min_argument_count(), 0);
    assert_eq!(original_record.target(), None);
    assert_eq!(original_record.mapper(), None);
    assert_eq!(original_record.resolved_return_type(), Some(outer));
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let expected_types = [bootstrap.string_type, bootstrap.number_type];
    let mut values = Vec::new();
    let mut signatures = vec![(Some(declaration), original, outer)];
    let mut instances = Vec::new();
    let mut selected = Vec::new();
    for (index, &call) in calls.iter().enumerate() {
        let expected = expected_types[index % 2];
        assert_eq!(context.get_type_at_location(call), Ok(expected));
        let NodeData::CallExpression(call_data) = &parsed.arena.get(call.node).unwrap().data else {
            panic!("expected a tuple-rest call")
        };
        let callee = NodeRef::new(parsed.arena.id(), FILE, call_data.expression);
        let instance = context.get_type_at_location(callee).unwrap();
        let copied = signature(&context, call);
        let store = context.store();
        let TypeData::TypeReference(reference) = store.type_payload(instance).unwrap().data() else {
            panic!("the callee must keep its specialized interface type")
        };
        assert_eq!(reference.object.target, Some(interface_type));
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(&[expected][..])
        );
        assert_eq!(reference.object.structured.call_signature_count, 1);
        assert_eq!(
            reference.object.structured.signatures.as_deref(),
            Some(&[copied][..])
        );
        let record = store.signature(copied).unwrap();
        assert_ne!(copied, original);
        assert_eq!(record.declaration(), Some(declaration));
        assert_eq!(record.target(), Some(original));
        assert_eq!(record.flags(), SignatureFlags::HAS_REST_PARAMETER);
        assert!(record.type_parameters().is_empty());
        assert_eq!(record.resolved_return_type(), Some(expected));
        let [copied_parameter] = record.parameters() else {
            panic!("the copied signature must keep one rest parameter")
        };
        assert_ne!(*copied_parameter, parameter_owner);
        let links = store.value_symbol_links(*copied_parameter).unwrap();
        assert_eq!(links.target, Some(parameter_owner));
        assert_eq!(links.mapper, record.mapper());
        assert_eq!(
            pair_type(&context, links.resolved_type.unwrap(), expected),
            tuple_target
        );
        values.extend([(callee, instance), (call, expected)]);
        signatures.push((Some(call), copied, expected));
        instances.push(instance);
        selected.push(copied);
    }
    assert_eq!(instances[0], instances[2]);
    assert_eq!(instances[0], instances[4]);
    assert_eq!(instances[1], instances[3]);
    assert_ne!(instances[0], instances[1]);
    assert_eq!(selected[0], selected[2]);
    assert_eq!(selected[0], selected[4]);
    assert_eq!(selected[1], selected[3]);
    assert_ne!(selected[0], selected[1]);

    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 3, "{diagnostics:?}");
    for ((diagnostic, &call), message) in
        diagnostics[..2].iter().zip(&calls[2..4]).zip([
            "Argument of type 'number' is not assignable to parameter of type 'string'.",
            "Argument of type 'string' is not assignable to parameter of type 'number'.",
        ])
    {
        let NodeData::CallExpression(call) = &parsed.arena.get(call.node).unwrap().data else {
            panic!("expected a bad tuple-rest call")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2345);
        assert_eq!(
            diagnostic.node,
            Some(NodeRef::new(parsed.arena.id(), FILE, call.arguments.nodes[1]))
        );
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
    }
    let missing = &diagnostics[2];
    let NodeData::CallExpression(missing_call) = &parsed.arena.get(calls[4].node).unwrap().data
    else {
        panic!("expected the short tuple-rest call")
    };
    assert_eq!(missing.diagnostic.code(), 2554);
    assert_eq!(
        missing.node,
        Some(NodeRef::new(parsed.arena.id(), FILE, missing_call.expression))
    );
    assert_eq!(missing.range_override, None);
    assert!(missing.related_information.is_empty());
    assert_eq!(
        missing.diagnostic.render().unwrap(),
        "Expected 2 arguments, but got 1."
    );
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        panic!("expected the original tuple-rest parameter")
    };
    replay(
        &mut context,
        &[(
            NodeRef::new(parsed.arena.id(), FILE, parameter_data.type_.unwrap()),
            parameter_type,
        )],
        &values,
        &[(owner, interface_type), (outer_owner, outer)],
        &signatures,
    );
}

#[test]
fn generic_tuple_rest_call_defaults_keep_the_written_constraint_error() {
    let parsed = parse_source_file(concat!(
        "interface Route<Outer> {\n",
        "  <Item extends string = number>(...items: [Item, Item]): Outer;\n",
        "}\n",
    ));
    let call = nodes(&parsed, SyntaxKind::CallSignature)[0];
    let formals = nodes(&parsed, SyntaxKind::TypeParameter);
    let tuple = nodes(&parsed, SyntaxKind::TupleType)[0];
    let NodeData::TypeParameterDeclaration(formal) =
        &parsed.arena.get(formals[1].node).unwrap().data
    else {
        panic!("expected the call's own type parameter")
    };
    let constraint = NodeRef::new(parsed.arena.id(), FILE, formal.constraint.unwrap());
    let default_type = NodeRef::new(parsed.arena.id(), FILE, formal.default_type.unwrap());
    for query_first in [false, true] {
        let mut context = context(&parsed);
        if query_first {
            context.get_type_from_type_node(tuple).unwrap();
            assert!(context.diagnostics().is_empty());
        }
        context.check_source_file(FILE).unwrap();
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("expected one written default constraint error")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2344);
        assert_eq!(diagnostic.node, Some(default_type));
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type 'number' does not satisfy the constraint 'string'."
        );
        let owners = formals
            .iter()
            .map(|&formal| symbol(&context, formal))
            .collect::<Vec<_>>();
        let outer = context.get_declared_type_of_symbol(owners[0]).unwrap();
        let inner = context.get_declared_type_of_symbol(owners[1]).unwrap();
        assert_ne!(outer, inner);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let string = bootstrap.string_type;
        let number = bootstrap.number_type;
        let TypeData::TypeParameter(data) = context.store().type_payload(inner).unwrap().data()
        else {
            panic!("the invalid default must not replace its formal type")
        };
        assert_eq!(
            context.store().type_payload(inner).unwrap().symbol(),
            Some(owners[1])
        );
        assert_eq!(data.constraint, Some(string));
        assert_eq!(data.resolved_default_type, Some(number));
        assert_eq!(data.target, None);
        assert_eq!(data.mapper, None);
        let tuple_type = context.get_type_from_type_node(tuple).unwrap();
        pair_type(&context, tuple_type, inner);
        let signature = signature(&context, call);
        let record = context.store().signature(signature).unwrap();
        assert_eq!(record.type_parameters(), [inner]);
        assert_eq!(record.flags(), SignatureFlags::HAS_REST_PARAMETER);
        assert_eq!(record.resolved_return_type(), Some(outer));
        replay(
            &mut context,
            &[(constraint, string), (default_type, number), (tuple, tuple_type)],
            &[],
            &[(owners[0], outer), (owners[1], inner)],
            &[(Some(call), signature, outer)],
        );
    }
}
