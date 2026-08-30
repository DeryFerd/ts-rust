use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    TypeData, TypeId, signatures::SignatureFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(5_840);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/constructor-overloads.ts\""),
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
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn source_nodes(parsed: &ParseResult, kind: SyntaxKind) -> Vec<NodeRef> {
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

fn bound_symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn signature_at(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the source node must retain its exact signature")
}

fn construct_signatures(context: &CanonicalCheckerContext<'_>, value: TypeId) -> Vec<SignatureId> {
    let TypeData::Object(object) = context.store().type_payload(value).unwrap().data() else {
        panic!("the class value must retain its object record")
    };
    assert_eq!(object.structured.call_signature_count, 0);
    object
        .structured
        .signatures
        .clone()
        .expect("the class value must retain its construct signatures")
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 5] {
    let store = context.store();
    [
        store.type_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn assert_stable_replay(context: &mut CanonicalCheckerContext<'_>, nodes: &[NodeRef]) {
    let before = counts(context);
    let diagnostics = context.diagnostics().clone();
    let links = nodes
        .iter()
        .map(|&node| {
            (
                context.store().type_node_links(node).cloned(),
                context.store().signature_links(node).cloned(),
            )
        })
        .collect::<Vec<_>>();

    context.recheck_source_file(FILE).unwrap();

    assert_eq!(counts(context), before);
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(
        nodes
            .iter()
            .map(|&node| {
                (
                    context.store().type_node_links(node).cloned(),
                    context.store().signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        links
    );
}

// Pinned Go getSignaturesOfSymbol keeps the written order and omits the adjacent body.
#[test]
#[allow(clippy::too_many_lines)] // Both query orders check one complete source signature group.
fn constructor_overloads_keep_source_order_and_select_exact_class_signatures() {
    let parsed = parse_source_file(concat!(
        "class Model {\n",
        "  constructor(value: string);\n",
        "  constructor(value: number);\n",
        "  constructor(value: string | number) {}\n",
        "}\n",
        "const text = new Model('ready');\n",
        "const count = new Model(2);\n",
    ));
    let classes = source_nodes(&parsed, SyntaxKind::ClassDeclaration);
    let [class] = classes.as_slice() else {
        panic!("the source must contain one class")
    };
    let constructors = source_nodes(&parsed, SyntaxKind::Constructor);
    let [string_constructor, number_constructor, implementation] = constructors.as_slice() else {
        panic!("the source must retain two overloads and one implementation")
    };
    let constructions = source_nodes(&parsed, SyntaxKind::NewExpression);
    let [string_new, number_new] = constructions.as_slice() else {
        panic!("the source must contain two constructions")
    };

    for members_first in [false, true] {
        let mut context = context(&parsed);
        let owner = bound_symbol(&context, *class);
        let constructor_owner = bound_symbol(&context, *string_constructor);
        assert_eq!(
            context
                .store()
                .symbol(constructor_owner)
                .unwrap()
                .declarations(),
            Some(constructors.as_slice())
        );
        assert!(
            constructors
                .iter()
                .all(|&node| bound_symbol(&context, node) == constructor_owner)
        );
        let prepared = members_first.then(|| context.get_nongeneric_class_members(owner).unwrap());

        context.check_source_file(FILE).unwrap();

        assert!(context.diagnostics().is_empty());
        let members = context.get_nongeneric_class_members(owner).unwrap();
        if let Some(prepared) = prepared {
            assert_eq!(prepared, members);
        }
        let shells = members.shells();
        assert_eq!(shells.symbol(), owner);
        assert_eq!(shells.declaration(), *class);
        assert_ne!(shells.instance_type(), shells.value_type());
        let signatures = constructors
            .iter()
            .map(|&node| signature_at(&context, node))
            .collect::<Vec<_>>();
        assert_eq!(
            construct_signatures(&context, shells.value_type()),
            signatures[..2]
        );
        assert_ne!(signatures[0], signatures[1]);
        assert!(!signatures[..2].contains(&signatures[2]));
        for (&declaration, &signature) in constructors.iter().zip(&signatures) {
            let record = context.store().signature(signature).unwrap();
            assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
            assert_eq!(record.declaration(), Some(declaration));
            assert_eq!(record.resolved_return_type(), Some(shells.instance_type()));
            assert!(record.type_parameters().is_empty());
            assert!(record.target().is_none());
            assert!(record.mapper().is_none());
            assert_eq!(record.min_argument_count(), 1);
            let NodeData::ConstructorDeclaration(source) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("the source node must be a constructor declaration")
            };
            let parameters = source
                .parameters
                .nodes
                .iter()
                .map(|&node| bound_symbol(&context, NodeRef::new(parsed.arena.id(), FILE, node)))
                .collect::<Vec<_>>();
            assert_eq!(record.parameters(), parameters.as_slice());
            assert_eq!(source.body.is_some(), declaration == *implementation);
        }
        for (node, declaration) in [
            (*string_new, *string_constructor),
            (*number_new, *number_constructor),
        ] {
            assert_eq!(
                signature_at(&context, node),
                signature_at(&context, declaration)
            );
            assert_eq!(
                context.get_type_at_location(node).unwrap(),
                shells.instance_type()
            );
            let NodeData::NewExpression(expression) = &parsed.arena.get(node.node).unwrap().data
            else {
                panic!("the source node must be a new expression")
            };
            assert_eq!(
                context
                    .get_type_at_location(NodeRef::new(
                        parsed.arena.id(),
                        FILE,
                        expression.expression
                    ))
                    .unwrap(),
                shells.value_type()
            );
        }
        let mut replay = constructors.clone();
        replay.extend_from_slice(&constructions);
        assert_stable_replay(&mut context, &replay);
        assert_eq!(
            context.get_nongeneric_class_members(owner).unwrap(),
            members
        );
        assert_eq!(
            construct_signatures(&context, shells.value_type()),
            signatures[..2]
        );
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Wrong type and missing argument share the hidden implementation.
fn constructor_implementation_parameters_do_not_become_public_overloads() {
    let parsed = parse_source_file(concat!(
        "class Model {\n",
        "  constructor(value: string);\n",
        "  constructor(value?: string | number) {}\n",
        "}\n",
        "const valid = new Model('ready');\n",
        "const wrong = new Model(1);\n",
        "const missing = new Model();\n",
    ));
    let mut context = context(&parsed);
    let classes = source_nodes(&parsed, SyntaxKind::ClassDeclaration);
    let [class] = classes.as_slice() else {
        panic!("the source must contain one class")
    };
    let owner = bound_symbol(&context, *class);
    let constructors = source_nodes(&parsed, SyntaxKind::Constructor);
    let [overload, implementation] = constructors.as_slice() else {
        panic!("the source must retain one overload and one implementation")
    };
    let constructions = source_nodes(&parsed, SyntaxKind::NewExpression);
    let [_, wrong, missing] = constructions.as_slice() else {
        panic!("the source must contain one valid and two invalid constructions")
    };

    context.check_source_file(FILE).unwrap();

    let members = context.get_nongeneric_class_members(owner).unwrap();
    let overload_signature = signature_at(&context, *overload);
    let implementation_signature = signature_at(&context, *implementation);
    assert_ne!(overload_signature, implementation_signature);
    assert_eq!(
        construct_signatures(&context, members.shells().value_type()),
        [overload_signature]
    );
    assert_eq!(
        context
            .store()
            .signature(overload_signature)
            .unwrap()
            .min_argument_count(),
        1
    );
    assert_eq!(
        context
            .store()
            .signature(implementation_signature)
            .unwrap()
            .min_argument_count(),
        0
    );
    let [argument, arity] = context.diagnostics().as_slice() else {
        panic!("the hidden implementation must not accept either invalid construction")
    };
    assert_eq!(argument.diagnostic.code(), 2345);
    assert_eq!(
        argument.diagnostic.render().unwrap(),
        "Argument of type 'number' is not assignable to parameter of type 'string'."
    );
    let NodeData::NewExpression(wrong_expression) = &parsed.arena.get(wrong.node).unwrap().data
    else {
        panic!("the wrong construction must retain its new expression")
    };
    let wrong_argument = wrong_expression.arguments.as_ref().unwrap().nodes[0];
    assert_eq!(
        argument.node,
        Some(NodeRef::new(parsed.arena.id(), FILE, wrong_argument))
    );
    let [implementation_note] = argument.related_information.as_slice() else {
        panic!("the argument error must identify the hidden implementation that accepts it")
    };
    assert_eq!(implementation_note.diagnostic.code(), 2793);
    assert_eq!(implementation_note.node, Some(*implementation));
    assert_eq!(
        implementation_note.diagnostic.render().unwrap(),
        concat!(
            "The call would have succeeded against this implementation, ",
            "but implementation signatures of overloads are not externally visible."
        )
    );
    assert_eq!(arity.diagnostic.code(), 2554);
    assert_eq!(arity.node, Some(*missing));
    assert_eq!(
        arity.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 0."
    );
    let [related] = arity.related_information.as_slice() else {
        panic!("the missing argument must identify the public overload parameter")
    };
    assert_eq!(related.diagnostic.code(), 6210);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument for 'value' was not provided."
    );
    for &construction in &constructions {
        assert_eq!(signature_at(&context, construction), overload_signature);
        assert_eq!(
            context.get_type_at_location(construction).unwrap(),
            members.shells().instance_type()
        );
    }
    let mut replay = constructors;
    replay.extend_from_slice(&constructions);
    assert_stable_replay(&mut context, &replay);
}

// The pinned constructorsWithSpecializedSignatures baseline stops at the first mismatch.
#[test]
fn incompatible_constructor_implementation_reports_the_first_mismatch_and_body() {
    let parsed = parse_source_file(concat!(
        "class Model {\n",
        "  constructor(value: number);\n",
        "  constructor(value: string);\n",
        "  constructor(value: boolean);\n",
        "  constructor(value: number) {}\n",
        "}\n",
    ));
    let mut context = context(&parsed);
    let classes = source_nodes(&parsed, SyntaxKind::ClassDeclaration);
    let [class] = classes.as_slice() else {
        panic!("the source must contain one class")
    };
    let owner = bound_symbol(&context, *class);
    let constructors = source_nodes(&parsed, SyntaxKind::Constructor);
    let [_, incompatible, _, implementation] = constructors.as_slice() else {
        panic!("the source must retain three overloads and one implementation")
    };

    context.check_source_file(FILE).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("only the first incompatible overload must produce a diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2394);
    assert_eq!(diagnostic.node, Some(*incompatible));
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "This overload signature is not compatible with its implementation signature."
    );
    let [related] = diagnostic.related_information.as_slice() else {
        panic!("the compatibility diagnostic must identify the real implementation")
    };
    assert_eq!(related.diagnostic.code(), 2750);
    assert_eq!(related.node, Some(*implementation));
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "The implementation signature is declared here."
    );
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let signatures = constructors
        .iter()
        .map(|&node| signature_at(&context, node))
        .collect::<Vec<_>>();
    assert_eq!(
        construct_signatures(&context, members.shells().value_type()),
        signatures[..3]
    );
    assert!(!signatures[..3].contains(&signatures[3]));
    assert_stable_replay(&mut context, &constructors);
}

#[test]
fn constructor_compatibility_diagnostic_keeps_mixed_body_source_order() {
    let parsed = parse_source_file(concat!(
        "class Model {\n",
        "  before(): number { return 'wrong'; }\n",
        "  constructor(value: string);\n",
        "  constructor(value: number) { const later: string = value; }\n",
        "}\n",
    ));
    let mut context = context(&parsed);
    let methods = source_nodes(&parsed, SyntaxKind::MethodDeclaration);
    let [method] = methods.as_slice() else {
        panic!("the source must contain one ordinary method before the constructor group")
    };
    let constructors = source_nodes(&parsed, SyntaxKind::Constructor);
    let [overload, implementation] = constructors.as_slice() else {
        panic!("the source must retain one overload and one implementation")
    };

    context.check_source_file(FILE).unwrap();

    let [method_error, compatibility, constructor_error] = context.diagnostics().as_slice() else {
        panic!("the source must retain both body errors and the overload compatibility error")
    };
    assert_eq!(
        [
            method_error.diagnostic.code(),
            compatibility.diagnostic.code(),
            constructor_error.diagnostic.code(),
        ],
        [2322, 2394, 2322]
    );
    assert_eq!(compatibility.node, Some(*overload));
    let [related] = compatibility.related_information.as_slice() else {
        panic!("the compatibility diagnostic must retain its implementation note")
    };
    assert_eq!(related.diagnostic.code(), 2750);
    assert_eq!(related.node, Some(*implementation));
    for (diagnostic, declaration) in [
        (method_error, *method),
        (constructor_error, *implementation),
    ] {
        let node = diagnostic
            .node
            .expect("a body error must retain its source node");
        let range = parsed.arena.get(node.node).unwrap().range;
        let owner_range = parsed.arena.get(declaration.node).unwrap().range;
        assert!(owner_range.start <= range.start && range.end <= owner_range.end);
    }
    let mut replay = methods;
    replay.extend_from_slice(&constructors);
    replay.extend(source_nodes(&parsed, SyntaxKind::VariableDeclaration));
    assert_stable_replay(&mut context, &replay);
}

#[test]
#[allow(clippy::too_many_lines)] // Both entry orders share one constructor and tuple-method source.
fn constructor_member_queries_prepare_tuple_methods_before_source_checking() {
    let parsed = parse_source_file(concat!(
        "class Model {\n",
        "  constructor(value: string);\n",
        "  constructor(value: number);\n",
        "  constructor(value: any) {}\n",
        "  first(pair: [number, string]): number { return pair[0]; }\n",
        "}\n",
        "declare const pair: [number, string];\n",
        "const model = new Model(1);\n",
        "const result: number = model.first(pair);\n",
    ));
    let classes = source_nodes(&parsed, SyntaxKind::ClassDeclaration);
    let [class] = classes.as_slice() else {
        panic!("the source must contain one class")
    };
    let constructors = source_nodes(&parsed, SyntaxKind::Constructor);
    assert_eq!(constructors.len(), 3);
    let methods = source_nodes(&parsed, SyntaxKind::MethodDeclaration);
    let [method] = methods.as_slice() else {
        panic!("the class must retain one tuple method")
    };
    let NodeData::MethodDeclaration(method_data) = &parsed.arena.get(method.node).unwrap().data
    else {
        unreachable!()
    };
    let parameter = NodeRef::new(parsed.arena.id(), FILE, method_data.parameters.nodes[0]);
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        unreachable!()
    };
    let annotation = NodeRef::new(parsed.arena.id(), FILE, parameter_data.type_.unwrap());
    let constructions = source_nodes(&parsed, SyntaxKind::NewExpression);
    let calls = source_nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(constructions.len(), 1);
    assert_eq!(calls.len(), 1);

    for members_first in [false, true] {
        let mut context = context(&parsed);
        let owner = bound_symbol(&context, *class);
        let prepared = members_first.then(|| {
            let members = context.get_nongeneric_class_members(owner).unwrap();
            let before = counts(&context);
            assert_eq!(
                context.get_nongeneric_class_members(owner).unwrap(),
                members
            );
            assert_eq!(counts(&context), before);
            members
        });

        context.check_source_file(FILE).unwrap();

        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let members = context.get_nongeneric_class_members(owner).unwrap();
        if let Some(prepared) = prepared {
            assert_eq!(members, prepared);
        }
        let signatures = constructors
            .iter()
            .map(|&node| signature_at(&context, node))
            .collect::<Vec<_>>();
        assert_eq!(
            construct_signatures(&context, members.shells().value_type()),
            signatures[..2]
        );
        assert!(!signatures[..2].contains(&signatures[2]));
        assert_eq!(signature_at(&context, constructions[0]), signatures[1]);
        assert_eq!(
            context.get_type_at_location(constructions[0]).unwrap(),
            members.shells().instance_type(),
        );
        let tuple = context.get_type_from_type_node(annotation).unwrap();
        let parameter_symbol = bound_symbol(&context, parameter);
        assert_eq!(
            context
                .store()
                .value_symbol_links(parameter_symbol)
                .unwrap()
                .resolved_type,
            Some(tuple),
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let TypeData::TypeReference(reference) =
            context.store().type_payload(tuple).unwrap().data()
        else {
            panic!("the method parameter must keep its canonical tuple reference")
        };
        assert_eq!(
            reference.resolved_type_arguments.as_deref(),
            Some(&[number, string][..])
        );
        assert!(matches!(
            context
                .store()
                .type_payload(reference.object.target.unwrap())
                .unwrap()
                .data(),
            TypeData::Tuple(_),
        ));
        let method_signature = signature_at(&context, *method);
        assert_eq!(
            context
                .store()
                .signature(method_signature)
                .unwrap()
                .parameters(),
            &[parameter_symbol]
        );
        assert_eq!(signature_at(&context, calls[0]), method_signature);
        assert_eq!(context.get_type_at_location(calls[0]).unwrap(), number);
        let mut replay = constructors.clone();
        replay.extend([*method, annotation, constructions[0], calls[0]]);
        assert_stable_replay(&mut context, &replay);
        let before = counts(&context);
        assert_eq!(
            context.get_nongeneric_class_members(owner).unwrap(),
            members
        );
        assert_eq!(counts(&context), before);
    }
}

#[test]
fn constructor_extra_arguments_use_the_argument_range_without_implementation_note() {
    let source = concat!(
        "class Model {\n",
        "  constructor();\n",
        "  constructor(value?: number) {}\n",
        "}\n",
        "new Model(1);\n",
    );
    let parsed = parse_source_file(source);
    let mut context = context(&parsed);
    let classes = source_nodes(&parsed, SyntaxKind::ClassDeclaration);
    let [class] = classes.as_slice() else {
        panic!("the source must contain one class")
    };
    let owner = bound_symbol(&context, *class);
    let constructors = source_nodes(&parsed, SyntaxKind::Constructor);
    let [overload, implementation] = constructors.as_slice() else {
        panic!("the source must retain one overload and one implementation")
    };
    let constructions = source_nodes(&parsed, SyntaxKind::NewExpression);
    let [construction] = constructions.as_slice() else {
        panic!("the source must contain one construction")
    };

    context.check_source_file(FILE).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the public zero-argument overload must reject the extra argument")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2554);
    assert_eq!(diagnostic.node, Some(*construction));
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Expected 0 arguments, but got 1."
    );
    assert!(diagnostic.related_information.is_empty());
    let NodeData::NewExpression(expression) = &parsed.arena.get(construction.node).unwrap().data
    else {
        panic!("the construction must retain its new expression")
    };
    let argument = expression.arguments.as_ref().unwrap().nodes[0];
    let range = diagnostic
        .range_override
        .expect("the extra argument must have its own diagnostic range")
        .range();
    assert_eq!(range, parsed.arena.get(argument).unwrap().range);
    assert_eq!(
        &source[range.start.get() as usize..range.end.get() as usize],
        "1"
    );
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let signature = signature_at(&context, *overload);
    assert_ne!(signature, signature_at(&context, *implementation));
    assert_eq!(
        construct_signatures(&context, members.shells().value_type()),
        [signature]
    );
    assert_eq!(signature_at(&context, *construction), signature);
    assert_eq!(
        context.get_type_at_location(*construction).unwrap(),
        members.shells().instance_type()
    );
    let mut replay = constructors;
    replay.extend_from_slice(&constructions);
    assert_stable_replay(&mut context, &replay);
}
