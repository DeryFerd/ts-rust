use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, ClassMembers, IntrinsicBootstrapOptions,
    SignatureId, TypeData, TypeId, signatures::SignatureFlags, types::ObjectFlags,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(5_850);
const LIBRARY_FILE: FileId = FileId::new(5_851);
const ARRAY_LIBRARY: &str = "interface Array<T> {} interface ReadonlyArray<T> {}";

fn context<'arena>(
    library: &'arena ParseResult,
    parsed: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let mut binder = CanonicalBinder::new();
    for (parsed, file, path) in [
        (library, LIBRARY_FILE, "\"/project/lib.d.ts\""),
        (parsed, FILE, "\"/project/class-construction.ts\""),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        vec![(LIBRARY_FILE, &library.arena), (FILE, &parsed.arena)],
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

fn new_arguments(parsed: &ParseResult, node: NodeRef) -> Vec<NodeRef> {
    let NodeData::NewExpression(expression) = &parsed.arena.get(node.node).unwrap().data else {
        panic!("the construction must retain its new expression")
    };
    expression
        .arguments
        .as_ref()
        .unwrap()
        .nodes
        .iter()
        .map(|&node| NodeRef::new(parsed.arena.id(), FILE, node))
        .collect()
}

fn assert_construction_identity(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    constructions: &[NodeRef],
) -> ClassMembers {
    let classes = source_nodes(parsed, SyntaxKind::ClassDeclaration);
    let [class] = classes.as_slice() else {
        panic!("the source must contain one class")
    };
    let constructors = source_nodes(parsed, SyntaxKind::Constructor);
    let [constructor] = constructors.as_slice() else {
        panic!("the source must contain one explicit constructor")
    };
    let owner = bound_symbol(context, *class);
    let constructor_owner = bound_symbol(context, *constructor);
    assert_eq!(
        context
            .store()
            .symbol(constructor_owner)
            .unwrap()
            .declarations(),
        Some(constructors.as_slice())
    );
    let members = context.get_nongeneric_class_members(owner).unwrap();
    let shells = members.shells();
    assert_eq!(shells.symbol(), owner);
    assert_eq!(shells.declaration(), *class);
    assert_ne!(shells.instance_type(), shells.value_type());
    let signature = signature_at(context, *constructor);
    assert_eq!(members.default_construct_signature(), signature);
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(*constructor));
    assert_eq!(record.flags(), SignatureFlags::CONSTRUCT);
    assert_eq!(record.resolved_return_type(), Some(shells.instance_type()));
    assert_eq!(record.min_argument_count(), 1);
    assert!(record.type_parameters().is_empty());
    assert!(record.target().is_none());
    assert!(record.mapper().is_none());
    let NodeData::ConstructorDeclaration(source) =
        &parsed.arena.get(constructor.node).unwrap().data
    else {
        panic!("the signature must retain its real constructor declaration")
    };
    assert!(source.body.is_some());
    let parameters = source
        .parameters
        .nodes
        .iter()
        .map(|&node| bound_symbol(context, NodeRef::new(parsed.arena.id(), FILE, node)))
        .collect::<Vec<_>>();
    assert_eq!(record.parameters(), parameters.as_slice());
    let TypeData::Object(value) = context
        .store()
        .type_payload(shells.value_type())
        .unwrap()
        .data()
    else {
        panic!("the class value must retain its object record")
    };
    assert_eq!(value.structured.call_signature_count, 0);
    assert_eq!(
        value.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    for &construction in constructions {
        assert_eq!(signature_at(context, construction), signature);
        assert_eq!(
            context.get_type_at_location(construction).unwrap(),
            shells.instance_type()
        );
        let NodeData::NewExpression(expression) =
            &parsed.arena.get(construction.node).unwrap().data
        else {
            panic!("the source must retain its new expression")
        };
        assert_eq!(
            context
                .get_type_at_location(NodeRef::new(parsed.arena.id(), FILE, expression.expression))
                .unwrap(),
            shells.value_type()
        );
    }
    members
}

fn array_element(context: &CanonicalCheckerContext<'_>, array: TypeId) -> TypeId {
    let TypeData::TypeReference(reference) = context.store().type_payload(array).unwrap().data()
    else {
        panic!("the array must retain its canonical type reference")
    };
    assert_eq!(
        reference.object.target,
        Some(context.global_types().array_type)
    );
    let [element] = reference.resolved_type_arguments.as_deref().unwrap() else {
        panic!("the array must retain one element type")
    };
    *element
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

fn assert_stable_replay(context: &mut CanonicalCheckerContext<'_>, parsed: &ParseResult) {
    let snapshot = |context: &CanonicalCheckerContext<'_>| {
        parsed
            .arena
            .iter()
            .map(|(node, _)| {
                let node = NodeRef::new(parsed.arena.id(), FILE, node);
                (
                    context.store().type_node_links(node).cloned(),
                    context.store().signature_links(node).cloned(),
                    context.store().symbol_node_links(node).cloned(),
                    context.store().array_literal_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>()
    };
    let before = counts(context);
    let diagnostics = context.diagnostics().clone();
    let links = snapshot(context);

    context.recheck_source_file(FILE).unwrap();

    assert_eq!(counts(context), before);
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(snapshot(context), links);
}

#[test]
fn source_constructor_checks_identifier_and_binary_arguments_in_either_query_order() {
    let library = parse_source_file(ARRAY_LIBRARY);
    let parsed = parse_source_file(concat!(
        "class Model { constructor(value: number) { const copy: number = value; } }\n",
        "const input: number = 2;\n",
        "const direct = new Model(input);\n",
        "const sum = new Model(input + 1);\n",
    ));
    let class = source_nodes(&parsed, SyntaxKind::ClassDeclaration)[0];
    let constructions = source_nodes(&parsed, SyntaxKind::NewExpression);
    assert_eq!(constructions.len(), 2);

    for members_first in [false, true] {
        let mut context = context(&library, &parsed);
        let owner = bound_symbol(&context, class);
        let prepared = members_first.then(|| context.get_nongeneric_class_members(owner).unwrap());

        context.check_source_file(FILE).unwrap();

        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let members = assert_construction_identity(&mut context, &parsed, &constructions);
        if let Some(prepared) = prepared {
            assert_eq!(prepared, members);
        }
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        for &construction in &constructions {
            let arguments = new_arguments(&parsed, construction);
            let [argument] = arguments.as_slice() else {
                panic!("each construction must have one checked expression argument")
            };
            assert_eq!(context.get_type_at_location(*argument).unwrap(), number);
        }
        let [parameter] = context
            .store()
            .signature(members.default_construct_signature())
            .unwrap()
            .parameters()
        else {
            panic!("the constructor must retain its real parameter")
        };
        assert_eq!(
            context
                .store()
                .value_symbol_links(*parameter)
                .unwrap()
                .resolved_type,
            Some(number)
        );
        assert_stable_replay(&mut context, &parsed);
        assert_eq!(
            context.get_nongeneric_class_members(owner).unwrap(),
            members
        );
    }
}

#[test]
fn source_constructor_argument_errors_keep_the_constructor_signature_and_ranges() {
    let library = parse_source_file(ARRAY_LIBRARY);
    let source = concat!(
        "class Model { constructor(value: number) { const copy: number = value; } }\n",
        "const wrong: string = 'bad';\n",
        "new Model(wrong);\n",
        "new Model();\n",
        "new Model(1, 2);\n",
    );
    let parsed = parse_source_file(source);
    let mut context = context(&library, &parsed);
    let constructions = source_nodes(&parsed, SyntaxKind::NewExpression);
    let [wrong, missing, extra] = constructions.as_slice() else {
        panic!("the source must retain all three invalid constructions")
    };

    context.check_source_file(FILE).unwrap();

    let [argument_error, missing_error, extra_error] = context.diagnostics().as_slice() else {
        panic!("the constructor must report one type error and both arity errors")
    };
    assert_eq!(argument_error.diagnostic.code(), 2345);
    assert_eq!(argument_error.node, Some(new_arguments(&parsed, *wrong)[0]));
    assert_eq!(
        argument_error.diagnostic.render().unwrap(),
        "Argument of type 'string' is not assignable to parameter of type 'number'."
    );
    assert!(argument_error.related_information.is_empty());
    assert_eq!(missing_error.diagnostic.code(), 2554);
    assert_eq!(missing_error.node, Some(*missing));
    assert_eq!(
        missing_error.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 0."
    );
    let [note] = missing_error.related_information.as_slice() else {
        panic!("the missing argument must identify the real constructor parameter")
    };
    assert_eq!(note.diagnostic.code(), 6210);
    assert_eq!(
        note.node,
        Some(source_nodes(&parsed, SyntaxKind::Parameter)[0])
    );
    assert_eq!(
        note.diagnostic.render().unwrap(),
        "An argument for 'value' was not provided."
    );
    assert_eq!(extra_error.diagnostic.code(), 2554);
    assert_eq!(extra_error.node, Some(*extra));
    assert_eq!(
        extra_error.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 2."
    );
    assert!(extra_error.related_information.is_empty());
    let extra_argument = new_arguments(&parsed, *extra)[1];
    let range = extra_error
        .range_override
        .expect("the extra argument must have its own diagnostic range")
        .range();
    assert_eq!(range, parsed.arena.get(extra_argument.node).unwrap().range);
    assert_eq!(
        &source[range.start.get() as usize..range.end.get() as usize],
        "2"
    );
    assert_construction_identity(&mut context, &parsed, &constructions);
    assert_stable_replay(&mut context, &parsed);
}

// New uses the same contextual argument and array-element checks as a function call.
#[test]
#[allow(clippy::too_many_lines)] // Both query orders check the same source arrays and diagnostics.
fn source_constructor_array_arguments_keep_real_array_types_and_element_errors() {
    let library = parse_source_file(ARRAY_LIBRARY);
    let parsed = parse_source_file(concat!(
        "class Batch { constructor(values: number[]) { const copy: number[] = values; } }\n",
        "new Batch([]);\n",
        "new Batch([1, 2]);\n",
        "const wrong: string[] = ['bad'];\n",
        "new Batch(wrong);\n",
        "new Batch([1, 'bad']);\n",
    ));
    let class = source_nodes(&parsed, SyntaxKind::ClassDeclaration)[0];
    let constructions = source_nodes(&parsed, SyntaxKind::NewExpression);
    let arguments = constructions
        .iter()
        .map(|&construction| new_arguments(&parsed, construction)[0])
        .collect::<Vec<_>>();
    let [empty, numbers, wrong, invalid] = arguments.as_slice() else {
        panic!("the source must retain all four array arguments")
    };
    let NodeData::ArrayLiteralExpression(invalid_array) =
        &parsed.arena.get(invalid.node).unwrap().data
    else {
        panic!("the invalid argument must retain its real array literal")
    };
    let invalid_element = NodeRef::new(parsed.arena.id(), FILE, invalid_array.elements.nodes[1]);
    let parameter = source_nodes(&parsed, SyntaxKind::Parameter)[0];
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        panic!("the constructor must retain its annotated parameter")
    };
    let annotation = NodeRef::new(parsed.arena.id(), FILE, parameter_data.type_.unwrap());

    for members_first in [false, true] {
        let mut context = context(&library, &parsed);
        let owner = bound_symbol(&context, class);
        let prepared = members_first.then(|| context.get_nongeneric_class_members(owner).unwrap());

        context.check_source_file(FILE).unwrap();

        let [argument_error, element_error] = context.diagnostics().as_slice() else {
            panic!("the array identifier and inline element must retain separate errors")
        };
        assert_eq!(argument_error.diagnostic.code(), 2345);
        assert_eq!(argument_error.node, Some(*wrong));
        assert_eq!(
            argument_error.diagnostic.render().unwrap(),
            "Argument of type 'string[]' is not assignable to parameter of type 'number[]'."
        );
        assert!(argument_error.related_information.is_empty());
        assert_eq!(element_error.diagnostic.code(), 2322);
        assert_eq!(element_error.node, Some(invalid_element));
        assert_eq!(
            element_error.diagnostic.render().unwrap(),
            "Type 'string' is not assignable to type 'number'."
        );
        let members = assert_construction_identity(&mut context, &parsed, &constructions);
        if let Some(prepared) = prepared {
            assert_eq!(prepared, members);
        }
        let (number, string, implicit_never) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (
                bootstrap.number_type,
                bootstrap.string_type,
                bootstrap.implicit_never_type,
            )
        };
        let parameter_owner = bound_symbol(&context, parameter);
        let parameter_type = context
            .store()
            .value_symbol_links(parameter_owner)
            .unwrap()
            .resolved_type
            .unwrap();
        assert_eq!(
            context.get_type_from_type_node(annotation).unwrap(),
            parameter_type
        );
        assert_eq!(array_element(&context, parameter_type), number);
        for (&argument, expected_element) in
            [empty, numbers, wrong]
                .into_iter()
                .zip([implicit_never, number, string])
        {
            let type_ = context.get_type_at_location(argument).unwrap();
            assert_eq!(array_element(&context, type_), expected_element);
        }
        for &literal in [empty, numbers, invalid] {
            let type_ = context.get_type_at_location(literal).unwrap();
            assert_ne!(type_, parameter_type);
            assert!(
                context
                    .store()
                    .type_payload(type_)
                    .unwrap()
                    .object_flags()
                    .contains(ObjectFlags::ARRAY_LITERAL)
            );
        }
        let invalid_type = context.get_type_at_location(*invalid).unwrap();
        let element_type = array_element(&context, invalid_type);
        let TypeData::Union(element) = context.store().type_payload(element_type).unwrap().data()
        else {
            panic!("the invalid array must keep both checked element types")
        };
        assert_eq!(element.union.types.len(), 2);
        assert!(element.union.types.contains(&number));
        assert!(element.union.types.contains(&string));
        assert_stable_replay(&mut context, &parsed);
        assert_eq!(
            context.get_nongeneric_class_members(owner).unwrap(),
            members
        );
    }
}
