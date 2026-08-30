use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalNameResolverOptions, CanonicalSourceFileFacts,
    CanonicalSourceLanguage, EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SignatureId, TypeData, TypeId,
    signatures::ElementFlags,
};
use ts_options::ScriptTarget;
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(62_202);
const LIBRARY_FILE: FileId = FileId::new(62_201);

fn context<'a>(
    parsed: &'a ParseResult,
    library: Option<&'a ParseResult>,
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    let mut sources = Vec::new();
    for (parsed, file, path, declaration_file) in library
        .map(|library| (library, LIBRARY_FILE, "\"/project/lib.d.ts\"", true))
        .into_iter()
        .chain([(
            parsed,
            FILE,
            "\"/project/class-method-overloads.ts\"",
            false,
        )])
    {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    declaration_file,
                    declaration_file,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        sources.push((file, &parsed.arena));
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        sources,
        CanonicalCheckerOptions {
            name_resolution: CanonicalNameResolverOptions {
                emit_target: ScriptTarget::Es2015,
                ..CanonicalNameResolverOptions::default()
            },
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

fn merged_symbol(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SemanticSymbolId {
    let raw = context.file(node.file).unwrap().1.symbol(node).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn method_name(parsed: &ParseResult, method: NodeRef) -> NodeRef {
    let NodeData::MethodDeclaration(data) = &parsed.arena.get(method.node).unwrap().data else {
        panic!("expected a method declaration")
    };
    NodeRef::new(method.arena, method.file, data.name)
}

fn callee(parsed: &ParseResult, call: NodeRef) -> NodeRef {
    let NodeData::CallExpression(data) = &parsed.arena.get(call.node).unwrap().data else {
        panic!("expected a call expression")
    };
    NodeRef::new(call.arena, call.file, data.expression)
}

fn signature(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    context
        .store()
        .signature_links(node)
        .and_then(|links| links.resolved_signature.signature())
        .expect("the checked declaration or call must retain its signature")
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .expect("the checked expression must retain its type")
}

fn counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize) {
    (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().mapper_len(),
    )
}

fn assert_replay(context: &mut CanonicalCheckerContext<'_>, queries: &[NodeRef]) {
    let types = queries
        .iter()
        .map(|node| context.get_type_at_location(*node).unwrap())
        .collect::<Vec<_>>();
    let publications = queries
        .iter()
        .map(|node| {
            (
                context.store().type_node_links(*node).cloned(),
                context.store().signature_links(*node).cloned(),
                context.store().symbol_node_links(*node).cloned(),
            )
        })
        .collect::<Vec<_>>();
    let warm = counts(context);
    let relations = context.store().relation_state_snapshot();
    let diagnostics = context.diagnostics().clone();

    context.check_source_file(FILE).unwrap();
    context.recheck_source_file(FILE).unwrap();

    for (node, type_) in queries.iter().zip(types) {
        assert_eq!(context.get_type_at_location(*node).unwrap(), type_);
    }
    assert_eq!(counts(context), warm);
    assert_eq!(context.store().relation_state_snapshot(), relations);
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(
        queries
            .iter()
            .map(|node| {
                (
                    context.store().type_node_links(*node).cloned(),
                    context.store().signature_links(*node).cloned(),
                    context.store().symbol_node_links(*node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        publications
    );
    assert!(
        context
            .source_file(FILE)
            .and_then(|source| context.store().source_file_links(source))
            .is_some_and(|links| links.type_checked)
    );
}

#[test]
#[allow(clippy::too_many_lines)] // One method group ties binder identity to calls and repeat queries.
fn method_overloads_preserve_binder_order_and_selected_returns() {
    let parsed = parse_source_file(concat!(
        "class Choice {\n",
        "  choose(value: string): string;\n",
        "  choose(value: number): number;\n",
        "  choose(value: any): any { return value; }\n",
        "}\n",
        "function text(choice: Choice): string { return choice.choose('text'); }\n",
        "function count(choice: Choice): number { return choice.choose(1); }\n",
    ));
    let mut context = context(&parsed, None);
    let declarations = nodes(&parsed, SyntaxKind::MethodDeclaration);
    let [text, count, implementation] = declarations.as_slice() else {
        panic!("expected two overload declarations and their implementation")
    };
    let owner = merged_symbol(&context, *text);
    for declaration in &declarations {
        assert_eq!(merged_symbol(&context, *declaration), owner);
    }
    assert_eq!(
        context.store().symbol(owner).unwrap().declarations(),
        Some(declarations.as_slice())
    );

    context.check_source_file(FILE).unwrap();

    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let method = context.store().symbol(owner).unwrap();
    assert_eq!(method.flags(), SymbolFlags::METHOD);
    assert_eq!(method.declarations(), Some(declarations.as_slice()));
    assert_eq!(method.value_declaration(), Some(*text));
    let class = merged_symbol(&context, nodes(&parsed, SyntaxKind::ClassDeclaration)[0]);
    let members = context.get_nongeneric_class_members(class).unwrap();
    assert_eq!(members.instance_properties(), &[owner]);
    assert!(members.static_properties().is_empty());

    let signatures = [*text, *count, *implementation].map(|node| signature(&context, node));
    let callable = context
        .store()
        .value_symbol_links(owner)
        .and_then(|links| links.resolved_type)
        .unwrap();
    let record = context.store().type_payload(callable).unwrap();
    let TypeData::Object(object) = record.data() else {
        panic!("a method overload group must retain its callable object")
    };
    assert_eq!(record.symbol(), Some(owner));
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&signatures[..2])
    );
    assert_eq!(object.structured.call_signature_count, 2);
    for ((declaration, signature), expected) in declarations
        .iter()
        .zip(signatures)
        .zip(["string", "number", "any"])
    {
        let record = context.store().signature(signature).unwrap();
        assert_eq!(record.declaration(), Some(*declaration));
        assert!(record.type_parameters().is_empty());
        assert_eq!(record.parameters().len(), 1);
        assert_eq!(
            context
                .type_to_string(record.resolved_return_type().unwrap())
                .unwrap(),
            expected
        );
    }

    let calls = nodes(&parsed, SyntaxKind::CallExpression);
    assert_eq!(calls.len(), 2);
    for ((call, selected), expected) in calls.iter().zip(&signatures[..2]).zip(["string", "number"])
    {
        assert_eq!(signature(&context, *call), *selected);
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, *call))
                .unwrap(),
            expected
        );
        let callee = callee(&parsed, *call);
        assert_eq!(context.get_type_at_location(callee).unwrap(), callable);
        assert_eq!(context.get_symbol_at_location(callee).unwrap(), Some(owner));
    }
    let names = declarations
        .iter()
        .map(|declaration| method_name(&parsed, *declaration))
        .collect::<Vec<_>>();
    for name in &names {
        assert_eq!(context.get_type_at_location(*name).unwrap(), callable);
        assert_eq!(context.get_symbol_at_location(*name).unwrap(), Some(owner));
    }
    let queries = names
        .into_iter()
        .chain(calls.iter().copied())
        .chain(calls.iter().map(|call| callee(&parsed, *call)))
        .collect::<Vec<_>>();
    assert_replay(&mut context, &queries);
    assert_eq!(
        declarations
            .iter()
            .map(|node| signature(&context, *node))
            .collect::<Vec<_>>(),
        signatures
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn a_broad_method_implementation_does_not_accept_bad_overload_arguments() {
    let parsed = parse_source_file(concat!(
        "class Reader {\n",
        "  read(value: string): number;\n",
        "  read(value: number, other: number): number;\n",
        "  read(value: any, other?: number): number { return 0; }\n",
        "}\n",
        "function bad(reader: Reader): number { return reader.read(true); }\n",
    ));
    let mut context = context(&parsed, None);

    context.check_source_file(FILE).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "the bad argument must produce one diagnostic: {:?}",
            context.diagnostics()
        )
    };
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'boolean' is not assignable to parameter of type 'string'."
    );
    assert_eq!(
        diagnostic.node,
        Some(nodes(&parsed, SyntaxKind::TrueKeyword)[0])
    );
    assert!(diagnostic.range_override.is_none());
    let declarations = nodes(&parsed, SyntaxKind::MethodDeclaration);
    let [related] = diagnostic.related_information.as_slice() else {
        panic!("the error must explain why the broad implementation cannot accept this call")
    };
    assert_eq!(related.node, Some(declarations[2]));
    assert_eq!(related.diagnostic.code(), 2793);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "The call would have succeeded against this implementation, but implementation signatures of overloads are not externally visible."
    );
    let call = nodes(&parsed, SyntaxKind::CallExpression)[0];
    let recovered = signature(&context, call);
    let original = declarations
        .iter()
        .map(|declaration| signature(&context, *declaration))
        .collect::<Vec<_>>();
    assert!(!original.contains(&recovered));
    let record = context.store().signature(recovered).unwrap();
    assert_eq!(record.flags(), ts_checker::semantic::signatures::SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE);
    assert_eq!(record.declaration(), Some(declarations[0]));
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(record.parameters().len(), 2);
    let sources = [
        context.store().signature(original[0]).unwrap().parameters()[0],
        context.store().signature(original[1]).unwrap().parameters()[1],
    ];
    for (parameter, source) in record.parameters().iter().zip(sources) {
        assert_ne!(*parameter, source);
        let links = context.store().value_symbol_links(*parameter).unwrap();
        assert_eq!(links.target, Some(source));
        assert_eq!(
            context.store().symbol(*parameter).unwrap().declarations(),
            context.store().symbol(source).unwrap().declarations()
        );
    }
    let parameter_types = record
        .parameters()
        .iter()
        .map(|parameter| {
            context
                .type_to_string(
                    context
                        .store()
                        .value_symbol_links(*parameter)
                        .unwrap()
                        .resolved_type
                        .unwrap(),
                )
                .unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(parameter_types, ["string | number", "number"]);
    let callable = context.get_type_at_location(callee(&parsed, call)).unwrap();
    let members = context
        .store()
        .type_payload(callable)
        .unwrap()
        .data()
        .structured()
        .unwrap();
    assert_eq!(members.signatures.as_deref(), Some(&original[..2]));
    assert_eq!(members.call_signature_count, 2);
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, call))
            .unwrap(),
        "number"
    );
    assert_replay(&mut context, &[call, callee(&parsed, call)]);
}

#[test]
fn incompatible_method_implementations_report_the_overload_and_implementation() {
    for (source, incompatible) in [
        (
            concat!(
                "class Reader {\n",
                "  read(value: string): number;\n",
                "  read(value: number): number;\n",
                "  read(value: string): number { return 0; }\n",
                "}\n",
            ),
            1,
        ),
        (
            concat!(
                "class Reader {\n",
                "  read(value: string): number;\n",
                "  read(value: number): number;\n",
                "  read(value: any): string { return 'wrong'; }\n",
                "}\n",
            ),
            0,
        ),
    ] {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed, None);
        let declarations = nodes(&parsed, SyntaxKind::MethodDeclaration);
        let [_, _, implementation] = declarations.as_slice() else {
            panic!("expected two overload declarations and their implementation")
        };

        context.check_source_file(FILE).unwrap();

        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!(
                "expected the first incompatible overload: {:?}",
                context.diagnostics()
            )
        };
        assert_eq!(diagnostic.diagnostic.code(), 2394);
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "This overload signature is not compatible with its implementation signature."
        );
        assert_eq!(diagnostic.node, Some(declarations[incompatible]));
        assert!(diagnostic.range_override.is_none());
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("the overload error must identify its implementation")
        };
        assert_eq!(related.node, Some(*implementation));
        assert_eq!(related.diagnostic.code(), 2750);
        assert_eq!(
            related.diagnostic.render().unwrap(),
            "The implementation signature is declared here."
        );
        let names = declarations
            .iter()
            .map(|declaration| method_name(&parsed, *declaration))
            .collect::<Vec<_>>();
        assert_replay(&mut context, &names);
    }
}

#[test]
fn compatible_method_overloads_still_check_the_implementation_body() {
    let parsed = parse_source_file(concat!(
        "class Reader {\n",
        "  read(value: string): number;\n",
        "  read(value: number): number;\n",
        "  read(value: any): number { return 'wrong'; }\n",
        "}\n",
        "function read(reader: Reader): number { return reader.read('text'); }\n",
    ));
    let mut context = context(&parsed, None);

    context.check_source_file(FILE).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!(
            "the body must produce one return error: {:?}",
            context.diagnostics()
        )
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'string' is not assignable to type 'number'."
    );
    assert_eq!(
        diagnostic.node,
        Some(nodes(&parsed, SyntaxKind::ReturnStatement)[0])
    );
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());
    let call = nodes(&parsed, SyntaxKind::CallExpression)[0];
    let declaration = nodes(&parsed, SyntaxKind::MethodDeclaration)[0];
    assert_eq!(signature(&context, call), signature(&context, declaration));
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, call))
            .unwrap(),
        "number"
    );
    assert_replay(&mut context, &[call, callee(&parsed, call)]);
}

#[test]
fn overload_and_body_diagnostics_follow_method_source_order() {
    let parsed = parse_source_file(concat!(
        "class Reader {\n",
        "  earlier(): number { return 'before'; }\n",
        "  read(value: string): number;\n",
        "  read(value: number): number;\n",
        "  read(value: string): number { return 'after'; }\n",
        "}\n",
    ));
    let mut context = context(&parsed, None);

    context.check_source_file(FILE).unwrap();

    let declarations = nodes(&parsed, SyntaxKind::MethodDeclaration);
    let returns = nodes(&parsed, SyntaxKind::ReturnStatement);
    let [earlier, overload, implementation] = context.diagnostics().as_slice() else {
        panic!("expected the earlier body, overload, and implementation errors")
    };
    assert_eq!(earlier.node, Some(returns[0]));
    assert_eq!(earlier.diagnostic.code(), 2322);
    assert_eq!(
        earlier.diagnostic.render().unwrap(),
        "Type 'string' is not assignable to type 'number'."
    );
    assert_eq!(overload.node, Some(declarations[2]));
    assert_eq!(overload.diagnostic.code(), 2394);
    assert_eq!(
        overload.diagnostic.render().unwrap(),
        "This overload signature is not compatible with its implementation signature."
    );
    let [related] = overload.related_information.as_slice() else {
        panic!("the overload error must retain its implementation note")
    };
    assert_eq!(related.node, Some(declarations[3]));
    assert_eq!(related.diagnostic.code(), 2750);
    assert_eq!(implementation.node, Some(returns[1]));
    assert_eq!(implementation.diagnostic.code(), 2322);
    assert_eq!(
        implementation.diagnostic.render().unwrap(),
        "Type 'string' is not assignable to type 'number'."
    );
    let names = declarations
        .iter()
        .map(|declaration| method_name(&parsed, *declaration))
        .collect::<Vec<_>>();
    assert_replay(&mut context, &names);
}

#[test]
fn method_body_calls_keep_array_overloads_and_their_shared_return() {
    // The unchanged ambiguousCallsWhereReturnTypesAgree.ts fixture has this method pair.
    let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
    let parsed = parse_source_file(concat!(
        "class TestClass2 {\n",
        "    public bar(x: string): number;\n",
        "    public bar(x: string[]): number;\n",
        "    public bar(x: any): number { return 0; }\n",
        "    public foo(x: string): number;\n",
        "    public foo(x: string[]): number;\n",
        "    public foo(x: any): number { return this.bar(x); }\n",
        "}\n",
    ));
    let mut context = context(&parsed, Some(&library));

    context.check_source_file(FILE).unwrap();

    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let declarations = nodes(&parsed, SyntaxKind::MethodDeclaration);
    assert_eq!(declarations.len(), 6);
    for group in declarations.chunks_exact(3) {
        let owner = merged_symbol(&context, group[0]);
        assert!(
            group
                .iter()
                .all(|node| merged_symbol(&context, *node) == owner)
        );
        assert_eq!(
            context.store().symbol(owner).unwrap().declarations(),
            Some(group)
        );
        let callable = context
            .store()
            .value_symbol_links(owner)
            .and_then(|links| links.resolved_type)
            .unwrap();
        let TypeData::Object(object) = context.store().type_payload(callable).unwrap().data()
        else {
            panic!("each method must retain its overload set")
        };
        let signatures = group[..2]
            .iter()
            .map(|node| signature(&context, *node))
            .collect::<Vec<_>>();
        assert_eq!(
            object.structured.signatures.as_deref(),
            Some(signatures.as_slice())
        );
        assert_eq!(object.structured.call_signature_count, 2);
        let array_parameter = context
            .store()
            .signature(signatures[1])
            .unwrap()
            .parameters()[0];
        let array = context
            .store()
            .value_symbol_links(array_parameter)
            .and_then(|links| links.resolved_type)
            .unwrap();
        assert_eq!(context.type_to_string(array).unwrap(), "string[]");
        let TypeData::TypeReference(array) = context.store().type_payload(array).unwrap().data()
        else {
            panic!("the array parameter must retain the canonical array reference")
        };
        assert_eq!(array.object.target, Some(context.global_types().array_type));
        assert_eq!(
            array.resolved_type_arguments.as_deref(),
            Some(&[context.store().intrinsic_bootstrap().unwrap().string_type][..])
        );
    }
    let call = nodes(&parsed, SyntaxKind::CallExpression)[0];
    assert_eq!(
        signature(&context, call),
        signature(&context, declarations[0])
    );
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, call))
            .unwrap(),
        "number"
    );
    let names = declarations
        .iter()
        .map(|declaration| method_name(&parsed, *declaration))
        .chain([call, callee(&parsed, call)])
        .collect::<Vec<_>>();
    assert_replay(&mut context, &names);
}

#[test]
#[allow(clippy::too_many_lines)] // The shared group proves tuple identity and overload choice together.
fn tuple_method_overloads_keep_selected_signatures_on_cold_and_warm_queries() {
    let source = concat!(
        "class Choice {\n",
        "  choose(pair: [number, string]): number;\n",
        "  choose(pair: [string, number]): string;\n",
        "  choose(pair: any): any { return pair; }\n",
        "}\n",
        "declare const numbers: [number, string];\n",
        "declare const strings: [string, number];\n",
        "const choice = new Choice();\n",
        "const count: number = choice.choose(numbers);\n",
        "const text: string = choice.choose(strings);\n",
    );
    for query_first in [false, true] {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed, None);
        let declarations = nodes(&parsed, SyntaxKind::MethodDeclaration);
        let [first, second, implementation] = declarations.as_slice() else {
            panic!("expected two tuple overloads and their implementation")
        };
        let annotations = [*first, *second].map(|declaration| {
            let NodeData::MethodDeclaration(method) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                unreachable!()
            };
            let NodeData::ParameterDeclaration(parameter) =
                &parsed.arena.get(method.parameters.nodes[0]).unwrap().data
            else {
                unreachable!()
            };
            NodeRef::new(declaration.arena, FILE, parameter.type_.unwrap())
        });
        let queried = query_first.then(|| {
            annotations.map(|annotation| context.get_type_from_type_node(annotation).unwrap())
        });

        context.check_source_file(FILE).unwrap();

        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let owner = merged_symbol(&context, *first);
        assert!(
            declarations
                .iter()
                .all(|node| merged_symbol(&context, *node) == owner)
        );
        assert_eq!(
            context.store().symbol(owner).unwrap().declarations(),
            Some(declarations.as_slice())
        );
        let signatures = [*first, *second, *implementation].map(|node| signature(&context, node));
        let callable = context
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type
            .unwrap();
        let record = context.store().type_payload(callable).unwrap();
        let TypeData::Object(object) = record.data() else {
            panic!("the method must retain one shared overload object")
        };
        assert_eq!(record.symbol(), Some(owner));
        assert_eq!(
            object.structured.signatures.as_deref(),
            Some(&signatures[..2])
        );
        assert_eq!(object.structured.call_signature_count, 2);
        assert_eq!(
            context
                .store()
                .signature(signatures[2])
                .unwrap()
                .declaration(),
            Some(*implementation)
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let mut tuples = Vec::new();
        for (signature, expected) in signatures[..2]
            .iter()
            .zip([[number, string], [string, number]])
        {
            let parameter = context.store().signature(*signature).unwrap().parameters()[0];
            let tuple_type = context
                .store()
                .value_symbol_links(parameter)
                .unwrap()
                .resolved_type
                .unwrap();
            let TypeData::TypeReference(reference) =
                context.store().type_payload(tuple_type).unwrap().data()
            else {
                panic!("each overload parameter must keep its canonical tuple reference")
            };
            assert_eq!(
                reference.resolved_type_arguments.as_deref(),
                Some(expected.as_slice())
            );
            let target = reference.object.target.unwrap();
            let TypeData::Tuple(tuple) = context.store().type_payload(target).unwrap().data()
            else {
                panic!("a tuple parameter must target a tuple, not an array")
            };
            assert_eq!(tuple.metadata.element_flags(), [ElementFlags::REQUIRED; 2]);
            assert_eq!(tuple.metadata.fixed_length(), 2);
            tuples.push(tuple_type);
        }
        if let Some(queried) = queried {
            assert_eq!(queried.as_slice(), tuples.as_slice());
        }
        let calls = nodes(&parsed, SyntaxKind::CallExpression);
        assert_eq!(calls.len(), 2);
        for ((call, signature_id), expected) in
            calls.iter().zip(&signatures[..2]).zip([number, string])
        {
            assert_eq!(signature(&context, *call), *signature_id);
            assert_eq!(context.get_type_at_location(*call).unwrap(), expected);
        }
        let queries = declarations
            .iter()
            .map(|node| method_name(&parsed, *node))
            .chain(annotations)
            .chain(calls)
            .collect::<Vec<_>>();
        assert_replay(&mut context, &queries);
    }
}
