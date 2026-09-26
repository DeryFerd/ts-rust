use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    TypeId, artifact_queries::CanonicalArtifactQueryError,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(27_590);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/arrow-object-parameters.ts\""),
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
            no_implicit_any: true,
            strict_function_types: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn node_text<'source>(source: &'source str, parsed: &ParseResult, node: NodeRef) -> &'source str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn variable(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then_some((node(parsed, id), node(parsed, variable.name)))
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

struct Arrow {
    declaration: NodeRef,
    variable: NodeRef,
    variable_name: NodeRef,
    parameters: Vec<NodeRef>,
    return_annotation: Option<NodeRef>,
    body: NodeRef,
}

fn arrow(parsed: &ParseResult, expected: &str) -> Arrow {
    let (variable, variable_name) = variable(parsed, expected);
    let NodeData::VariableDeclaration(binding) = &parsed.arena.get(variable.node).unwrap().data
    else {
        unreachable!()
    };
    assert!(
        binding.type_.is_none(),
        "the arrow must not use a contextual annotation"
    );
    let declaration = node(parsed, binding.initializer.unwrap());
    let record = parsed.arena.get(declaration.node).unwrap();
    let NodeData::ArrowFunction(data) = &record.data else {
        panic!("expected an actual arrow")
    };
    assert_eq!(record.kind, SyntaxKind::ArrowFunction);
    assert_eq!(record.parent, Some(variable.node));
    Arrow {
        declaration,
        variable,
        variable_name,
        parameters: data
            .parameters
            .nodes
            .iter()
            .map(|&id| node(parsed, id))
            .collect(),
        return_annotation: data.type_.map(|id| node(parsed, id)),
        body: node(parsed, data.body),
    }
}

fn annotation(parsed: &ParseResult, parameter: NodeRef) -> NodeRef {
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        panic!("expected a parameter")
    };
    node(parsed, data.type_.unwrap())
}

fn bindings(parsed: &ParseResult, parameter: NodeRef) -> Vec<(NodeRef, NodeRef)> {
    let NodeData::ParameterDeclaration(data) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        panic!("expected a parameter")
    };
    let record = parsed.arena.get(data.name).unwrap();
    assert_eq!(record.kind, SyntaxKind::ObjectBindingPattern);
    let NodeData::BindingPattern(pattern) = &record.data else {
        panic!("expected an object binding pattern")
    };
    pattern
        .elements
        .nodes
        .iter()
        .map(|&id| {
            let NodeData::BindingElement(element) = &parsed.arena.get(id).unwrap().data else {
                panic!("expected a binding element")
            };
            (node(parsed, id), node(parsed, element.name.unwrap()))
        })
        .collect()
}

fn body_read(parsed: &ParseResult, arrow: &Arrow, expected: &str) -> NodeRef {
    let body = parsed.arena.get(arrow.body.node).unwrap().range;
    let mut reads = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::Identifier(name) = &record.data else {
            return None;
        };
        (name.text == expected && record.range.start >= body.start && record.range.end <= body.end)
            .then_some(node(parsed, id))
    });
    let read = reads
        .next()
        .unwrap_or_else(|| panic!("missing body read {expected}"));
    assert!(reads.next().is_none(), "expected one body read {expected}");
    read
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
}

fn counts(context: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = context.store();
    [
        store.type_len(),
        store.type_alias_len(),
        store.symbol_len(),
        store.signature_len(),
        store.mapper_len(),
        store.index_info_len(),
        store.symbol_store().symbol_table_len(),
    ]
}

fn is_checked(context: &CanonicalCheckerContext<'_>) -> bool {
    context
        .store()
        .source_file_links(context.source_file(FILE).unwrap())
        .is_some_and(|links| links.type_checked)
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    arrows: &[NodeRef],
    types: &[(NodeRef, TypeId)],
    symbols: &[(NodeRef, SemanticSymbolId)],
) {
    for &(location, expected) in types {
        assert_eq!(context.get_type_at_location(location).unwrap(), expected);
    }
    for &(location, expected) in symbols {
        assert_eq!(
            context.get_symbol_at_location(location).unwrap(),
            Some(expected)
        );
    }
    let before = counts(context);
    let diagnostics = context.diagnostics().clone();
    let signatures = arrows
        .iter()
        .map(|&arrow| (arrow, context.store().signature_links(arrow).cloned()))
        .collect::<Vec<_>>();
    let type_links = types
        .iter()
        .map(|&(location, _)| (location, context.store().type_node_links(location).cloned()))
        .collect::<Vec<_>>();
    let symbol_links = symbols
        .iter()
        .map(|&(location, _)| (location, context.store().symbol_node_links(location).cloned()))
        .collect::<Vec<_>>();
    let mut owners = symbols.iter().map(|&(_, symbol)| symbol).collect::<Vec<_>>();
    owners.extend(arrows.iter().map(|&arrow| symbol(context, arrow)));
    let value_links = owners
        .into_iter()
        .map(|owner| (owner, context.store().value_symbol_links(owner).cloned()))
        .collect::<Vec<_>>();

    context.check_source_file(FILE).unwrap();
    context.recheck_source_file(FILE).unwrap();
    for &(location, expected) in types {
        assert_eq!(context.get_type_at_location(location).unwrap(), expected);
    }
    for &(location, expected) in symbols {
        assert_eq!(
            context.get_symbol_at_location(location).unwrap(),
            Some(expected)
        );
    }
    for (arrow, expected) in signatures {
        assert_eq!(context.store().signature_links(arrow).cloned(), expected);
    }
    for (location, expected) in type_links {
        assert_eq!(context.store().type_node_links(location).cloned(), expected);
    }
    for (location, expected) in symbol_links {
        assert_eq!(context.store().symbol_node_links(location).cloned(), expected);
    }
    for (owner, expected) in value_links {
        assert_eq!(context.store().value_symbol_links(owner).cloned(), expected);
    }
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(counts(context), before);
    assert!(is_checked(context));
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the arrow, parameter, leaves, and replay in one check.
fn typed_object_arrows_keep_real_parent_leaf_and_annotation_identities() {
    for (index, body) in ["count + text", "{ return count + text; }"]
        .into_iter()
        .enumerate()
    {
        let source = format!(
            "const read = ({{ count, label: text }}: {{ count: number; label: string }}): string \
             => {body}; const result: string = read({{ count: 1, label: 'ready' }});",
        );
        let parsed = parse_source_file(&source);
        let mut context = context(&parsed);
        let arrow = arrow(&parsed, "read");
        let parameter = arrow.parameters[0];
        let annotation = annotation(&parsed, parameter);
        let owner = symbol(&context, arrow.declaration);
        let variable = symbol(&context, arrow.variable);
        let parent = symbol(&context, parameter);
        let bindings = bindings(&parsed, parameter);
        assert_eq!(bindings.len(), 2);
        assert!(!is_checked(&context));
        if index == 0 {
            context.get_type_at_location(bindings[0].1).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        assert!(is_checked(&context));

        let callable = context.get_type_at_location(arrow.declaration).unwrap();
        let parent_type = context.get_type_at_location(parameter).unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        assert_ne!(owner, variable);
        assert_ne!(owner, parent);
        assert_eq!(
            context.store().symbol(owner).unwrap().flags(),
            SymbolFlags::FUNCTION
        );
        assert_eq!(
            context.get_symbol_declarations(owner).unwrap(),
            &[arrow.declaration]
        );
        assert_eq!(
            context.store().type_payload(callable).unwrap().symbol(),
            Some(owner)
        );
        assert_eq!(
            context.get_symbol_at_location(arrow.declaration).unwrap(),
            None
        );
        assert_eq!(
            context.type_to_string(callable).unwrap(),
            "({ count, label: text }: { count: number; label: string; }) => string",
        );
        assert_eq!(
            context.type_to_string(parent_type).unwrap(),
            "{ count: number; label: string; }"
        );
        assert_eq!(
            context.get_symbol_declarations(parent).unwrap(),
            &[parameter]
        );
        assert_eq!(
            context.store().symbol(parent).unwrap().flags(),
            SymbolFlags::FUNCTION_SCOPED_VARIABLE,
        );
        let signature = context
            .store()
            .signature_links(arrow.declaration)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        let record = context.store().signature(signature).unwrap();
        assert_eq!(record.parameters(), &[parent]);
        assert_eq!(record.min_argument_count(), 1);
        assert_eq!(record.resolved_return_type(), Some(string));
        let mut types = vec![
            (arrow.declaration, callable),
            (arrow.variable_name, callable),
            (parameter, parent_type),
            (annotation, parent_type),
            (arrow.return_annotation.unwrap(), string),
        ];
        let mut symbols = vec![(arrow.variable_name, variable), (parameter, parent)];
        for (((element, name), expected), expected_name) in bindings
            .into_iter()
            .zip([number, string])
            .zip(["count", "text"])
        {
            let leaf = symbol(&context, element);
            assert_ne!(leaf, parent);
            assert_ne!(leaf, owner);
            assert_eq!(context.get_symbol_declarations(leaf).unwrap(), &[element]);
            assert_eq!(context.symbol_to_string(leaf).unwrap(), expected_name);
            let read = body_read(&parsed, &arrow, expected_name);
            let (_, bound) = context.file(FILE).unwrap();
            for location in [parameter, element, name, read] {
                assert_eq!(bound.container(location), Some(arrow.declaration));
                assert_eq!(
                    bound.block_scope_container(location),
                    Some(arrow.declaration)
                );
            }
            for location in [element, name, read] {
                types.push((location, expected));
                symbols.push((location, leaf));
            }
        }
        for (id, record) in parsed.arena.iter() {
            if record.kind == SyntaxKind::CallExpression {
                types.push((node(&parsed, id), string));
            }
        }
        assert!(context.diagnostics().is_empty());
        assert_replay(&mut context, &[arrow.declaration], &types, &symbols);
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Check optional reads and default scope with the same parent.
fn optional_object_leaf_and_later_default_keep_the_arrow_parameter_scope() {
    let source = concat!(
        "const seed: string = 'outside';\n",
        "const read = ({ seed, optional: item }: { seed: number; optional?: number }, ",
        "fallback: number = seed): number | undefined => item;\n",
        "const omitted: number | undefined = read({ seed: 1 });\n",
        "const explicit: number | undefined = read({ seed: 1 }, undefined);\n",
    );
    let parsed = parse_source_file(source);
    let mut context = context(&parsed);
    let arrow = arrow(&parsed, "read");
    let parameter = arrow.parameters[0];
    let [(seed_element, seed_name), (item_element, item_name)]: [(NodeRef, NodeRef); 2] =
        bindings(&parsed, parameter).try_into().unwrap();
    let seed = symbol(&context, seed_element);
    let item = symbol(&context, item_element);
    let (outer_declaration, outer_name) = variable(&parsed, "seed");
    let outer = symbol(&context, outer_declaration);
    assert_ne!(seed, outer);
    let fallback = arrow.parameters[1];
    let NodeData::ParameterDeclaration(default) = &parsed.arena.get(fallback.node).unwrap().data
    else {
        panic!("expected the defaulted identifier parameter")
    };
    let default_read = node(&parsed, default.initializer.unwrap());
    assert_eq!(node_text(source, &parsed, default_read), "seed");
    context.get_type_at_location(default_read).unwrap();

    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let optional = context.get_type_at_location(item_name).unwrap();
    assert_eq!(context.type_to_string(optional).unwrap(), "number | undefined");
    let parent_type = context.get_type_at_location(parameter).unwrap();
    assert_eq!(
        context.type_to_string(parent_type).unwrap(),
        "{ seed: number; optional?: number | undefined; }"
    );
    let parent = symbol(&context, parameter);
    let fallback_symbol = symbol(&context, fallback);
    let signature = context
        .store()
        .signature_links(arrow.declaration)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.parameters(), &[parent, fallback_symbol]);
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(record.resolved_return_type(), Some(optional));
    assert_eq!(context.get_symbol_declarations(seed).unwrap(), &[seed_element]);
    assert_eq!(context.get_symbol_declarations(item).unwrap(), &[item_element]);
    assert_eq!(
        context.get_symbol_declarations(fallback_symbol).unwrap(),
        &[fallback]
    );
    let read = body_read(&parsed, &arrow, "item");
    let mut types = vec![
        (outer_name, string),
        (parameter, parent_type),
        (annotation(&parsed, parameter), parent_type),
        (seed_element, number),
        (seed_name, number),
        (default_read, number),
        (fallback, number),
        (node(&parsed, default.name), number),
        (annotation(&parsed, fallback), number),
        (item_element, optional),
        (item_name, optional),
        (read, optional),
        (arrow.return_annotation.unwrap(), optional),
    ];
    for (id, record) in parsed.arena.iter() {
        if record.kind == SyntaxKind::CallExpression {
            types.push((node(&parsed, id), optional));
        }
    }
    assert!(context.diagnostics().is_empty());
    assert_replay(
        &mut context,
        &[arrow.declaration],
        &types,
        &[
            (outer_name, outer),
            (parameter, parent),
            (seed_element, seed),
            (seed_name, seed),
            (default_read, seed),
            (fallback, fallback_symbol),
            (item_element, item),
            (item_name, item),
            (read, item),
        ],
    );
}

#[test]
fn same_name_object_leaves_remain_in_their_own_arrow_scopes() {
    let parsed = parse_source_file(concat!(
        "const first = ({ value }: { value: number }): number => value;\n",
        "const second = ({ value }: { value: string }): string => value;\n",
    ));
    let mut context = context(&parsed);
    let first = arrow(&parsed, "first");
    let second = arrow(&parsed, "second");
    context.check_source_file(FILE).unwrap();
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    let mut leaves = Vec::new();
    let mut parents = Vec::new();
    let mut types = Vec::new();
    let mut symbols = Vec::new();
    for (arrow, expected) in [(&first, number), (&second, string)] {
        let parameter = arrow.parameters[0];
        let [(element, name)]: [(NodeRef, NodeRef); 1] =
            bindings(&parsed, parameter).try_into().unwrap();
        let leaf = symbol(&context, element);
        let parent = symbol(&context, parameter);
        let owner = symbol(&context, arrow.declaration);
        let read = body_read(&parsed, arrow, "value");
        let (_, bound) = context.file(FILE).unwrap();
        for location in [parameter, element, name, read] {
            assert_eq!(bound.container(location), Some(arrow.declaration));
        }
        let callable = context.get_type_at_location(arrow.declaration).unwrap();
        assert_eq!(
            context.store().type_payload(callable).unwrap().symbol(),
            Some(owner)
        );
        let signature = context
            .store()
            .signature_links(arrow.declaration)
            .unwrap()
            .resolved_signature
            .signature()
            .unwrap();
        assert_eq!(
            context.store().signature(signature).unwrap().parameters(),
            &[parent]
        );
        assert_eq!(
            context.get_return_type_of_signature(signature).unwrap(),
            expected
        );
        types.push((arrow.declaration, callable));
        for location in [element, name, read] {
            types.push((location, expected));
            symbols.push((location, leaf));
        }
        leaves.push(leaf);
        parents.push(parent);
    }
    assert_ne!(leaves[0], leaves[1]);
    assert_ne!(parents[0], parents[1]);
    assert_ne!(
        symbol(&context, first.declaration),
        symbol(&context, second.declaration)
    );
    assert!(context.diagnostics().is_empty());
    assert_replay(
        &mut context,
        &[first.declaration, second.declaration],
        &types,
        &symbols,
    );
}

#[test]
fn object_arrow_property_and_call_errors_keep_exact_locations_and_recovery_types() {
    let source = concat!(
        "const read = ({ value, missing: item }: { value: number }): number => item;\n",
        "const omitted: number = read();\n",
        "const invalid: number = read(false);\n",
    );
    let parsed = parse_source_file(source);
    let mut context = context(&parsed);
    let arrow = arrow(&parsed, "read");
    let parameter = arrow.parameters[0];
    let [(_, _), (element, name)]: [(NodeRef, NodeRef); 2] =
        bindings(&parsed, parameter).try_into().unwrap();
    let NodeData::BindingElement(binding) = &parsed.arena.get(element.node).unwrap().data else {
        unreachable!()
    };
    let property = node(&parsed, binding.property_name.unwrap());
    context.check_source_file(FILE).unwrap();

    let [missing, omitted, invalid] = context.diagnostics().as_slice() else {
        panic!("expected the missing property and the two call errors")
    };
    assert_eq!(missing.diagnostic.code(), 2339);
    assert_eq!(missing.node, Some(property));
    assert_eq!(node_text(source, &parsed, property), "missing");
    assert_eq!(
        missing.diagnostic.render().unwrap(),
        "Property 'missing' does not exist on type '{ value: number; }'.",
    );
    assert_eq!(missing.range_override, None);
    assert!(missing.related_information.is_empty());
    assert_eq!(omitted.diagnostic.code(), 2554);
    assert_eq!(
        omitted.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 0."
    );
    assert_eq!(node_text(source, &parsed, omitted.node.unwrap()), "read");
    let omitted_range = parsed.arena.get(omitted.node.unwrap().node).unwrap().range;
    assert_eq!(
        usize::try_from(omitted_range.start.get()).unwrap(),
        source.find("read()").unwrap()
    );
    assert_eq!(omitted.range_override, None);
    let [related] = omitted.related_information.as_slice() else {
        panic!("the omitted argument must identify the whole object parameter")
    };
    assert_eq!(related.node, Some(parameter));
    assert_eq!(related.diagnostic.code(), 6211);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument matching this binding pattern was not provided.",
    );
    assert_eq!(invalid.diagnostic.code(), 2345);
    assert_eq!(node_text(source, &parsed, invalid.node.unwrap()), "false");
    assert_eq!(
        invalid.diagnostic.render().unwrap(),
        "Argument of type 'boolean' is not assignable to parameter of type '{ value: number; }'.",
    );
    assert_eq!(invalid.range_override, None);
    assert!(invalid.related_information.is_empty());

    let error = context.store().intrinsic_bootstrap().unwrap().error_type;
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    let leaf = symbol(&context, element);
    let read = body_read(&parsed, &arrow, "item");
    let mut types = vec![(element, error), (name, error), (read, error)];
    for (id, record) in parsed.arena.iter() {
        if record.kind == SyntaxKind::CallExpression {
            types.push((node(&parsed, id), number));
        }
    }
    assert_replay(
        &mut context,
        &[arrow.declaration],
        &types,
        &[(element, leaf), (name, leaf), (read, leaf)],
    );
}

#[test]
fn later_object_arrow_patterns_remain_unsupported_without_partial_publication() {
    for source in [
        "const read = ({ value = 1 }: { value?: number }): number => value;",
        "const read = ({ value }: { value: number } = { value: 1 }): number => value;",
        "const read = ({ nested: { value } }: { nested: { value: number } }): number => value;",
        "const read = ({ value, ...rest }: { value: number; other: string }): number => value;",
    ] {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed);
        let arrow = arrow(&parsed, "read");
        let before = counts(&context);
        let error = context.check_source_file(FILE).unwrap_err();
        assert!(
            matches!(error, SourceCheckError::Unsupported(_)),
            "{source}: {error:?}"
        );
        assert_eq!(
            context.check_source_file(FILE).unwrap_err(),
            error,
            "{source}"
        );
        assert_eq!(
            context.get_type_at_location(arrow.declaration).unwrap_err(),
            CanonicalArtifactQueryError::SourceCheck(error),
            "{source}",
        );
        assert_eq!(counts(&context), before, "{source}");
        assert!(context.diagnostics().is_empty(), "{source}");
        assert!(!is_checked(&context), "{source}");
        assert!(
            context.store().signature_links(arrow.declaration).is_none(),
            "{source}"
        );
        for (id, record) in parsed.arena.iter() {
            if matches!(
                record.kind,
                SyntaxKind::ArrowFunction | SyntaxKind::Parameter | SyntaxKind::BindingElement
            ) && let Some(symbol) = context.file(FILE).unwrap().1.symbol(node(&parsed, id))
            {
                assert!(
                    context.store().value_symbol_links(symbol).is_none(),
                    "{source}"
                );
            }
        }
    }
}
