use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    TypeId, artifact_queries::CanonicalArtifactQueryError,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(19_760);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/destructured-arrow-parameters.ts\""),
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

fn only_node(parsed: &ParseResult, kind: SyntaxKind) -> NodeRef {
    let mut nodes = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| (record.kind == kind).then_some(node(parsed, id)));
    let result = nodes.next().unwrap_or_else(|| panic!("missing {kind:?}"));
    assert!(nodes.next().is_none(), "expected one {kind:?}");
    result
}

struct ArrowParts {
    arrow: NodeRef,
    variable: NodeRef,
    variable_name: NodeRef,
    parameters: Vec<NodeRef>,
    contextual_parameters: Vec<NodeRef>,
    contextual_return: NodeRef,
    body: NodeRef,
}

fn arrow_parts(parsed: &ParseResult) -> ArrowParts {
    let arrow = only_node(parsed, SyntaxKind::ArrowFunction);
    let record = parsed.arena.get(arrow.node).unwrap();
    let NodeData::ArrowFunction(data) = &record.data else {
        unreachable!()
    };
    let variable = node(parsed, record.parent.unwrap());
    let NodeData::VariableDeclaration(binding) = &parsed.arena.get(variable.node).unwrap().data
    else {
        panic!("the arrow must retain its variable context")
    };
    let NodeData::FunctionTypeNode(target) =
        &parsed.arena.get(binding.type_.unwrap()).unwrap().data
    else {
        panic!("the variable must supply the contextual function type")
    };
    ArrowParts {
        arrow,
        variable,
        variable_name: node(parsed, binding.name),
        parameters: data
            .parameters
            .nodes
            .iter()
            .map(|&id| node(parsed, id))
            .collect(),
        contextual_parameters: target
            .parameters
            .nodes
            .iter()
            .map(|&id| {
                let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(id).unwrap().data
                else {
                    panic!("expected a contextual parameter")
                };
                node(parsed, parameter.type_.unwrap())
            })
            .collect(),
        contextual_return: node(parsed, target.type_.unwrap()),
        body: node(parsed, data.body),
    }
}

fn bindings(parsed: &ParseResult, parameter: NodeRef) -> Vec<(NodeRef, NodeRef)> {
    let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(parameter.node).unwrap().data
    else {
        panic!("expected a parameter")
    };
    let NodeData::BindingPattern(pattern) = &parsed.arena.get(parameter.name).unwrap().data else {
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

fn body_read(parsed: &ParseResult, arrow: &ArrowParts, expected: &str) -> NodeRef {
    let body = parsed.arena.get(arrow.body.node).unwrap().range;
    let mut reads = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::Identifier(identifier) = &record.data else {
            return None;
        };
        (identifier.text == expected
            && record.range.start >= body.start
            && record.range.end <= body.end)
            .then_some(node(parsed, id))
    });
    let result = reads
        .next()
        .unwrap_or_else(|| panic!("missing {expected} read"));
    assert!(reads.next().is_none(), "expected one {expected} read");
    result
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

fn node_text<'source>(
    source: &'source str,
    parsed: &ParseResult,
    location: NodeRef,
) -> &'source str {
    let range = parsed.arena.get(location.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    arrow: NodeRef,
    types: &[(NodeRef, TypeId)],
    symbols: &[(NodeRef, SemanticSymbolId)],
) {
    let before = counts(context);
    let diagnostics = context.diagnostics().clone();
    let signature = context.store().signature_links(arrow).cloned();
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
    assert_eq!(context.store().signature_links(arrow).cloned(), signature);
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(counts(context), before);
    assert!(is_checked(context));
}

#[test]
#[allow(clippy::too_many_lines)] // Keep the contextual parent, bound names, and replay in one check.
fn contextual_object_arrow_bindings_keep_parent_and_leaf_identities() {
    for (index, (body, return_name)) in [
        ("count + text", "string"),
        ("{ return count + text; }", "string"),
        ("{}", "void"),
    ]
    .into_iter()
    .enumerate()
    {
        let source = format!(
            "const read: (input: {{ count: number; label: string }}) => {return_name} = \
             ({{ count, label: text }}) => {body};",
        );
        let parsed = parse_source_file(&source);
        let mut context = context(&parsed);
        let parts = arrow_parts(&parsed);
        let parameter = parts.parameters[0];
        let parent = symbol(&context, parameter);
        let owner = symbol(&context, parts.arrow);
        let variable = symbol(&context, parts.variable);
        let bindings = bindings(&parsed, parameter);
        assert_eq!(bindings.len(), 2);
        assert!(!is_checked(&context));
        if index == 0 {
            context.get_type_at_location(bindings[0].1).unwrap();
        } else {
            context.check_source_file(FILE).unwrap();
        }
        assert!(is_checked(&context));

        let callable = context.get_type_at_location(parts.arrow).unwrap();
        let target = context.get_type_at_location(parts.variable_name).unwrap();
        let parent_type = context.get_type_at_location(parameter).unwrap();
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let number = bootstrap.number_type;
        let string = bootstrap.string_type;
        let void = bootstrap.void_type;
        let expected_return = if return_name == "void" { void } else { string };
        assert_ne!(callable, target);
        assert_ne!(owner, variable);
        assert_ne!(owner, parent);
        assert_eq!(
            context.store().type_payload(callable).unwrap().symbol(),
            Some(owner)
        );
        assert_eq!(
            context.type_to_string(callable).unwrap(),
            format!(
                "({{ count, label: text }}: {{ count: number; label: string; }}) => {return_name}"
            ),
        );
        assert_eq!(
            context.type_to_string(parent_type).unwrap(),
            "{ count: number; label: string; }",
        );
        assert_eq!(
            context
                .get_type_at_location(parts.contextual_parameters[0])
                .unwrap(),
            parent_type,
        );
        assert_eq!(
            context.get_symbol_declarations(parent).unwrap(),
            &[parameter]
        );
        let signature = context
            .store()
            .signature_links(parts.arrow)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        let record = context.store().signature(signature).unwrap();
        assert_eq!(record.parameters(), &[parent]);
        assert_eq!(record.min_argument_count(), 1);
        assert_eq!(record.resolved_return_type(), Some(expected_return));

        let mut types = vec![
            (parts.arrow, callable),
            (parts.variable_name, target),
            (parameter, parent_type),
            (parts.contextual_parameters[0], parent_type),
        ];
        let mut symbols = vec![(parts.variable_name, variable), (parameter, parent)];
        for (((element, name), expected), expected_name) in bindings
            .into_iter()
            .zip([number, string])
            .zip(["count", "text"])
        {
            let leaf = symbol(&context, element);
            assert_ne!(leaf, parent);
            assert_eq!(context.get_symbol_declarations(leaf).unwrap(), &[element]);
            assert_eq!(context.symbol_to_string(leaf).unwrap(), expected_name);
            let mut locations = vec![element, name];
            if return_name != "void" {
                locations.push(body_read(&parsed, &parts, expected_name));
            }
            for location in locations {
                assert_eq!(context.get_type_at_location(location).unwrap(), expected);
                assert_eq!(
                    context.get_symbol_at_location(location).unwrap(),
                    Some(leaf)
                );
                types.push((location, expected));
                symbols.push((location, leaf));
            }
        }
        assert!(context.diagnostics().is_empty());
        assert_replay(&mut context, parts.arrow, &types, &symbols);
    }
}

#[test]
fn optional_contextual_object_arrow_binding_keeps_undefined() {
    let parsed = parse_source_file(concat!(
        "interface Props { value?: number }\n",
        "const read: (input: Props) => number | undefined = ({ value: item }) => item;\n",
        "const result: number | undefined = read({});\n",
    ));
    let mut context = context(&parsed);
    let parts = arrow_parts(&parsed);
    let bindings = bindings(&parsed, parts.parameters[0]);
    let [(element, name)] = bindings.as_slice() else {
        panic!("expected one renamed binding")
    };
    let leaf = symbol(&context, *element);
    let type_ = context.get_type_at_location(*name).unwrap();
    assert_eq!(context.type_to_string(type_).unwrap(), "number | undefined");
    let parent = context.get_type_at_location(parts.parameters[0]).unwrap();
    assert_eq!(context.type_to_string(parent).unwrap(), "Props");
    assert_eq!(
        context
            .get_type_at_location(parts.contextual_parameters[0])
            .unwrap(),
        parent,
    );
    let read = body_read(&parsed, &parts, "item");
    let call = only_node(&parsed, SyntaxKind::CallExpression);
    for location in [*element, read, call, parts.contextual_return] {
        assert_eq!(context.get_type_at_location(location).unwrap(), type_);
    }
    let callable = context.get_type_at_location(parts.arrow).unwrap();
    assert_eq!(
        context.type_to_string(callable).unwrap(),
        "({ value: item }: Props) => number | undefined",
    );
    let signature = context
        .store()
        .signature_links(parts.arrow)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    assert_eq!(
        context
            .store()
            .signature(signature)
            .unwrap()
            .resolved_return_type(),
        Some(type_)
    );
    assert!(context.diagnostics().is_empty());
    assert_replay(
        &mut context,
        parts.arrow,
        &[
            (parts.arrow, callable),
            (parts.parameters[0], parent),
            (*element, type_),
            (*name, type_),
            (read, type_),
            (call, type_),
        ],
        &[(*element, leaf), (*name, leaf), (read, leaf)],
    );
}

#[test]
fn mixed_contextual_arrow_parameters_check_binding_reads_in_body_calls() {
    let source = concat!(
        "function acceptNumber(value: number): number { return value; }\n",
        "const read: (input: { value: string }, count: number) => number = ",
        "({ value }, count) => acceptNumber(value) + count;\n",
    );
    let parsed = parse_source_file(source);
    let mut context = context(&parsed);
    let parts = arrow_parts(&parsed);
    context.check_source_file(FILE).unwrap();

    let value_read = body_read(&parsed, &parts, "value");
    let count_read = body_read(&parsed, &parts, "count");
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the string binding must fail the number argument check")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2345);
    assert_eq!(diagnostic.node, Some(value_read));
    assert_eq!(node_text(source, &parsed, value_read), "value");
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Argument of type 'string' is not assignable to parameter of type 'number'.",
    );
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());

    let bindings = bindings(&parsed, parts.parameters[0]);
    let [(element, name)] = bindings.as_slice() else {
        panic!("expected one object binding")
    };
    let leaf = symbol(&context, *element);
    let parents = parts
        .parameters
        .iter()
        .map(|&node| symbol(&context, node))
        .collect::<Vec<_>>();
    assert_ne!(parents[0], leaf);
    assert_ne!(parents[1], leaf);
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let string = bootstrap.string_type;
    for location in [*element, *name, value_read] {
        assert_eq!(context.get_type_at_location(location).unwrap(), string);
        assert_eq!(
            context.get_symbol_at_location(location).unwrap(),
            Some(leaf)
        );
    }
    assert_eq!(
        context.get_type_at_location(parts.parameters[1]).unwrap(),
        number
    );
    assert_eq!(context.get_type_at_location(count_read).unwrap(), number);
    let signature = context
        .store()
        .signature_links(parts.arrow)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.parameters(), parents);
    assert_eq!(record.min_argument_count(), 2);
    assert_eq!(record.resolved_return_type(), Some(number));
    assert_replay(
        &mut context,
        parts.arrow,
        &[
            (*element, string),
            (*name, string),
            (value_read, string),
            (parts.parameters[1], number),
            (count_read, number),
        ],
        &[(value_read, leaf), (count_read, parents[1])],
    );
}

#[test]
fn contextual_object_arrow_return_error_keeps_the_inferred_return_type() {
    let source = "const read: (input: { value: string }) => number = ({ value }) => value;";
    let parsed = parse_source_file(source);
    let mut context = context(&parsed);
    let parts = arrow_parts(&parsed);
    let callable = context.get_type_at_location(parts.arrow).unwrap();
    let read = body_read(&parsed, &parts, "value");
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let string = bootstrap.string_type;
    let number = bootstrap.number_type;
    assert_eq!(context.get_type_at_location(read).unwrap(), string);
    assert_eq!(
        context
            .get_type_at_location(parts.contextual_return)
            .unwrap(),
        number
    );
    let signature = context
        .store()
        .signature_links(parts.arrow)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    assert_eq!(
        context
            .store()
            .signature(signature)
            .unwrap()
            .resolved_return_type(),
        Some(string)
    );
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the inferred string return must fail the contextual number return")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.node, Some(parts.arrow));
    assert_eq!(
        node_text(source, &parsed, parts.arrow),
        "({ value }) => value"
    );
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type '({ value }: { value: string; }) => string' is not assignable to type '(input: { value: string; }) => number'.",
    );
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    assert_replay(
        &mut context,
        parts.arrow,
        &[
            (parts.arrow, callable),
            (read, string),
            (parts.contextual_return, number),
        ],
        &[],
    );
}

#[test]
fn missing_contextual_object_arrow_binding_keeps_property_diagnostics_on_replay() {
    let source = concat!(
        "const read: (input: { present: number }) => number = ",
        "({ missing: item }) => item;",
    );
    let parsed = parse_source_file(source);
    let mut context = context(&parsed);
    let parts = arrow_parts(&parsed);
    context.check_source_file(FILE).unwrap();

    let bindings = bindings(&parsed, parts.parameters[0]);
    let [(element, name)] = bindings.as_slice() else {
        panic!("expected one renamed binding")
    };
    let NodeData::BindingElement(binding) = &parsed.arena.get(element.node).unwrap().data else {
        unreachable!()
    };
    let property = node(&parsed, binding.property_name.unwrap());
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the absent property must produce one diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2339);
    assert_eq!(diagnostic.node, Some(property));
    assert_eq!(node_text(source, &parsed, property), "missing");
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Property 'missing' does not exist on type '{ present: number; }'.",
    );
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());

    let leaf = symbol(&context, *element);
    let error = context.store().intrinsic_bootstrap().unwrap().error_type;
    let read = body_read(&parsed, &parts, "item");
    for location in [*element, *name, read] {
        assert_eq!(context.get_type_at_location(location).unwrap(), error);
        assert_eq!(
            context.get_symbol_at_location(location).unwrap(),
            Some(leaf)
        );
    }
    assert_replay(
        &mut context,
        parts.arrow,
        &[(*element, error), (*name, error), (read, error)],
        &[(*element, leaf), (*name, leaf), (read, leaf)],
    );
}

#[test]
fn later_destructured_arrow_forms_stay_unsupported_without_publication() {
    for source in [
        "const read: (input: [number]) => number = ([value]) => value;",
        "const read: (input: { nested: { value: number } }) => number = ({ nested: { value } }) => value;",
        "const read: (input: { value: number }) => number = ({ [\"value\"]: value }) => value;",
        "const read: (input: { value?: number }) => number = ({ value = 1 }) => value;",
        "const read: (input: { value: number }) => number = ({ value } = { value: 1 }) => value;",
        "const read: (input: { value: number; other: string }) => number = ({ value, ...rest }) => value;",
        "const read = ({ value }) => value;",
        "declare function accept<T>(callback: (input: T) => T): T; const result = accept(({ value }) => value);",
        "const read: (input: { value: number }) => number = ({ value }) => { const copy = value; return copy; };",
    ] {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed);
        let arrow = only_node(&parsed, SyntaxKind::ArrowFunction);
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
            context.get_type_at_location(arrow).unwrap_err(),
            CanonicalArtifactQueryError::SourceCheck(error),
            "{source}",
        );
        assert_eq!(counts(&context), before, "{source}");
        assert!(context.diagnostics().is_empty(), "{source}");
        assert!(!is_checked(&context), "{source}");
        assert!(context.store().signature_links(arrow).is_none(), "{source}");
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
