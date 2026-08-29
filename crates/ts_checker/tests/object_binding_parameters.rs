use ts_ast::{FileId, NodeData, NodeId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
};
use ts_parser::{ParseResult, parse_source_file};

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/object-binding-parameters.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            ),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            no_implicit_any: true,
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node(parsed: &ParseResult, file: FileId, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), file, id)
}

fn node_text<'a>(source: &'a str, parsed: &ParseResult, node: NodeRef) -> &'a str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn function_nodes(parsed: &ParseResult, file: FileId) -> (NodeRef, NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            Some((
                node(parsed, file, id),
                node(parsed, file, function.name.unwrap()),
                node(parsed, file, function.parameters.nodes[0]),
            ))
        })
        .expect("the source must contain a named function with a parameter")
}

fn parameter_bindings(parsed: &ParseResult, parameter: NodeRef) -> Vec<(NodeRef, NodeRef)> {
    let NodeData::ParameterDeclaration(parameter_data) =
        &parsed.arena.get(parameter.node).unwrap().data
    else {
        panic!("expected a parameter declaration")
    };
    let NodeData::BindingPattern(pattern) = &parsed.arena.get(parameter_data.name).unwrap().data
    else {
        panic!("expected a binding pattern")
    };
    pattern
        .elements
        .nodes
        .iter()
        .map(|id| {
            let NodeData::BindingElement(element) = &parsed.arena.get(*id).unwrap().data else {
                panic!("expected a binding element")
            };
            (
                node(parsed, parameter.file, *id),
                node(parsed, parameter.file, element.name.unwrap()),
            )
        })
        .collect()
}

fn identifier_read(
    parsed: &ParseResult,
    file: FileId,
    expected: &str,
    parent_kind: SyntaxKind,
) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::Identifier(identifier) = &record.data else {
                return None;
            };
            let parent = parsed.arena.get(record.parent?)?;
            (identifier.text == expected && parent.kind == parent_kind)
                .then_some(node(parsed, file, id))
        })
        .unwrap_or_else(|| panic!("missing {expected} read in {parent_kind:?}"))
}

fn declaration_symbol(
    context: &CanonicalCheckerContext<'_>,
    declaration: NodeRef,
) -> SemanticSymbolId {
    let symbol = context
        .file(declaration.file)
        .unwrap()
        .1
        .symbol(declaration)
        .unwrap();
    context.store().get_merged_symbol(symbol).unwrap()
}

fn store_counts(context: &CanonicalCheckerContext<'_>) -> (usize, usize, usize, usize) {
    (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().symbol_len(),
        context.store().mapper_len(),
    )
}

fn assert_warm_recheck(context: &mut CanonicalCheckerContext<'_>, file: FileId) {
    let counts = store_counts(context);
    let diagnostics = context.diagnostics().clone();
    context.recheck_source_file(file).unwrap();
    assert_eq!(store_counts(context), counts);
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
#[allow(clippy::too_many_lines)] // One function checks parent, leaf, display, and query identity.
fn static_object_parameters_keep_parent_and_leaf_artifact_identities() {
    let source = concat!(
        "function read({ count, label: text }: { count: number; label: string }) { ",
        "count; return text; }\n",
        "const result: string = read({ count: 1, label: \"ready\" });\n",
    );
    let parsed = parse_source_file(source);
    let file = FileId::new(19_701);
    let mut context = context(&parsed, file);
    let (function, function_name, parameter) = function_nodes(&parsed, file);
    let parent_symbol = declaration_symbol(&context, parameter);
    let source_file = context.source_file(file).unwrap();
    assert!(
        context
            .store()
            .source_file_links(source_file)
            .is_none_or(|links| !links.type_checked)
    );

    let callable_type = context.get_type_at_location(function_name).unwrap();
    assert!(
        context
            .store()
            .source_file_links(source_file)
            .unwrap()
            .type_checked
    );
    assert_eq!(
        context.type_to_string(callable_type).unwrap(),
        "({ count, label: text }: { count: number; label: string; }) => string",
    );
    let parent_type = context.get_type_at_location(parameter).unwrap();
    assert_eq!(
        context.type_to_string(parent_type).unwrap(),
        "{ count: number; label: string; }",
    );
    assert_eq!(
        context.get_symbol_at_location(parameter).unwrap(),
        Some(parent_symbol),
    );
    assert_eq!(
        context.get_symbol_declarations(parent_symbol).unwrap(),
        &[parameter]
    );
    let signature = context
        .store()
        .signature_links(function)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.parameters(), &[parent_symbol]);
    assert_eq!(record.min_argument_count(), 1);
    let string = context.store().intrinsic_bootstrap().unwrap().string_type;
    assert_eq!(record.resolved_return_type(), Some(string));

    let bindings = parameter_bindings(&parsed, parameter);
    assert_eq!(bindings.len(), 2);
    let reads = [
        identifier_read(&parsed, file, "count", SyntaxKind::ExpressionStatement),
        identifier_read(&parsed, file, "text", SyntaxKind::ReturnStatement),
    ];
    let mut artifacts = Vec::new();
    for (((element, name), read), expected) in
        bindings.into_iter().zip(reads).zip(["number", "string"])
    {
        let leaf_symbol = declaration_symbol(&context, element);
        assert_ne!(leaf_symbol, parent_symbol);
        assert_eq!(
            context.get_symbol_declarations(leaf_symbol).unwrap(),
            &[element]
        );
        assert_eq!(
            context.symbol_to_string(leaf_symbol).unwrap(),
            node_text(source, &parsed, name),
        );
        let leaf_type = context.get_type_at_location(name).unwrap();
        assert_eq!(context.type_to_string(leaf_type).unwrap(), expected);
        for location in [element, name, read] {
            assert_eq!(context.get_type_at_location(location).unwrap(), leaf_type);
            assert_eq!(
                context.get_symbol_at_location(location).unwrap(),
                Some(leaf_symbol),
            );
            artifacts.push((location, leaf_type, leaf_symbol));
        }
    }
    assert!(context.diagnostics().is_empty());

    let counts = store_counts(&context);
    assert_warm_recheck(&mut context, file);
    assert_eq!(
        context.get_type_at_location(function_name).unwrap(),
        callable_type
    );
    assert_eq!(
        context.get_type_at_location(parameter).unwrap(),
        parent_type
    );
    assert_eq!(
        context
            .store()
            .signature_links(function)
            .and_then(|links| links.resolved_signature.signature()),
        Some(signature),
    );
    for (location, type_, symbol) in artifacts {
        assert_eq!(context.get_type_at_location(location).unwrap(), type_);
        assert_eq!(
            context.get_symbol_at_location(location).unwrap(),
            Some(symbol)
        );
    }
    assert_eq!(store_counts(&context), counts);
}

#[test]
#[allow(clippy::too_many_lines)] // Both named parents must retain the same public query identities.
fn named_object_parameters_preserve_annotation_call_and_artifact_identities() {
    for (index, declaration) in [
        "interface Props { value: number }",
        "type Props = { value: number };",
    ]
    .into_iter()
    .enumerate()
    {
        let source = format!(
            "{declaration}\nfunction read({{ value }}: Props) {{ return value; }}\n\
             const result: number = read({{ value: 1 }});\n",
        );
        let parsed = parse_source_file(&source);
        let file = FileId::new(19_740 + u32::try_from(index).unwrap());
        let mut context = context(&parsed, file);
        let (function, function_name, parameter) = function_nodes(&parsed, file);
        let parent_symbol = declaration_symbol(&context, parameter);
        let NodeData::ParameterDeclaration(parameter_data) =
            &parsed.arena.get(parameter.node).unwrap().data
        else {
            unreachable!("the helper selected a parameter declaration")
        };
        let annotation = node(&parsed, file, parameter_data.type_.unwrap());
        let NodeData::TypeReferenceNode(reference) =
            &parsed.arena.get(annotation.node).unwrap().data
        else {
            panic!("the real parameter annotation must remain a type reference")
        };
        let reference_name = node(&parsed, file, reference.type_name);
        let props = parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                matches!(
                    record.kind,
                    SyntaxKind::InterfaceDeclaration | SyntaxKind::TypeAliasDeclaration
                )
                .then_some(node(&parsed, file, id))
            })
            .unwrap();
        let props_symbol = declaration_symbol(&context, props);
        let bindings = parameter_bindings(&parsed, parameter);
        let [(element, name)] = bindings.as_slice() else {
            panic!("the source must contain one binding")
        };
        let leaf_symbol = declaration_symbol(&context, *element);
        assert!(context.store().type_node_links(annotation).is_none());
        assert!(context.store().value_symbol_links(leaf_symbol).is_none());

        let callable_type = context.get_type_at_location(function_name).unwrap();
        assert_eq!(
            context.type_to_string(callable_type).unwrap(),
            "({ value }: Props) => number",
        );
        let parent_type = context
            .store()
            .type_node_links(annotation)
            .and_then(|links| links.resolved_type)
            .expect("the real annotation must own the resolved parent type");
        assert_eq!(context.type_to_string(parent_type).unwrap(), "Props");
        for location in [annotation, reference_name, parameter] {
            assert_eq!(context.get_type_at_location(location).unwrap(), parent_type);
        }
        assert_eq!(
            context.get_symbol_at_location(reference_name).unwrap(),
            Some(props_symbol),
        );
        assert_eq!(
            context.get_symbol_at_location(parameter).unwrap(),
            Some(parent_symbol),
        );
        assert_eq!(
            context
                .store()
                .value_symbol_links(parent_symbol)
                .unwrap()
                .resolved_type,
            Some(parent_type),
        );
        assert_ne!(leaf_symbol, parent_symbol);
        assert_ne!(leaf_symbol, props_symbol);
        let read = identifier_read(&parsed, file, "value", SyntaxKind::ReturnStatement);
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        for location in [*element, *name, read] {
            assert_eq!(context.get_type_at_location(location).unwrap(), number);
            assert_eq!(
                context.get_symbol_at_location(location).unwrap(),
                Some(leaf_symbol),
            );
        }
        let call = parsed
            .arena
            .iter()
            .find_map(|(id, record)| {
                (record.kind == SyntaxKind::CallExpression).then_some(node(&parsed, file, id))
            })
            .unwrap();
        assert_eq!(context.get_type_at_location(call).unwrap(), number);
        let signature = context
            .store()
            .signature_links(function)
            .and_then(|links| links.resolved_signature.signature())
            .unwrap();
        let record = context.store().signature(signature).unwrap();
        assert_eq!(record.parameters(), &[parent_symbol]);
        assert_eq!(record.min_argument_count(), 1);
        assert_eq!(record.resolved_return_type(), Some(number));
        assert!(context.diagnostics().is_empty());

        let parent_links = context.store().value_symbol_links(parent_symbol).cloned();
        let leaf_links = context.store().value_symbol_links(leaf_symbol).cloned();
        let annotation_links = context.store().type_node_links(annotation).cloned();
        let counts = store_counts(&context);
        assert_warm_recheck(&mut context, file);
        assert_eq!(
            context.get_type_at_location(function_name).unwrap(),
            callable_type
        );
        for location in [annotation, reference_name, parameter] {
            assert_eq!(context.get_type_at_location(location).unwrap(), parent_type);
        }
        for location in [*element, *name, read, call] {
            assert_eq!(context.get_type_at_location(location).unwrap(), number);
        }
        assert_eq!(
            context.get_symbol_at_location(read).unwrap(),
            Some(leaf_symbol)
        );
        assert_eq!(
            context.get_symbol_at_location(reference_name).unwrap(),
            Some(props_symbol)
        );
        assert_eq!(
            context.store().value_symbol_links(parent_symbol).cloned(),
            parent_links
        );
        assert_eq!(
            context.store().value_symbol_links(leaf_symbol).cloned(),
            leaf_links
        );
        assert_eq!(
            context.store().type_node_links(annotation).cloned(),
            annotation_links
        );
        assert_eq!(
            context
                .store()
                .signature_links(function)
                .and_then(|links| links.resolved_signature.signature()),
            Some(signature),
        );
        assert_eq!(store_counts(&context), counts);
    }
}

#[test]
fn literal_computed_object_parameters_keep_key_types_and_pattern_display() {
    for (index, (key, annotation, expected, key_type)) in [
        ("[\"value\"]", "value: number", "number", "\"value\""),
        ("[1]", "1: string", "string", "1"),
        ("[`value`]", "value: boolean", "boolean", "\"value\""),
    ]
    .into_iter()
    .enumerate()
    {
        let source =
            format!("function read({{ {key}: chosen }}: {{ {annotation} }}) {{ return chosen; }}");
        let parsed = parse_source_file(&source);
        let file = FileId::new(19_710 + u32::try_from(index).unwrap());
        let mut context = context(&parsed, file);
        let (_, function_name, parameter) = function_nodes(&parsed, file);

        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let callable_type = context.get_type_at_location(function_name).unwrap();
        assert_eq!(
            context.type_to_string(callable_type).unwrap(),
            format!("({{ {key}: chosen }}: {{ {annotation}; }}) => {expected}"),
        );
        let bindings = parameter_bindings(&parsed, parameter);
        let [(element, name)] = bindings.as_slice() else {
            panic!("the source must contain one binding")
        };
        let NodeData::BindingElement(element_data) = &parsed.arena.get(element.node).unwrap().data
        else {
            unreachable!("the helper selected a binding element")
        };
        let NodeData::ComputedPropertyName(property) = &parsed
            .arena
            .get(element_data.property_name.unwrap())
            .unwrap()
            .data
        else {
            panic!("the binding must have a computed property name")
        };
        let key = node(&parsed, file, property.expression);
        let key_type_id = context.get_type_at_location(key).unwrap();
        assert_eq!(context.type_to_string(key_type_id).unwrap(), key_type);
        let leaf_type = context.get_type_at_location(*name).unwrap();
        assert_eq!(context.type_to_string(leaf_type).unwrap(), expected);
        let read = identifier_read(&parsed, file, "chosen", SyntaxKind::ReturnStatement);
        assert_eq!(context.get_type_at_location(read).unwrap(), leaf_type);
        assert_eq!(
            context.get_symbol_at_location(read).unwrap(),
            Some(declaration_symbol(&context, *element)),
        );

        assert_warm_recheck(&mut context, file);
        assert_eq!(context.get_type_at_location(key).unwrap(), key_type_id);
        assert_eq!(
            context.get_type_at_location(function_name).unwrap(),
            callable_type
        );
    }
}

#[test]
fn object_parameter_calls_check_the_parent_type_and_required_arity() {
    let source = concat!(
        "function read({ value }: { value: number }) { return value; }\n",
        "const accepted: number = read({ value: 1 });\n",
        "const omitted: number = read();\n",
        "const invalid: number = read(false);\n",
    );
    let parsed = parse_source_file(source);
    let file = FileId::new(19_720);
    let mut context = context(&parsed, file);
    let (function, _, parameter) = function_nodes(&parsed, file);

    context.check_source_file(file).unwrap();

    let [missing, invalid] = context.diagnostics().as_slice() else {
        panic!("the omitted and invalid arguments must each produce one diagnostic")
    };
    assert_eq!(missing.diagnostic.code(), 2554);
    assert_eq!(
        missing.diagnostic.render().unwrap(),
        "Expected 1 arguments, but got 0."
    );
    assert_eq!(node_text(source, &parsed, missing.node.unwrap()), "read");
    assert_eq!(missing.range_override, None);
    let [related] = missing.related_information.as_slice() else {
        panic!("the missing argument must refer to the whole binding parameter")
    };
    assert_eq!(related.node, Some(parameter));
    assert_eq!(related.diagnostic.code(), 6211);
    assert_eq!(
        related.diagnostic.render().unwrap(),
        "An argument matching this binding pattern was not provided.",
    );
    assert_eq!(invalid.diagnostic.code(), 2345);
    assert_eq!(node_text(source, &parsed, invalid.node.unwrap()), "false");
    let signature = context
        .store()
        .signature_links(function)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(
        record.parameters(),
        &[declaration_symbol(&context, parameter)]
    );
    assert_eq!(record.min_argument_count(), 1);
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    for (id, record) in parsed.arena.iter() {
        if record.kind == SyntaxKind::CallExpression {
            assert_eq!(
                context
                    .get_type_at_location(node(&parsed, file, id))
                    .unwrap(),
                number
            );
        }
    }
    assert_warm_recheck(&mut context, file);
}

#[test]
fn optional_object_properties_keep_undefined_in_leaf_and_return_types() {
    let parsed = parse_source_file(concat!(
        "function read({ value }: { value?: number }) { return value; }\n",
        "const result: number = read({});\n",
    ));
    let file = FileId::new(19_721);
    let mut context = context(&parsed, file);
    let (function, _, parameter) = function_nodes(&parsed, file);

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the optional return must not be assignable to number")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    let bindings = parameter_bindings(&parsed, parameter);
    let [(element, name)] = bindings.as_slice() else {
        panic!("the source must contain one binding")
    };
    let leaf_type = context.get_type_at_location(*name).unwrap();
    assert_eq!(
        context.type_to_string(leaf_type).unwrap(),
        "number | undefined"
    );
    assert_eq!(context.get_type_at_location(*element).unwrap(), leaf_type);
    let read = identifier_read(&parsed, file, "value", SyntaxKind::ReturnStatement);
    assert_eq!(context.get_type_at_location(read).unwrap(), leaf_type);
    let signature = context
        .store()
        .signature_links(function)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    assert_eq!(
        context
            .store()
            .signature(signature)
            .unwrap()
            .resolved_return_type(),
        Some(leaf_type),
    );
    assert_warm_recheck(&mut context, file);
    assert_eq!(context.get_type_at_location(read).unwrap(), leaf_type);
}

#[test]
fn missing_object_parameter_property_reports_the_property_span() {
    let source = concat!(
        "function read({ present, missing: renamed }: { present: number }) { ",
        "return renamed; }",
    );
    let parsed = parse_source_file(source);
    let file = FileId::new(19_722);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the absent property must produce one diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2339);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Property 'missing' does not exist on type '{ present: number; }'.",
    );
    let location = diagnostic.node.unwrap();
    assert_eq!(node_text(source, &parsed, location), "missing");
    let range = parsed.arena.get(location.node).unwrap().range;
    let start = source.find("missing").unwrap();
    assert_eq!(usize::try_from(range.start.get()).unwrap(), start);
    assert_eq!(
        usize::try_from(range.end.get()).unwrap(),
        start + "missing".len()
    );
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    assert_warm_recheck(&mut context, file);
}

#[test]
fn object_parameter_leaf_assignment_updates_existing_return_flow() {
    let parsed = parse_source_file(concat!(
        "function assign({ value }: { value: string | number }, replacement: number): number { ",
        "value = replacement; return value; }\n",
        "const result: number = assign({ value: \"before\" }, 1);\n",
    ));
    let file = FileId::new(19_723);
    let mut context = context(&parsed, file);
    let (_, _, parameter) = function_nodes(&parsed, file);

    context.check_source_file(file).unwrap();
    assert!(context.diagnostics().is_empty());

    let bindings = parameter_bindings(&parsed, parameter);
    let [(element, name)] = bindings.as_slice() else {
        panic!("the source must contain one binding")
    };
    let leaf = declaration_symbol(&context, *element);
    let declared_type = context.get_type_at_location(*name).unwrap();
    assert_eq!(
        context.type_to_string(declared_type).unwrap(),
        "string | number"
    );
    let target = identifier_read(&parsed, file, "value", SyntaxKind::BinaryExpression);
    let read = identifier_read(&parsed, file, "value", SyntaxKind::ReturnStatement);
    for location in [target, read] {
        assert_eq!(
            context.get_symbol_at_location(location).unwrap(),
            Some(leaf)
        );
    }
    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(context.get_type_at_location(read).unwrap(), number);
    assert_eq!(
        context
            .store()
            .value_symbol_links(leaf)
            .unwrap()
            .resolved_type,
        Some(declared_type),
    );
    assert_warm_recheck(&mut context, file);
    assert_eq!(context.get_type_at_location(read).unwrap(), number);
}

#[test]
fn index_only_object_parameter_is_unsupported_without_diagnostics_or_leaf_links() {
    let parsed =
        parse_source_file("function read({ value }: { [key: string]: number }) { return value; }");
    let file = FileId::new(19_742);
    let mut context = context(&parsed, file);
    let (_, _, parameter) = function_nodes(&parsed, file);
    let bindings = parameter_bindings(&parsed, parameter);
    let [(element, _)] = bindings.as_slice() else {
        panic!("the source must contain one binding")
    };
    let leaf_symbol = declaration_symbol(&context, *element);

    for _ in 0..2 {
        let error = context.check_source_file(file).unwrap_err();
        assert!(
            matches!(error, SourceCheckError::Unsupported(_)),
            "{error:?}"
        );
        assert!(
            context.diagnostics().is_empty(),
            "an index-only parent must not report TS2339"
        );
        assert!(context.store().value_symbol_links(leaf_symbol).is_none());
        let source_file = context.source_file(file).unwrap();
        assert!(
            context
                .store()
                .source_file_links(source_file)
                .is_none_or(|links| !links.type_checked),
        );
    }
}

#[test]
fn object_parameter_forms_outside_the_flat_annotated_slice_publish_nothing() {
    for (index, source) in [
        "function read({ value }: { value: number } = { value: 1 }) { return value; }",
        "function read({ value = 1 }: { value?: number }) { return value; }",
        "function read({ value, ...rest }: { value: number; other: string }) { return value; }",
        "function read(key: string, { [key]: value }: { value: number }) { return value; }",
        "function read({ nested: { value } }: { nested: { value: number } }) { return value; }",
        "function read<T>({ value }: { value: T }) { return value; }",
        "declare function read({ value }: { value: number }): number;",
        "function read({ value }) { return value; }",
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        let file = FileId::new(19_730 + u32::try_from(index).unwrap());
        let mut context = context(&parsed, file);
        let before = store_counts(&context);
        let first = context.check_source_file(file).unwrap_err();
        assert!(
            matches!(first, SourceCheckError::Unsupported(_)),
            "{source}: {first:?}"
        );
        assert_eq!(store_counts(&context), before, "{source}");
        assert!(context.diagnostics().is_empty(), "{source}");
        assert_eq!(
            context.check_source_file(file).unwrap_err(),
            first,
            "{source}"
        );
        assert_eq!(store_counts(&context), before, "{source}");
        assert!(context.diagnostics().is_empty(), "{source}");

        for (id, record) in parsed.arena.iter() {
            if matches!(
                record.kind,
                SyntaxKind::FunctionDeclaration
                    | SyntaxKind::Parameter
                    | SyntaxKind::BindingElement
            ) {
                let declaration = node(&parsed, file, id);
                if let Some(symbol) = context.file(file).unwrap().1.symbol(declaration) {
                    assert!(
                        context.store().value_symbol_links(symbol).is_none(),
                        "{source}"
                    );
                }
                assert!(
                    context.store().signature_links(declaration).is_none(),
                    "{source}"
                );
            }
        }
        let source_file = context.source_file(file).unwrap();
        assert!(
            context
                .store()
                .source_file_links(source_file)
                .is_none_or(|links| !links.type_checked),
            "{source}",
        );
    }
}
