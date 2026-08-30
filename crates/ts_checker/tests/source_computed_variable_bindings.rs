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

const FILE: FileId = FileId::new(19_780);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/computed-variable-bindings.ts\""),
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

struct BindingParts {
    declaration: NodeRef,
    element: NodeRef,
    name: NodeRef,
    key: Option<NodeRef>,
    default: Option<NodeRef>,
    initializer: NodeRef,
}

fn binding_parts(parsed: &ParseResult, expected: &str) -> BindingParts {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::BindingElement(binding) = &record.data else {
                return None;
            };
            let name = binding.name?;
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            if identifier.text != expected {
                return None;
            }
            let pattern = parsed.arena.get(record.parent?)?;
            assert_eq!(pattern.kind, SyntaxKind::ObjectBindingPattern);
            let declaration = node(parsed, pattern.parent?);
            let NodeData::VariableDeclaration(variable) = &parsed.arena.get(declaration.node)?.data
            else {
                panic!("the binding must belong to its original variable declaration")
            };
            let key = binding.property_name.and_then(|property| {
                let NodeData::ComputedPropertyName(computed) = &parsed.arena.get(property)?.data
                else {
                    return None;
                };
                Some(node(parsed, computed.expression))
            });
            Some(BindingParts {
                declaration,
                element: node(parsed, id),
                name: node(parsed, name),
                key,
                default: binding.initializer.map(|id| node(parsed, id)),
                initializer: node(parsed, variable.initializer.unwrap()),
            })
        })
        .unwrap_or_else(|| panic!("missing binding {expected}"))
}

fn variable_initializer(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected)
                .then_some(variable.initializer)
                .flatten()
                .map(|id| node(parsed, id))
        })
        .unwrap_or_else(|| panic!("missing variable {expected}"))
}

fn node_text<'source>(
    source: &'source str,
    parsed: &ParseResult,
    location: NodeRef,
) -> &'source str {
    let range = parsed.arena.get(location.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
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

fn assert_binding(
    context: &mut CanonicalCheckerContext<'_>,
    binding: &BindingParts,
    expected: &str,
) -> (TypeId, SemanticSymbolId) {
    let (_, bound) = context.file(FILE).unwrap();
    assert!(bound.symbol(binding.declaration).is_none());
    let symbol = context
        .store()
        .get_merged_symbol(bound.symbol(binding.element).unwrap())
        .unwrap();
    let record = context.store().symbol(symbol).unwrap();
    assert_eq!(record.flags(), SymbolFlags::BLOCK_SCOPED_VARIABLE);
    assert_eq!(record.declarations(), Some(&[binding.element][..]));
    assert_eq!(record.value_declaration(), Some(binding.element));
    let type_ = context.get_type_at_location(binding.name).unwrap();
    assert_eq!(context.type_to_string(type_).unwrap(), expected);
    assert_eq!(
        context.get_type_at_location(binding.element).unwrap(),
        type_
    );
    for location in [binding.element, binding.name] {
        assert_eq!(
            context.get_symbol_at_location(location).unwrap(),
            Some(symbol)
        );
    }
    assert_eq!(
        context.get_symbol_declarations(symbol).unwrap(),
        &[binding.element]
    );
    (type_, symbol)
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    types: &[(NodeRef, TypeId)],
    symbols: &[(NodeRef, SemanticSymbolId)],
) {
    let before = counts(context);
    let diagnostics = context.diagnostics().clone();
    let source = context
        .store()
        .source_file_links(context.source_file(FILE).unwrap())
        .cloned();
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
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(counts(context), before);
    assert_eq!(
        context
            .store()
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        source
    );
    assert!(is_checked(context));
}

#[test]
fn single_computed_bindings_accept_identifier_and_known_call_initializers() {
    for (prefix, initializer, kind) in [
        (
            "const input = { value: 1 };",
            "input",
            SyntaxKind::Identifier,
        ),
        (
            "function input(): { value: number } { return { value: 1 }; }",
            "input()",
            SyntaxKind::CallExpression,
        ),
    ] {
        let source = format!(
            "{prefix}\nconst {{ ['value']: selected }} = {initializer};\nconst observed = selected;",
        );
        let parsed = parse_source_file(&source);
        let mut context = context(&parsed);
        let binding = binding_parts(&parsed, "selected");
        assert_eq!(
            parsed.arena.get(binding.initializer.node).unwrap().kind,
            kind
        );
        assert!(!is_checked(&context));
        let (type_, symbol) = assert_binding(&mut context, &binding, "number");
        assert!(is_checked(&context));
        assert_eq!(
            type_,
            context.store().intrinsic_bootstrap().unwrap().number_type
        );
        let key = binding.key.unwrap();
        let key_type = context.get_type_at_location(key).unwrap();
        assert_eq!(context.type_to_string(key_type).unwrap(), "\"value\"");
        let input_type = context.get_type_at_location(binding.initializer).unwrap();
        assert_eq!(
            context.type_to_string(input_type).unwrap(),
            "{ value: number; }"
        );
        let observed = variable_initializer(&parsed, "observed");
        assert_eq!(context.get_type_at_location(observed).unwrap(), type_);
        assert_eq!(
            context.get_symbol_at_location(observed).unwrap(),
            Some(symbol)
        );
        assert!(context.diagnostics().is_empty());
        assert_replay(
            &mut context,
            &[
                (binding.element, type_),
                (binding.name, type_),
                (key, key_type),
                (binding.initializer, input_type),
                (observed, type_),
            ],
            &[
                (binding.element, symbol),
                (binding.name, symbol),
                (observed, symbol),
            ],
        );
    }
}

#[test]
fn fixed_computed_keys_remove_actual_properties_from_defaulted_rest() {
    for (key_value, input_members, expected_key, expected_rest) in [
        (
            "'value'",
            "value?: number; key: boolean; keep: string",
            "\"value\"",
            "{ key: boolean; keep: string; }",
        ),
        ("1", "1?: number; keep: string", "1", "{ keep: string; }"),
    ] {
        let source = format!(
            "interface Input {{ {input_members} }}\ndeclare const input: Input;\n\
             const key = {key_value};\nconst {{ [key]: selected = 7, ...rest }} = input;\n\
             const observed = selected;\nconst kept = rest.keep;",
        );
        let parsed = parse_source_file(&source);
        let mut context = context(&parsed);
        context.check_source_file(FILE).unwrap();
        let selected = binding_parts(&parsed, "selected");
        let rest = binding_parts(&parsed, "rest");
        let (selected_type, selected_symbol) = assert_binding(&mut context, &selected, "number");
        let (rest_type, rest_symbol) = assert_binding(&mut context, &rest, expected_rest);
        assert_ne!(selected_symbol, rest_symbol);
        let key = selected.key.unwrap();
        let key_type = context.get_type_at_location(key).unwrap();
        let key_symbol = context.get_symbol_at_location(key).unwrap().unwrap();
        assert_eq!(context.type_to_string(key_type).unwrap(), expected_key);
        assert_ne!(key_symbol, selected_symbol);
        let default = selected.default.unwrap();
        let default_type = context.get_type_at_location(default).unwrap();
        assert_eq!(context.type_to_string(default_type).unwrap(), "7");
        let observed = variable_initializer(&parsed, "observed");
        let kept = variable_initializer(&parsed, "kept");
        assert_eq!(
            context.get_type_at_location(observed).unwrap(),
            selected_type
        );
        let string = context.store().intrinsic_bootstrap().unwrap().string_type;
        assert_eq!(context.get_type_at_location(kept).unwrap(), string);
        assert!(context.diagnostics().is_empty());
        assert_replay(
            &mut context,
            &[
                (selected.element, selected_type),
                (selected.name, selected_type),
                (rest.element, rest_type),
                (rest.name, rest_type),
                (key, key_type),
                (default, default_type),
                (observed, selected_type),
                (kept, string),
            ],
            &[
                (selected.name, selected_symbol),
                (rest.name, rest_symbol),
                (key, key_symbol),
                (observed, selected_symbol),
            ],
        );
    }
}

#[test]
fn missing_named_property_defaults_keep_literal_and_widened_types() {
    for (declaration, expected) in [("const", "1"), ("let", "number")] {
        let source = format!("{declaration} {{ missing = 1 }} = {{}}; const observed = missing;");
        let parsed = parse_source_file(&source);
        let mut context = context(&parsed);
        let binding = binding_parts(&parsed, "missing");
        assert_eq!(binding.key, None);
        let (type_, symbol) = assert_binding(&mut context, &binding, expected);
        let observed = variable_initializer(&parsed, "observed");
        assert_eq!(context.get_type_at_location(observed).unwrap(), type_);
        let default = binding.default.unwrap();
        let default_type = context.get_type_at_location(default).unwrap();
        assert_eq!(context.type_to_string(default_type).unwrap(), "1");
        assert!(context.diagnostics().is_empty());
        assert_replay(
            &mut context,
            &[
                (binding.element, type_),
                (binding.name, type_),
                (default, default_type),
                (observed, type_),
            ],
            &[
                (binding.element, symbol),
                (binding.name, symbol),
                (observed, symbol),
            ],
        );
    }
}

#[test]
fn annotated_computed_defaults_keep_declared_types_and_default_errors() {
    let source = concat!(
        "const key = 'value';\n",
        "const { [key]: good = 1 }: { value?: number } = {};\n",
        "const { [key]: wrong = 'fallback' }: { value?: number } = {};\n",
        "const { [key]: retains = undefined }: { value?: number } = {};\n",
        "interface Input { value?: number }\n",
        "declare const input: Input;\n",
        "const { [key]: inferred = 'fallback' } = input;\n",
        "const observedGood = good; const observedWrong = wrong;\n",
        "const observedRetains = retains; const observedInferred = inferred;\n",
    );
    let parsed = parse_source_file(source);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let wrong = binding_parts(&parsed, "wrong");
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("only the string default on the annotated number binding must fail")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.node, Some(wrong.name));
    assert_eq!(
        node_text(source, &parsed, diagnostic.node.unwrap()),
        "wrong"
    );
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'string' is not assignable to type 'number'."
    );
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());

    let mut types = Vec::new();
    let mut symbols = Vec::new();
    for (name, observed, expected) in [
        ("good", "observedGood", "number"),
        ("wrong", "observedWrong", "number"),
        ("retains", "observedRetains", "number | undefined"),
        ("inferred", "observedInferred", "number | \"fallback\""),
    ] {
        let binding = binding_parts(&parsed, name);
        let (resolved, symbol) = assert_binding(&mut context, &binding, expected);
        let observed = variable_initializer(&parsed, observed);
        assert_eq!(context.get_type_at_location(observed).unwrap(), resolved);
        types.extend([
            (binding.element, resolved),
            (binding.name, resolved),
            (observed, resolved),
        ]);
        symbols.extend([
            (binding.element, symbol),
            (binding.name, symbol),
            (observed, symbol),
        ]);
    }
    assert_replay(&mut context, &types, &symbols);
}

#[test]
fn broad_computed_keys_keep_primitive_types_and_index_diagnostics() {
    for (key_value, input, expected_key, expected_parent) in [
        ("'value'", "{ value: 1 }", "string", "{ value: number; }"),
        ("1", "{ 1: 'ready' }", "number", "{ 1: string; }"),
    ] {
        let source = format!(
            "let key = {key_value}; const input = {input};\n\
             const {{ [key]: selected }} = input; const observed = selected;",
        );
        let parsed = parse_source_file(&source);
        let mut context = context(&parsed);
        context.check_source_file(FILE).unwrap();
        let binding = binding_parts(&parsed, "selected");
        let key = binding.key.unwrap();
        let [diagnostic] = context.diagnostics().as_slice() else {
            panic!("the broad key must report one missing index signature")
        };
        assert_eq!(diagnostic.diagnostic.code(), 2537);
        assert_eq!(diagnostic.node, Some(key));
        assert_eq!(node_text(&source, &parsed, key), "key");
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            format!(
                "Type '{expected_parent}' has no matching index signature for type '{expected_key}'."
            )
        );
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
        let key_type = context.get_type_at_location(key).unwrap();
        assert_eq!(context.type_to_string(key_type).unwrap(), expected_key);
        let (type_, symbol) = assert_binding(&mut context, &binding, "any");
        assert_eq!(
            type_,
            context.store().intrinsic_bootstrap().unwrap().error_type
        );
        let observed = variable_initializer(&parsed, "observed");
        assert_eq!(context.get_type_at_location(observed).unwrap(), type_);
        assert_replay(
            &mut context,
            &[
                (binding.element, type_),
                (binding.name, type_),
                (key, key_type),
                (observed, type_),
            ],
            &[
                (binding.element, symbol),
                (binding.name, symbol),
                (observed, symbol),
            ],
        );
    }

    let source = concat!(
        "let key = 'missing';\n",
        "const { [key]: inferred = 'fallback' } = {};\n",
        "const { [key]: annotated = 'fallback' }: {} = {};\n",
    );
    let parsed = parse_source_file(source);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let inferred = binding_parts(&parsed, "inferred");
    let annotated = binding_parts(&parsed, "annotated");
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("a default must not hide the declared type's missing index signature")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2537);
    assert_eq!(diagnostic.node, annotated.key);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type '{}' has no matching index signature for type 'string'."
    );
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    let (inferred_type, inferred_symbol) = assert_binding(&mut context, &inferred, "\"fallback\"");
    let (annotated_type, annotated_symbol) = assert_binding(&mut context, &annotated, "any");
    assert_eq!(
        annotated_type,
        context.store().intrinsic_bootstrap().unwrap().error_type
    );
    assert_replay(
        &mut context,
        &[
            (inferred.element, inferred_type),
            (inferred.name, inferred_type),
            (annotated.element, annotated_type),
            (annotated.name, annotated_type),
        ],
        &[
            (inferred.name, inferred_symbol),
            (annotated.name, annotated_symbol),
        ],
    );
}

#[test]
fn broad_computed_rest_keys_stay_unsupported_without_a_rest_type() {
    for (key_value, input) in [("'value'", "{ value: 1 }"), ("1", "{ 1: 'ready' }")] {
        let source =
            format!("let key = {key_value}; const {{ [key]: selected, ...rest }} = {input};");
        let parsed = parse_source_file(&source);
        let mut context = context(&parsed);
        let rest = binding_parts(&parsed, "rest");
        let symbol = context.file(FILE).unwrap().1.symbol(rest.element).unwrap();
        let error = context.check_source_file(FILE).unwrap_err();
        assert!(
            matches!(error, SourceCheckError::Unsupported(_)),
            "{source}: {error:?}"
        );
        let diagnostics = context.diagnostics().clone();
        assert_eq!(
            context.check_source_file(FILE).unwrap_err(),
            error,
            "{source}"
        );
        assert_eq!(
            context.get_type_at_location(rest.name).unwrap_err(),
            CanonicalArtifactQueryError::SourceCheck(error),
            "{source}"
        );
        assert_eq!(context.diagnostics(), &diagnostics);
        assert!(!is_checked(&context));
        assert!(
            context
                .store()
                .value_symbol_links(symbol)
                .is_none_or(|links| links.resolved_type.is_none())
        );
    }
}
