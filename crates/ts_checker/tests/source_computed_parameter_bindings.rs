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

const FILE: FileId = FileId::new(19_800);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/computed-parameter-bindings.ts\""),
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

struct FunctionParts {
    declaration: NodeRef,
    name: NodeRef,
    parameter: NodeRef,
    annotation: NodeRef,
    body: NodeRef,
}

fn function_parts(parsed: &ParseResult, expected: &str) -> FunctionParts {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::FunctionDeclaration(function) = &record.data else {
                return None;
            };
            let name = function.name?;
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            if identifier.text != expected {
                return None;
            }
            let [parameter] = function.parameters.nodes.as_slice() else {
                panic!("the control must retain one object parameter")
            };
            let NodeData::ParameterDeclaration(data) = &parsed.arena.get(*parameter)?.data else {
                panic!("expected a parameter declaration")
            };
            Some(FunctionParts {
                declaration: node(parsed, id),
                name: node(parsed, name),
                parameter: node(parsed, *parameter),
                annotation: node(parsed, data.type_.unwrap()),
                body: node(parsed, function.body.unwrap()),
            })
        })
        .unwrap_or_else(|| panic!("missing function {expected}"))
}

struct BindingParts {
    element: NodeRef,
    name: NodeRef,
    key: Option<NodeRef>,
}

fn binding_parts(parsed: &ParseResult, function: &FunctionParts, expected: &str) -> BindingParts {
    let NodeData::ParameterDeclaration(parameter) =
        &parsed.arena.get(function.parameter.node).unwrap().data
    else {
        unreachable!()
    };
    let pattern_record = parsed.arena.get(parameter.name).unwrap();
    assert_eq!(pattern_record.kind, SyntaxKind::ObjectBindingPattern);
    let NodeData::BindingPattern(pattern) = &pattern_record.data else {
        panic!("expected the original object binding pattern")
    };
    pattern
        .elements
        .nodes
        .iter()
        .find_map(|&id| {
            let NodeData::BindingElement(binding) = &parsed.arena.get(id)?.data else {
                return None;
            };
            let name = binding.name?;
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            if identifier.text != expected {
                return None;
            }
            let key = binding.property_name.and_then(|property| {
                let NodeData::ComputedPropertyName(computed) = &parsed.arena.get(property)?.data
                else {
                    return None;
                };
                Some(node(parsed, computed.expression))
            });
            Some(BindingParts {
                element: node(parsed, id),
                name: node(parsed, name),
                key,
            })
        })
        .unwrap_or_else(|| panic!("missing binding {expected}"))
}

fn body_read(parsed: &ParseResult, function: &FunctionParts, expected: &str) -> NodeRef {
    let body = parsed.arena.get(function.body.node).unwrap().range;
    let mut nodes = parsed.arena.iter().filter_map(|(id, record)| {
        let NodeData::Identifier(identifier) = &record.data else {
            return None;
        };
        (identifier.text == expected
            && record.range.start >= body.start
            && record.range.end <= body.end)
            .then_some(node(parsed, id))
    });
    let result = nodes
        .next()
        .unwrap_or_else(|| panic!("missing {expected} read"));
    assert!(nodes.next().is_none(), "expected one {expected} read");
    result
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

fn named_value_declaration(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let name = match &record.data {
                NodeData::VariableDeclaration(variable) => variable.name,
                NodeData::FunctionDeclaration(function) => function.name?,
                _ => return None,
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(name)?.data else {
                return None;
            };
            (identifier.text == expected).then_some(node(parsed, id))
        })
        .unwrap_or_else(|| panic!("missing declaration {expected}"))
}

fn symbol(context: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    context.store().get_merged_symbol(raw).unwrap()
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
    function: &FunctionParts,
    binding: &BindingParts,
    expected: TypeId,
) -> SemanticSymbolId {
    let parent = symbol(context, function.parameter);
    let leaf = symbol(context, binding.element);
    assert_ne!(parent, leaf);
    let record = context.store().symbol(leaf).unwrap();
    assert_eq!(record.flags(), SymbolFlags::FUNCTION_SCOPED_VARIABLE);
    assert_eq!(record.declarations(), Some(&[binding.element][..]));
    assert_eq!(record.value_declaration(), Some(binding.element));
    for location in [binding.element, binding.name] {
        assert_eq!(context.get_type_at_location(location).unwrap(), expected);
        assert_eq!(
            context.get_symbol_at_location(location).unwrap(),
            Some(leaf)
        );
    }
    assert_eq!(
        context.get_symbol_declarations(leaf).unwrap(),
        &[binding.element]
    );
    leaf
}

fn assert_function(
    context: &mut CanonicalCheckerContext<'_>,
    function: &FunctionParts,
    expected_return: TypeId,
    expected_display: &str,
) -> (TypeId, TypeId, SemanticSymbolId) {
    let owner = symbol(context, function.declaration);
    let parent = symbol(context, function.parameter);
    let callable = context.get_type_at_location(function.name).unwrap();
    let parent_type = context.get_type_at_location(function.parameter).unwrap();
    assert_eq!(context.type_to_string(callable).unwrap(), expected_display);
    assert_eq!(
        context.store().type_payload(callable).unwrap().symbol(),
        Some(owner)
    );
    assert_eq!(
        context.get_type_at_location(function.annotation).unwrap(),
        parent_type
    );
    assert_eq!(
        context.get_symbol_at_location(function.parameter).unwrap(),
        Some(parent)
    );
    assert_eq!(
        context.get_symbol_declarations(parent).unwrap(),
        &[function.parameter]
    );
    let signature = context
        .store()
        .signature_links(function.declaration)
        .and_then(|links| links.resolved_signature.signature())
        .unwrap();
    let record = context.store().signature(signature).unwrap();
    assert_eq!(record.parameters(), &[parent]);
    assert_eq!(record.min_argument_count(), 1);
    assert_eq!(record.resolved_return_type(), Some(expected_return));
    (callable, parent_type, parent)
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    functions: &[NodeRef],
    types: &[(NodeRef, TypeId)],
    symbols: &[(NodeRef, SemanticSymbolId)],
) {
    let before = counts(context);
    let diagnostics = context.diagnostics().clone();
    let signatures = functions
        .iter()
        .map(|&node| (node, context.store().signature_links(node).cloned()))
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
    for (function, expected) in signatures {
        assert_eq!(context.store().signature_links(function).cloned(), expected);
    }
    assert_eq!(context.diagnostics(), &diagnostics);
    assert_eq!(counts(context), before);
    assert!(is_checked(context));
}

#[test]
fn original_computed_parameter_forms_keep_key_types_diagnostics_and_displays() {
    let source = concat!(
        "let foo = \"bar\";\n",
        "let foo2 = () => \"bar\";\n",
        "function f1({[\"bar\"]: x}: { bar: number }) {}\n",
        "function f2({[foo]: x}: { bar: number }) {}\n",
        "function f3({[foo2()]: x}: { bar: number }) {}\n",
    );
    let parsed = parse_source_file(source);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let string = bootstrap.string_type;
    let error = bootstrap.error_type;
    let void = bootstrap.void_type;
    let mut functions = Vec::new();
    let mut types = Vec::new();
    let mut symbols = Vec::new();
    let mut diagnostic_nodes = Vec::new();
    let mut leaves = Vec::new();
    for (name, key_text, expected) in [
        ("f1", "\"bar\"", number),
        ("f2", "foo", error),
        ("f3", "foo2()", error),
    ] {
        let function = function_parts(&parsed, name);
        let binding = binding_parts(&parsed, &function, "x");
        let key = binding.key.unwrap();
        let leaf = assert_binding(&mut context, &function, &binding, expected);
        assert!(!leaves.contains(&leaf));
        leaves.push(leaf);
        let (callable, parent_type, parent) = assert_function(
            &mut context,
            &function,
            void,
            &format!("({{ [{key_text}]: x }}: {{ bar: number; }}) => void"),
        );
        let key_type = context.get_type_at_location(key).unwrap();
        assert_eq!(node_text(source, &parsed, key), key_text);
        if expected == number {
            assert_eq!(context.type_to_string(key_type).unwrap(), "\"bar\"");
        } else {
            assert_eq!(key_type, string);
            diagnostic_nodes.push(key);
        }
        functions.push(function.declaration);
        types.extend([
            (function.name, callable),
            (function.parameter, parent_type),
            (function.annotation, parent_type),
            (binding.element, expected),
            (binding.name, expected),
            (key, key_type),
        ]);
        symbols.extend([
            (function.parameter, parent),
            (binding.element, leaf),
            (binding.name, leaf),
        ]);
    }
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 2);
    for (diagnostic, key) in diagnostics.iter().zip(diagnostic_nodes) {
        assert_eq!(diagnostic.diagnostic.code(), 2537);
        assert_eq!(diagnostic.node, Some(key));
        assert_eq!(
            diagnostic.diagnostic.render().unwrap(),
            "Type '{ bar: number; }' has no matching index signature for type 'string'."
        );
        assert_eq!(diagnostic.range_override, None);
        assert!(diagnostic.related_information.is_empty());
    }
    assert_replay(&mut context, &functions, &types, &symbols);
}

#[test]
fn fixed_external_parameter_keys_keep_leaf_return_and_call_types() {
    for (prefix, key, member, expected_key) in [
        ("const key = 'value';", "key", "value", "\"value\""),
        (
            "function key(): 'value' { return 'value'; }",
            "key()",
            "value",
            "\"value\"",
        ),
        ("const key = 1;", "key", "1", "1"),
    ] {
        let source = format!(
            "{prefix}\nfunction read({{ [{key}]: chosen }}: {{ {member}: number }}) {{ return chosen; }}\n\
             const result = read({{ {member}: 1 }});",
        );
        let parsed = parse_source_file(&source);
        let mut context = context(&parsed);
        let function = function_parts(&parsed, "read");
        let binding = binding_parts(&parsed, &function, "chosen");
        assert!(!is_checked(&context));
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let leaf = assert_binding(&mut context, &function, &binding, number);
        assert!(is_checked(&context));
        let (callable, parent_type, parent) = assert_function(
            &mut context,
            &function,
            number,
            &format!("({{ [{key}]: chosen }}: {{ {member}: number; }}) => number"),
        );
        let key = binding.key.unwrap();
        let key_type = context.get_type_at_location(key).unwrap();
        assert_eq!(context.type_to_string(key_type).unwrap(), expected_key);
        let key_read = match &parsed.arena.get(key.node).unwrap().data {
            NodeData::CallExpression(call) => node(&parsed, call.expression),
            NodeData::Identifier(_) => key,
            _ => panic!("the fixed key must retain its original identifier or call"),
        };
        let key_declaration = named_value_declaration(&parsed, "key");
        let key_symbol = symbol(&context, key_declaration);
        assert_ne!(key_symbol, parent);
        assert_ne!(key_symbol, leaf);
        assert_eq!(
            context.get_symbol_at_location(key_read).unwrap(),
            Some(key_symbol)
        );
        assert_eq!(
            context.get_symbol_declarations(key_symbol).unwrap(),
            &[key_declaration]
        );
        let read = body_read(&parsed, &function, "chosen");
        let call = variable_initializer(&parsed, "result");
        assert_eq!(context.get_type_at_location(read).unwrap(), number);
        assert_eq!(context.get_symbol_at_location(read).unwrap(), Some(leaf));
        assert_eq!(context.get_type_at_location(call).unwrap(), number);
        assert!(context.diagnostics().is_empty());
        assert_replay(
            &mut context,
            &[function.declaration],
            &[
                (function.name, callable),
                (function.parameter, parent_type),
                (function.annotation, parent_type),
                (binding.element, number),
                (binding.name, number),
                (key, key_type),
                (read, number),
                (call, number),
            ],
            &[
                (function.parameter, parent),
                (binding.element, leaf),
                (binding.name, leaf),
                (key_read, key_symbol),
                (read, leaf),
            ],
        );
    }
}

#[test]
fn computed_parameter_bindings_keep_explicit_return_diagnostics() {
    let source = concat!(
        "const key = 'value';\n",
        "function read({ [key]: chosen }: { value: number }): string { return chosen; }\n",
        "const result = read({ value: 1 });",
    );
    let parsed = parse_source_file(source);
    let mut context = context(&parsed);
    context.check_source_file(FILE).unwrap();
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let string = bootstrap.string_type;
    let function = function_parts(&parsed, "read");
    let binding = binding_parts(&parsed, &function, "chosen");
    let leaf = assert_binding(&mut context, &function, &binding, number);
    let (callable, parent_type, parent) = assert_function(
        &mut context,
        &function,
        string,
        "({ [key]: chosen }: { value: number; }) => string",
    );
    let read = body_read(&parsed, &function, "chosen");
    let statement = node(
        &parsed,
        parsed.arena.get(read.node).unwrap().parent.unwrap(),
    );
    assert_eq!(
        parsed.arena.get(statement.node).unwrap().kind,
        SyntaxKind::ReturnStatement
    );
    let call = variable_initializer(&parsed, "result");
    assert_eq!(context.get_type_at_location(read).unwrap(), number);
    assert_eq!(context.get_symbol_at_location(read).unwrap(), Some(leaf));
    assert_eq!(context.get_type_at_location(call).unwrap(), string);
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("the number binding must not satisfy the declared string return type")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(diagnostic.node, Some(statement));
    assert_eq!(node_text(source, &parsed, statement), "return chosen;");
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'number' is not assignable to type 'string'."
    );
    assert_eq!(diagnostic.range_override, None);
    assert!(diagnostic.related_information.is_empty());
    assert_replay(
        &mut context,
        &[function.declaration],
        &[
            (function.name, callable),
            (function.parameter, parent_type),
            (function.annotation, parent_type),
            (binding.element, number),
            (binding.name, number),
            (read, number),
            (call, string),
        ],
        &[
            (function.parameter, parent),
            (binding.element, leaf),
            (binding.name, leaf),
            (read, leaf),
        ],
    );
}

#[test]
fn unsupported_computed_parameter_forms_publish_nothing_on_replay() {
    for source in [
        "const key = 'value'; function read({ [key]: value = 1 }: { value?: number }) { return value; }",
        "const key = 'value'; function read({ [key]: value, ...rest }: { value: number; other: string }) { return value; }",
        "let key = 'value'; function read({ [key]: value, ...rest }: { value: number; other: string }) { return value; }",
        "let key = 1; function read({ [key]: value, ...rest }: { 1: number; other: string }) { return value; }",
        "function read({ [missing]: value }: { value: number }) { return value; }",
        "function read(key: 'value', { [key]: value }: { value: number }) { return value; }",
        "function read(key: () => 'value', { [key()]: value }: { value: number }) { return value; }",
        "const key = 'nested'; function read({ [key]: { value } }: { nested: { value: number } }) { return value; }",
        "const key = 'value'; function read<T>({ [key]: value }: { value: T }) { return value; }",
    ] {
        let parsed = parse_source_file(source);
        let mut context = context(&parsed);
        let before = counts(&context);
        let bindings = parsed
            .arena
            .iter()
            .filter_map(|(id, record)| {
                let NodeData::BindingElement(binding) = &record.data else {
                    return None;
                };
                let name = binding.name?;
                matches!(parsed.arena.get(name)?.data, NodeData::Identifier(_))
                    .then_some((node(&parsed, id), node(&parsed, name)))
            })
            .collect::<Vec<_>>();
        assert!(!bindings.is_empty());
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
            context.recheck_source_file(FILE).unwrap_err(),
            error,
            "{source}"
        );
        for (element, name) in bindings {
            for location in [element, name] {
                assert_eq!(
                    context.get_type_at_location(location).unwrap_err(),
                    CanonicalArtifactQueryError::SourceCheck(error),
                    "{source}"
                );
                assert!(
                    context.store().type_node_links(location).is_none(),
                    "{source}"
                );
            }
        }
        for (id, record) in parsed.arena.iter() {
            if matches!(
                record.kind,
                SyntaxKind::FunctionDeclaration
                    | SyntaxKind::Parameter
                    | SyntaxKind::BindingElement
            ) {
                let declaration = node(&parsed, id);
                if let Some(raw) = context.file(FILE).unwrap().1.symbol(declaration) {
                    let symbol = context.store().get_merged_symbol(raw).unwrap();
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
        assert_eq!(counts(&context), before, "{source}");
        assert!(context.diagnostics().is_empty(), "{source}");
        assert!(!is_checked(&context), "{source}");
    }
}
