use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName, SemanticSymbolId, SymbolFlags,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SignatureId,
    SourceCheckError, SourceFunctionUnsupported, TypeData, TypeId, UnsupportedSourceSyntax,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: FileId = FileId::new(53_300);
const FILE: FileId = FileId::new(53_301);
const ES5: &str = include_str!("../../ts_bundled/libs/lib.es5.d.ts");

fn context<'arena>(
    library: &'arena ParseResult,
    source: &'arena ParseResult,
) -> CanonicalCheckerContext<'arena> {
    let files = [
        (LIBRARY, library, "\"/lib.es5.d.ts\"", true),
        (FILE, source, "\"/methods.ts\"", false),
    ];
    let mut binder = CanonicalBinder::new();
    for (file, parsed, path, library) in files {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new_with_default_library(
                    EscapedName::source(path),
                    CanonicalSourceLanguage::TypeScript,
                    library,
                    library,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
    }
    for (file, parsed, _, _) in files {
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
    }
    CanonicalCheckerContext::new(
        binder.finish(),
        files
            .into_iter()
            .map(|(file, parsed, _, _)| (file, &parsed.arena))
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types: false,
            },
            no_implicit_any: true,
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node_text<'source>(source: &'source str, parsed: &ParseResult, node: NodeRef) -> &'source str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn method(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::MethodDeclaration(method) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(method.name)?.data else {
                return None;
            };
            if name.text != expected {
                return None;
            }
            assert_eq!(record.kind, SyntaxKind::MethodDeclaration);
            assert_eq!(
                parsed.arena.get(record.parent.unwrap()).unwrap().kind,
                SyntaxKind::ObjectLiteralExpression,
            );
            Some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap_or_else(|| panic!("missing actual object method {expected}"))
}

fn initializer(parsed: &ParseResult, expected: &str) -> NodeRef {
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
                .map(|node| NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap_or_else(|| panic!("missing initializer for {expected}"))
}

fn symbol(checker: &CanonicalCheckerContext<'_>, declaration: NodeRef) -> SemanticSymbolId {
    let raw = checker.file(FILE).unwrap().1.symbol(declaration).unwrap();
    checker.store().get_merged_symbol(raw).unwrap()
}

fn signature(checker: &CanonicalCheckerContext<'_>, node: NodeRef) -> SignatureId {
    checker
        .store()
        .signature_links(node)
        .unwrap()
        .resolved_signature
        .signature()
        .unwrap()
}

#[derive(Debug, Eq, PartialEq)]
struct MethodState {
    owner: SemanticSymbolId,
    callable: TypeId,
    signature: SignatureId,
    parameters: Vec<(SemanticSymbolId, TypeId)>,
    returned: TypeId,
}

fn method_state(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    declaration: NodeRef,
) -> MethodState {
    let NodeData::MethodDeclaration(method) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("expected a method declaration");
    };
    let node_ref = |node| NodeRef::new(parsed.arena.id(), FILE, node);
    let owner = symbol(checker, declaration);
    let callable = checker.get_type_at_location(declaration).unwrap();
    assert_eq!(
        checker.get_type_at_location(node_ref(method.name)),
        Ok(callable)
    );
    assert_eq!(
        checker.get_symbol_at_location(node_ref(method.name)),
        Ok(Some(owner))
    );
    let record = checker.store().symbol(owner).unwrap();
    assert_eq!(record.flags(), SymbolFlags::METHOD);
    assert_eq!(record.declarations(), Some(&[declaration][..]));
    assert_eq!(record.value_declaration(), Some(declaration));
    assert_eq!(
        checker
            .store()
            .value_symbol_links(owner)
            .unwrap()
            .resolved_type,
        Some(callable),
    );
    let signature = signature(checker, declaration);
    let record = checker.store().type_payload(callable).unwrap();
    assert_eq!(record.symbol(), Some(owner));
    let TypeData::Object(object) = record.data() else {
        panic!("the method must have a callable object");
    };
    assert_eq!(object.structured.call_signature_count, 1);
    assert_eq!(
        object.structured.signatures.as_deref(),
        Some(&[signature][..])
    );
    let parameters = method
        .parameters
        .nodes
        .iter()
        .map(|&node| {
            let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(node).unwrap().data
            else {
                panic!("expected an ordinary method parameter");
            };
            let owner = symbol(checker, node_ref(node));
            let type_ = checker
                .get_type_at_location(node_ref(parameter.name))
                .unwrap();
            assert_eq!(checker.get_type_at_location(node_ref(node)), Ok(type_));
            assert_eq!(
                checker.get_symbol_at_location(node_ref(parameter.name)),
                Ok(Some(owner))
            );
            assert_eq!(
                checker
                    .store()
                    .value_symbol_links(owner)
                    .unwrap()
                    .resolved_type,
                Some(type_),
            );
            (owner, type_)
        })
        .collect::<Vec<_>>();
    let returned = checker.get_return_type_of_signature(signature).unwrap();
    let record = checker.store().signature(signature).unwrap();
    assert_eq!(record.declaration(), Some(declaration));
    assert_eq!(
        record.parameters(),
        parameters
            .iter()
            .map(|&(owner, _)| owner)
            .collect::<Vec<_>>()
    );
    assert!(record.type_parameters().is_empty());
    assert_eq!(record.this_parameter(), None);
    assert_eq!(record.target(), None);
    assert_eq!(record.mapper(), None);
    assert_eq!(record.resolved_return_type(), Some(returned));
    MethodState {
        owner,
        callable,
        signature,
        parameters,
        returned,
    }
}

fn allocations(checker: &CanonicalCheckerContext<'_>) -> [usize; 7] {
    let store = checker.store();
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

fn assert_replay(
    checker: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    methods: &[NodeRef],
    locations: &[NodeRef],
) {
    let states = methods
        .iter()
        .map(|&node| method_state(checker, parsed, node))
        .collect::<Vec<_>>();
    let queries = locations
        .iter()
        .map(|&node| {
            let type_ = checker.get_type_at_location(node).unwrap();
            (type_, checker.store().signature_links(node).cloned())
        })
        .collect::<Vec<_>>();
    let diagnostics = checker.diagnostics().clone();
    let before = allocations(checker);
    for _ in 0..2 {
        checker.check_source_file(FILE).unwrap();
        checker.recheck_source_file(FILE).unwrap();
        for (&method, expected) in methods.iter().zip(&states) {
            assert_eq!(&method_state(checker, parsed, method), expected);
        }
        for (&node, (expected, signature)) in locations.iter().zip(&queries) {
            assert_eq!(checker.get_type_at_location(node), Ok(*expected));
            assert_eq!(checker.store().signature_links(node), signature.as_ref());
        }
        assert_eq!(checker.diagnostics(), &diagnostics);
        assert_eq!(allocations(checker), before);
    }
}

fn assert_diagnostics(
    checker: &CanonicalCheckerContext<'_>,
    source: &str,
    parsed: &ParseResult,
    expected: &[(u32, &str, &str)],
) {
    let actual = checker.diagnostics().as_slice();
    assert_eq!(actual.len(), expected.len(), "{actual:?}");
    for (diagnostic, &(code, text, message)) in actual.iter().zip(expected) {
        assert_eq!(diagnostic.diagnostic.code(), code);
        assert_eq!(node_text(source, parsed, diagnostic.node.unwrap()), text);
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.render().unwrap(), message);
    }
}

#[test]
fn annotated_and_inferred_object_methods_keep_real_call_signatures_and_replay() {
    let library = parse_source_file(ES5);
    let source = concat!(
        "const object = { ",
        "identity(value: number): number { return value; }, ",
        "inferred(value: string) { return value; }, ",
        "literal() { return 1; } };\n",
        "const typed = object.identity(1);\n",
        "const inferred = object.inferred('ready');\n",
        "const literal = object.literal();",
    );
    let parsed = parse_source_file(source);
    let methods = ["identity", "inferred", "literal"].map(|name| method(&parsed, name));
    let calls = ["typed", "inferred", "literal"].map(|name| initializer(&parsed, name));
    for source_first in [false, true] {
        let mut checker = context(&library, &parsed);
        if source_first {
            checker.check_source_file(FILE).unwrap();
        } else {
            checker.get_type_at_location(methods[1]).unwrap();
        }
        assert_diagnostics(&checker, source, &parsed, &[]);
        assert!(
            checker
                .store()
                .source_file_links(checker.source_file(FILE).unwrap())
                .unwrap()
                .type_checked
        );
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        let expected_returns = [
            bootstrap.number_type,
            bootstrap.string_type,
            bootstrap.number_type,
        ];
        for ((&declaration, &call), expected) in methods.iter().zip(&calls).zip(expected_returns) {
            let state = method_state(&mut checker, &parsed, declaration);
            assert_eq!(state.returned, expected);
            assert_eq!(checker.get_type_at_location(call), Ok(expected));
            assert_eq!(signature(&checker, call), state.signature);
            let NodeData::CallExpression(call) = &parsed.arena.get(call.node).unwrap().data else {
                panic!("expected a direct method call");
            };
            let member = NodeRef::new(parsed.arena.id(), FILE, call.expression);
            assert_eq!(checker.get_type_at_location(member), Ok(state.callable));
            let selected = checker.get_symbol_at_location(member).unwrap().unwrap();
            assert_ne!(selected, state.owner);
            assert_eq!(
                checker.store().symbol(selected).unwrap().flags(),
                SymbolFlags::METHOD | SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT,
            );
            assert_eq!(
                checker.store().value_symbol_links(selected).unwrap().target,
                Some(state.owner),
            );
            for &(_, parameter_type) in &state.parameters {
                assert_eq!(parameter_type, expected);
            }
        }
        assert_replay(&mut checker, &parsed, &methods, &calls);
    }
}

#[test]
fn object_method_defaults_bodies_and_calls_keep_exact_diagnostics() {
    let library = parse_source_file(ES5);
    let source = concat!(
        "const object = { typed(value: number = 'wrong'): number { return 'bad'; } };\n",
        "const omitted = object.typed();\n",
        "const invalid = object.typed('argument');",
    );
    let parsed = parse_source_file(source);
    let mut checker = context(&library, &parsed);
    checker.check_source_file(FILE).unwrap();
    assert_diagnostics(
        &checker,
        source,
        &parsed,
        &[
            (
                2322,
                "value: number = 'wrong'",
                "Type 'string' is not assignable to type 'number'.",
            ),
            (
                2322,
                "return 'bad';",
                "Type 'string' is not assignable to type 'number'.",
            ),
            (
                2345,
                "'argument'",
                "Argument of type '\"argument\"' is not assignable to parameter of type 'number | undefined'.",
            ),
        ],
    );
    let method = method(&parsed, "typed");
    let state = method_state(&mut checker, &parsed, method);
    let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
    assert_eq!(state.returned, number);
    assert_eq!(state.parameters[0].1, number);
    assert_eq!(
        checker
            .store()
            .signature(state.signature)
            .unwrap()
            .min_argument_count(),
        0
    );
    let calls = ["omitted", "invalid"].map(|name| initializer(&parsed, name));
    for call in calls {
        assert_eq!(checker.get_type_at_location(call), Ok(number));
    }
    assert_replay(&mut checker, &parsed, &[method], &calls);
}

#[test]
fn contextual_object_methods_check_parameter_reads_and_linear_bodies() {
    let library = parse_source_file(ES5);
    for body in ["", "const text: string = value;"] {
        let source = format!(
            "interface Shape {{ run(value: number): string; }}\n\
             const object: Shape = {{ run(value) {{ {body} return 'ok'; }} }};\n\
             const result = object.run(1);"
        );
        let parsed = parse_source_file(&source);
        let mut checker = context(&library, &parsed);
        checker.check_source_file(FILE).unwrap();
        let expected = if body.is_empty() {
            Vec::new()
        } else {
            vec![(
                2322,
                "text",
                "Type 'number' is not assignable to type 'string'.",
            )]
        };
        assert_diagnostics(&checker, &source, &parsed, &expected);
        let method = method(&parsed, "run");
        let state = method_state(&mut checker, &parsed, method);
        let bootstrap = checker.store().intrinsic_bootstrap().unwrap();
        assert_eq!(state.parameters[0].1, bootstrap.number_type);
        assert_eq!(state.returned, bootstrap.string_type);
        let call = initializer(&parsed, "result");
        assert_eq!(checker.get_type_at_location(call), Ok(state.returned));
        assert_replay(&mut checker, &parsed, &[method], &[call]);
    }
}

#[test]
fn contextual_object_method_returns_keep_matching_literal_types() {
    let library = parse_source_file(ES5);
    for (parameters, target_parameters, argument) in [
        ("value", "value: number", "1"),
        ("", "", ""),
        ("value: number", "value: number", "1"),
    ] {
        let source = format!(
            "interface Shape {{ run({target_parameters}): 'ok'; }}\n\
             const object: Shape = {{ run({parameters}) {{ return 'ok'; }} }};\n\
             const result = object.run({argument});"
        );
        let parsed = parse_source_file(&source);
        let mut checker = context(&library, &parsed);
        checker.check_source_file(FILE).unwrap();
        assert_diagnostics(&checker, &source, &parsed, &[]);
        let method = method(&parsed, "run");
        let state = method_state(&mut checker, &parsed, method);
        assert_eq!(checker.type_to_string(state.returned).unwrap(), "\"ok\"");
        assert_eq!(state.parameters.len(), usize::from(!parameters.is_empty()));
        let number = checker.store().intrinsic_bootstrap().unwrap().number_type;
        for &(_, type_) in &state.parameters {
            assert_eq!(type_, number);
        }
        let call = initializer(&parsed, "result");
        assert_eq!(checker.get_type_at_location(call), Ok(state.returned));
        assert_replay(&mut checker, &parsed, &[method], &[call]);
    }
}

#[test]
fn contextual_object_method_keeps_a_mismatched_literal_return() {
    let library = parse_source_file(ES5);
    let source = concat!(
        "interface Shape { run(): 1; }\n",
        "const object: Shape = { run() { return 2; } };\n",
        "const result = object.run();",
    );
    let parsed = parse_source_file(source);
    let declaration = method(&parsed, "run");
    let NodeData::MethodDeclaration(data) = &parsed.arena.get(declaration.node).unwrap().data
    else {
        panic!("the source must retain its object method");
    };
    let name = NodeRef::new(parsed.arena.id(), FILE, data.name);
    let target_declaration = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let NodeData::MethodSignatureDeclaration(_) = &record.data else {
                return None;
            };
            Some(NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap();
    let call = initializer(&parsed, "result");
    for source_first in [false, true] {
        let mut checker = context(&library, &parsed);
        if source_first {
            checker.check_source_file(FILE).unwrap();
        } else {
            checker.get_type_at_location(declaration).unwrap();
        }
        let state = method_state(&mut checker, &parsed, declaration);
        assert_eq!(checker.type_to_string(state.returned).unwrap(), "2");
        let TypeData::Literal(literal) =
            checker.store().type_payload(state.returned).unwrap().data()
        else {
            panic!("the mismatched return must keep its numeric literal");
        };
        assert_eq!(literal.regular_type, state.returned);
        let called = checker.get_type_at_location(call).unwrap();
        assert_eq!(checker.type_to_string(called).unwrap(), "1");
        assert_ne!(signature(&checker, call), state.signature);
        let [diagnostic] = checker.diagnostics().as_slice() else {
            panic!("the method must report one contextual return mismatch");
        };
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(diagnostic.node, Some(name));
        assert_eq!(node_text(source, &parsed, name), "run");
        assert_eq!(diagnostic.range_override, None);
        assert_eq!(diagnostic.diagnostic.arguments, ["() => 2", "() => 1"]);
        let [related] = diagnostic.related_information.as_slice() else {
            panic!("the mismatch must retain the target method declaration");
        };
        assert_eq!(related.diagnostic.code(), 6500);
        assert_eq!(related.node, Some(target_declaration));
        assert_eq!(node_text(source, &parsed, target_declaration), "run(): 1;");
        assert_eq!(related.diagnostic.arguments, ["run", "Shape"]);
        assert_replay(&mut checker, &parsed, &[declaration], &[call]);
    }
}

#[test]
fn contextual_object_methods_infer_undefined_for_empty_and_bare_returns() {
    let library = parse_source_file(ES5);
    for (parameters, target_parameters, argument, body) in
        [("", "", "", ""), ("value", "value: number", "1", "return;")]
    {
        let source = format!(
            "interface Shape {{ run({target_parameters}): undefined; }}\n\
             const object: Shape = {{ run({parameters}) {{ {body} }} }};\n\
             const result = object.run({argument});"
        );
        let parsed = parse_source_file(&source);
        let mut checker = context(&library, &parsed);
        checker.check_source_file(FILE).unwrap();
        assert_diagnostics(&checker, &source, &parsed, &[]);
        let method = method(&parsed, "run");
        let state = method_state(&mut checker, &parsed, method);
        let undefined = checker
            .store()
            .intrinsic_bootstrap()
            .unwrap()
            .undefined_type;
        assert_eq!(state.returned, undefined);
        let call = initializer(&parsed, "result");
        assert_eq!(checker.get_type_at_location(call), Ok(undefined));
        assert_replay(&mut checker, &parsed, &[method], &[call]);
    }
}

#[test]
fn uncontextualized_object_method_reports_its_implicit_any_parameter() {
    let library = parse_source_file(ES5);
    let source = "const object = { untyped(value) { return value; } };";
    let parsed = parse_source_file(source);
    let mut checker = context(&library, &parsed);
    checker.check_source_file(FILE).unwrap();
    assert_diagnostics(
        &checker,
        source,
        &parsed,
        &[(
            7006,
            "value",
            "Parameter 'value' implicitly has an 'any' type.",
        )],
    );
    let method = method(&parsed, "untyped");
    let state = method_state(&mut checker, &parsed, method);
    let any = checker.store().intrinsic_bootstrap().unwrap().any_type;
    assert_eq!(state.parameters[0].1, any);
    assert_eq!(state.returned, any);
    assert_replay(&mut checker, &parsed, &[method], &[]);
}

#[test]
fn async_generator_and_generic_object_methods_keep_typed_boundaries() {
    let library = parse_source_file(ES5);
    // Recursive return inference is not part of this ordinary-method slice.
    for source in [
        "const object = { async run() { return 1; } };",
        "const object = { *run() { yield 1; } };",
        "const object = { run<T>(value: T): T { return value; } };",
    ] {
        let parsed = parse_source_file(source);
        let mut checker = context(&library, &parsed);
        let declaration = method(&parsed, "run");
        let expected = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
            SourceFunctionUnsupported::Callable(declaration),
        ));
        assert_eq!(checker.check_source_file(FILE), Err(expected));
        assert_eq!(checker.check_source_file(FILE), Err(expected));
        assert!(checker.diagnostics().is_empty());
        assert!(checker.store().signature_links(declaration).is_none());
    }
}
