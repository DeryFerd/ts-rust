use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, SourceCheckError,
    SourceFunctionUnsupported, TypeId, UnsupportedSourceSyntax,
};
use ts_parser::{ParseResult, parse_source_file};

const LIBRARY: &str = "interface Array<T> {} interface ReadonlyArray<T> {}";

const SUCCESS_SOURCE: &str = concat!(
    "const beforeDeclaration = numberValue();\n",
    "function numberValue() { return 1; }\n",
    "function empty() {}\n",
    "function echo(value: string) { return value; }\n",
    "function annotated(value: number): string { return \"ok\"; }\n",
    "function throughAnnotated() { return annotated(1); }\n",
    "function defaulted(value: number = 1) { return value; }\n",
    "function optionalArray(xs?: number[]) { return 1; }\n",
    "function defaultArray(xs: number[] = [1]) { return xs; }\n",
    "function arrayValue() { return [1, 2]; }\n",
    "function objectValue() { return { value: 1 }; }\n",
    "function nestedArrayObject() { return { values: [1] }; }\n",
    "const emptyResult = empty();\n",
    "const echoed = echo(\"value\");\n",
    "const annotatedResult = throughAnnotated();\n",
    "const defaultedResult = defaulted();\n",
    "const optionalArrayResult = optionalArray();\n",
    "const defaultArrayResult = defaultArray();\n",
    "const arrayResult = arrayValue();\n",
    "const objectResult = objectValue();\n",
    "const nestedArrayObjectResult: { values: number[] } = nestedArrayObject();\n",
    "const concise = (value: number) => value;\n",
    "const conciseResult = concise(1);\n",
    "const defaultedArrow = (value: number = 2) => value;\n",
    "const defaultedArrowResult = defaultedArrow();\n",
    "const block = () => { return true; };\n",
    "const blockResult = block();\n",
    "const emptyArrow = () => {};\n",
    "const emptyArrowResult = emptyArrow();\n",
);

const MUTABLE_CAPTURE_SOURCE: &str = concat!(
    "let x: string | number = 1;\n",
    "const f = () => x;\n",
    "const n: number = f();\n",
);

const INFERRED_DIAGNOSTIC_ORDER_SOURCE: &str = concat!(
    "const before = inferred();\n",
    "const top: string = 1;\n",
    "function inferred(value: number = \"bad\") { return value + true; }\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/inferred-returns.ts\""),
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
        CanonicalCheckerOptions::default(),
    )
    .unwrap()
}

fn context_with_library<'a>(
    library: &'a ParseResult,
    library_file: FileId,
    parsed: &'a ParseResult,
    file: FileId,
) -> CanonicalCheckerContext<'a> {
    let mut binder = CanonicalBinder::new();
    for (parsed, file, name) in [
        (library, library_file, "\"/project/lib.d.ts\""),
        (parsed, file, "\"/project/inferred-returns.ts\""),
    ] {
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(name),
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
        [(library_file, &library.arena), (file, &parsed.arena)]
            .into_iter()
            .collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node_text<'source>(source: &'source str, parsed: &ParseResult, node: NodeRef) -> &'source str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn call_expression(source: &str, parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let node = NodeRef::new(parsed.arena.id(), file, node);
            (record.kind == SyntaxKind::CallExpression
                && node_text(source, parsed, node) == expected)
                .then_some(node)
        })
        .unwrap_or_else(|| panic!("missing call expression {expected:?}"))
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing resolved type for {node:?}"))
}

#[test]
fn inferred_functions_and_arrows_publish_before_direct_use_and_replay_warm() {
    let library = parse_source_file(LIBRARY);
    assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
    let parsed = parse_source_file(SUCCESS_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let library_file = FileId::new(0);
    let file = FileId::new(1);
    let mut context = context_with_library(&library, library_file, &parsed, file);

    if let Err(error) = context.check_source_file(file) {
        match error {
            SourceCheckError::Call(node) => {
                panic!(
                    "call failed at {:?}: {error:?}",
                    node_text(SUCCESS_SOURCE, &parsed, node)
                )
            }
            _ => panic!("source check failed: {error:?}"),
        }
    }
    assert!(context.diagnostics().is_empty());
    for (call_text, expected) in [
        ("numberValue()", "number"),
        ("empty()", "void"),
        ("echo(\"value\")", "string"),
        ("throughAnnotated()", "string"),
        ("defaulted()", "number"),
        ("optionalArray()", "number"),
        ("defaultArray()", "number[]"),
        ("arrayValue()", "number[]"),
        ("objectValue()", "{ value: number; }"),
        ("nestedArrayObject()", "{ values: number[]; }"),
        ("concise(1)", "number"),
        ("defaultedArrow()", "number"),
        ("block()", "boolean"),
        ("emptyArrow()", "void"),
    ] {
        let call = call_expression(SUCCESS_SOURCE, &parsed, file, call_text);
        let rendered = context
            .type_to_string(resolved_type(&context, call))
            .unwrap_or_else(|error| panic!("failed to render {call_text}: {error:?}"));
        assert_eq!(rendered, expected,);
    }

    let counts = (context.store().type_len(), context.store().signature_len());
    let diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(
        (context.store().type_len(), context.store().signature_len()),
        counts
    );
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
fn inferred_arrow_mutable_capture_uses_declared_type_and_replays_diagnostic() {
    let parsed = parse_source_file(MUTABLE_CAPTURE_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(7);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    let call = call_expression(MUTABLE_CAPTURE_SOURCE, &parsed, file, "f()");
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, call))
            .unwrap(),
        "string | number",
    );
    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one capture assignment diagnostic")
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'string | number' is not assignable to type 'number'.",
    );

    let counts = (context.store().type_len(), context.store().signature_len());
    let diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(
        (context.store().type_len(), context.store().signature_len()),
        counts,
    );
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
fn inferred_function_diagnostics_replay_at_the_declaration_slot() {
    let parsed = parse_source_file(INFERRED_DIAGNOSTIC_ORDER_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(8);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();
    let diagnostics = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.diagnostic.code(),
                node_text(
                    INFERRED_DIAGNOSTIC_ORDER_SOURCE,
                    &parsed,
                    diagnostic.node.unwrap(),
                ),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        diagnostics,
        [
            (2322, "top"),
            (2322, "value: number = \"bad\""),
            (2365, "value + true"),
        ],
    );

    let counts = (context.store().type_len(), context.store().signature_len());
    let diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(
        (context.store().type_len(), context.store().signature_len()),
        counts,
    );
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
fn inferred_switch_returns_merge_grouped_literal_clauses() {
    let source = concat!(
        "function describe(level: number) {\n",
        "  switch (level) {\n",
        "    case 0:\n",
        "    case 1:\n",
        "      return 'ready';\n",
        "    default:\n",
        "      return 'fallback';\n",
        "  }\n",
        "}\n",
        "const result = describe(1);\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(9);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    assert!(context.diagnostics().is_empty());
    let call = call_expression(source, &parsed, file, "describe(1)");
    assert_eq!(
        context
            .type_to_string(resolved_type(&context, call))
            .unwrap(),
        "string"
    );

    let warm = (
        context.store().type_len(),
        context.store().signature_len(),
        context.diagnostics().clone(),
    );
    context.recheck_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().signature_len(),
            context.diagnostics().clone(),
        ),
        warm,
    );
}

fn assert_function_boundary_before_publication(
    source: &str,
    file: FileId,
    expected: impl FnOnce(&SourceCheckError) -> bool,
) {
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let source_record = parsed.arena.get(parsed.source_file).unwrap();
    let NodeData::SourceFile(source_data) = &source_record.data else {
        panic!("expected source file")
    };
    let declaration = source_data
        .statements
        .nodes
        .iter()
        .find_map(|node| {
            (parsed.arena.get(*node)?.kind == SyntaxKind::FunctionDeclaration)
                .then_some(NodeRef::new(parsed.arena.id(), file, *node))
        })
        .expect("expected function declaration");
    let mut context = context(&parsed, file);
    let owner = context.file(file).unwrap().1.symbol(declaration).unwrap();
    let before = (context.store().type_len(), context.store().signature_len());

    let error = context.check_source_file(file).unwrap_err();
    assert!(expected(&error), "unexpected error: {error:?}");
    assert_eq!(
        (context.store().type_len(), context.store().signature_len()),
        before
    );
    assert!(context.store().value_symbol_links(owner).is_none());
    assert!(context.store().signature_links(declaration).is_none());
    assert!(context.diagnostics().is_empty());
}

#[test]
fn inferred_function_dependency_boundaries_precede_callable_publication() {
    let cases = [
        (
            "function recursive() { return recursive(); }",
            FileId::new(2),
        ),
        (
            concat!(
                "function first() { return second(); }\n",
                "function second() { return 1; }",
            ),
            FileId::new(3),
        ),
        (
            concat!(
                "const captured = 1;\n",
                "function readsOuter() { return captured; }",
            ),
            FileId::new(4),
        ),
    ];
    for (source, file) in cases {
        assert_function_boundary_before_publication(source, file, |error| {
            matches!(
                error,
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
                    SourceFunctionUnsupported::FunctionBody(_)
                ))
            )
        });
    }
}

#[test]
fn generic_inferred_and_multiple_returns_precede_callable_publication() {
    assert_function_boundary_before_publication(
        "function identity<T>(value: T) { return value; }",
        FileId::new(5),
        |error| {
            matches!(
                error,
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
                    SourceFunctionUnsupported::Callable(_)
                ))
            )
        },
    );
    assert_function_boundary_before_publication(
        "function multiple() { return 1; return 2; }",
        FileId::new(6),
        |error| {
            matches!(
                error,
                SourceCheckError::Unsupported(UnsupportedSourceSyntax::Function(
                    SourceFunctionUnsupported::FunctionBody(_)
                ))
            )
        },
    );
}
