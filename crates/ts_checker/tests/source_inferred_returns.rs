use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError, SourceFunctionUnsupported,
    TypeId, UnsupportedSourceSyntax,
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
    "function arrayValue() { return [1, 2]; }\n",
    "function objectValue() { return { value: 1 }; }\n",
    "const emptyResult = empty();\n",
    "const echoed = echo(\"value\");\n",
    "const annotatedResult = throughAnnotated();\n",
    "const arrayResult = arrayValue();\n",
    "const objectResult = objectValue();\n",
    "const concise = (value: number) => value;\n",
    "const conciseResult = concise(1);\n",
    "const block = () => { return true; };\n",
    "const blockResult = block();\n",
    "const emptyArrow = () => {};\n",
    "const emptyArrowResult = emptyArrow();\n",
);

fn context<'a>(parsed: &'a ParseResult, file: FileId) -> CanonicalCheckerContext<'a> {
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
        CanonicalCheckerOptions::default(),
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
        ("arrayValue()", "number[]"),
        ("objectValue()", "{ value: number; }"),
        ("concise(1)", "number"),
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
