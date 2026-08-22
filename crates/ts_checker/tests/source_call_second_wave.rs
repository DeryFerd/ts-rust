use ts_ast::{FileId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
};
use ts_parser::{ParseResult, parse_source_file};

fn context<'arena>(
    library: &'arena ParseResult,
    source: &'arena ParseResult,
    file: FileId,
) -> CanonicalCheckerContext<'arena> {
    let library_file = FileId::new(3_500);
    let mut binder = CanonicalBinder::new();
    for (parsed, file, path) in [
        (library, library_file, "\"/project/lib.d.ts\""),
        (source, file, "\"/project/call-second-wave.ts\""),
    ] {
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
        [(library_file, &library.arena), (file, &source.arena)]
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

#[test]
fn contextual_array_call_arguments_report_each_invalid_element() {
    let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
    let text = concat!(
        "function take(values: number[]): void {}\n",
        "function nested(values: number[][]): void {}\n",
        "take([]);\n",
        "take([1]);\n",
        "take([1, 2]);\n",
        "take([1, 'bad', true]);\n",
        "nested([[1], [2, 'nested']]);\n",
    );
    let parsed = parse_source_file(text);
    assert!(library.diagnostics.is_empty());
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3_501);
    let mut context = context(&library, &parsed, file);

    context.check_source_file(file).unwrap();

    let diagnostics = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.diagnostic.code(),
                node_text(text, &parsed, diagnostic.node.unwrap()),
                diagnostic.diagnostic.render().unwrap(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        diagnostics,
        [
            (
                2322,
                "'bad'",
                "Type 'string' is not assignable to type 'number'.".to_owned(),
            ),
            (
                2322,
                "true",
                "Type 'boolean' is not assignable to type 'number'.".to_owned(),
            ),
            (
                2322,
                "'nested'",
                "Type 'string' is not assignable to type 'number'.".to_owned(),
            ),
        ]
    );
    let counts = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(context.diagnostics().len(), 3);
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        counts
    );
}

#[test]
fn asserted_object_call_arguments_use_the_asserted_type() {
    let library = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
    let text = concat!(
        "type Shape = { id: number };\n",
        "function accept(value: Shape): void {}\n",
        "accept(<Shape>({}));\n",
        "accept(({} as Shape));\n",
        "accept(<{ id: number }>({}));\n",
        "accept(({} as { id: number }));\n",
    );
    let parsed = parse_source_file(text);
    assert!(library.diagnostics.is_empty());
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3_502);
    let mut context = context(&library, &parsed, file);

    context.check_source_file(file).unwrap();

    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    let calls = parsed
        .arena
        .iter()
        .filter_map(|(node, record)| {
            (record.kind == SyntaxKind::CallExpression).then_some(NodeRef::new(
                parsed.arena.id(),
                file,
                node,
            ))
        })
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 4);
    assert!(calls.iter().all(|call| {
        context
            .store()
            .signature_links(*call)
            .and_then(|links| links.resolved_signature.signature())
            .is_some()
    }));
}
