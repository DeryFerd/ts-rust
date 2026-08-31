use ts_ast::{FileId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/conditional-operands.ts\""),
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
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node_text(parsed: &ParseResult, node: NodeRef) -> &str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &parsed.arena.source_text().unwrap()[range.start.get() as usize..range.end.get() as usize]
}

fn expression(parsed: &ParseResult, file: FileId, text: &str) -> NodeRef {
    let mut found = parsed.arena.iter().filter_map(|(id, node)| {
        let node_ref = NodeRef::new(parsed.arena.id(), file, id);
        (matches!(
            node.kind,
            SyntaxKind::ConditionalExpression | SyntaxKind::BinaryExpression
        ) && node_text(parsed, node_ref) == text)
            .then_some(node_ref)
    });
    let result = found
        .next()
        .unwrap_or_else(|| panic!("missing expression {text}"));
    assert!(found.next().is_none(), "ambiguous expression {text}");
    result
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap()
}

fn assert_completed(context: &CanonicalCheckerContext<'_>, file: FileId) {
    let source = context.source_file(file).unwrap();
    assert!(
        context
            .store()
            .source_file_links(source)
            .unwrap()
            .type_checked
    );
}

fn assert_warm_replay(
    context: &mut CanonicalCheckerContext<'_>,
    file: FileId,
    expressions: &[NodeRef],
) {
    let identities = expressions
        .iter()
        .map(|node| resolved_type(context, *node))
        .collect::<Vec<_>>();
    let counts = (
        context.store().type_len(),
        context.store().signature_len(),
        context.store().mapper_len(),
        context.store().symbol_len(),
        context.store().symbol_store().checker_created_symbol_len(),
        context.store().symbol_store().symbol_table_len(),
    );
    let diagnostics = context.diagnostics().clone();
    for _ in 0..2 {
        context.recheck_source_file(file).unwrap();
        assert_completed(context, file);
        assert_eq!(
            expressions
                .iter()
                .map(|node| resolved_type(context, *node))
                .collect::<Vec<_>>(),
            identities,
        );
        assert_eq!(
            (
                context.store().type_len(),
                context.store().signature_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
                context.store().symbol_store().checker_created_symbol_len(),
                context.store().symbol_store().symbol_table_len(),
            ),
            counts,
        );
        assert_eq!(context.diagnostics(), &diagnostics);
    }
}

#[test]
fn nullish_comparison_boolean_branches_and_equality_flow_replay() {
    let source = concat!(
        "function isOnline(): boolean { return true; }\n",
        "function canFetch(networkMode: string | undefined): boolean {\n",
        "  return (networkMode ?? 'online') === 'online' ? isOnline() : true;\n",
        "}\n",
        "function present(value: number | undefined): number {\n",
        "  return value !== undefined ? value : 0;\n",
        "}\n",
        "function absent(other: number | undefined): number {\n",
        "  return undefined === other ? 0 : other;\n",
        "}\n",
        "function flags(value: number, online: boolean, offline: boolean): boolean {\n",
        "  return value > 0 ? online : offline;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);
    context.check_source_file(file).unwrap();
    assert!(
        context.diagnostics().is_empty(),
        "{:?}",
        context.diagnostics()
    );
    assert_completed(&context, file);

    let expected = [
        ("networkMode ?? 'online'", "string"),
        ("(networkMode ?? 'online') === 'online'", "boolean"),
        (
            "(networkMode ?? 'online') === 'online' ? isOnline() : true",
            "boolean",
        ),
        ("value !== undefined", "boolean"),
        ("value !== undefined ? value : 0", "number"),
        ("undefined === other", "boolean"),
        ("undefined === other ? 0 : other", "number"),
        ("value > 0 ? online : offline", "boolean"),
    ];
    let nodes = expected.map(|(text, display)| {
        let node = expression(&parsed, file, text);
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, node))
                .unwrap(),
            display,
            "{text}"
        );
        node
    });
    assert_warm_replay(&mut context, file, &nodes);
}

#[test]
fn invalid_condition_operand_and_both_call_branches_keep_diagnostic_order() {
    let source = concat!(
        "function accept(value: number): boolean { return true; }\n",
        "function invalid(value: number): boolean {\n",
        "  return (value - 'condition') > 0 ? accept('true-branch') : accept('false-branch');\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);
    context.check_source_file(file).unwrap();
    assert_completed(&context, file);

    let expected = [
        (2363, "'condition'"),
        (2345, "'true-branch'"),
        (2345, "'false-branch'"),
    ];
    let actual = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            let node = diagnostic.node.unwrap();
            assert!(diagnostic.range_override.is_none());
            let range = parsed.arena.get(node.node).unwrap().range;
            (
                diagnostic.diagnostic.code(),
                node_text(&parsed, node),
                range.start.get() as usize,
                range.end.get() as usize,
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        actual,
        expected.map(|(code, text)| {
            let start = source.find(text).unwrap();
            (code, text, start, start + text.len())
        })
    );
    let nodes = [
        "(value - 'condition') > 0",
        "(value - 'condition') > 0 ? accept('true-branch') : accept('false-branch')",
    ]
    .map(|text| expression(&parsed, file, text));
    for &node in &nodes {
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, node))
                .unwrap(),
            "boolean"
        );
    }
    assert_warm_replay(&mut context, file, &nodes);
}

#[test]
fn wrong_nullish_branch_reports_its_narrowed_return_type() {
    let source = concat!(
        "function wrong(value: number | undefined): number {\n",
        "  return value === undefined ? value : 1;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);
    context.check_source_file(file).unwrap();
    assert_completed(&context, file);

    let [diagnostic] = context.diagnostics().as_slice() else {
        panic!("expected one return assignment diagnostic");
    };
    assert_eq!(diagnostic.diagnostic.code(), 2322);
    assert_eq!(
        diagnostic.diagnostic.render().unwrap(),
        "Type 'undefined' is not assignable to type 'number'.",
    );
    assert!(diagnostic.range_override.is_none());
    let node = diagnostic.node.unwrap();
    assert_eq!(node_text(&parsed, node), "value");
    let start = source.find("? value").unwrap() + 2;
    let range = parsed.arena.get(node.node).unwrap().range;
    assert_eq!(range.start.get() as usize, start);
    assert_eq!(range.end.get() as usize, start + "value".len());
    let conditional = expression(&parsed, file, "value === undefined ? value : 1");
    assert_warm_replay(&mut context, file, &[conditional]);
}
