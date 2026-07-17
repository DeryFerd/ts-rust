use ts_ast::{FileId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, SourceCheckError, SourceSyntaxRole, TypeId,
    UnsupportedSourceSyntax,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "let flag: boolean = true;\n",
    "let disabled: boolean = false;\n",
    "let key: string = \"\";\n",
    "let choice: number = 0;\n",
    "let magnitude: bigint = 0n;\n",
    "let text: string = \"x\";\n",
    "let count: number = 1;\n",
    "const mixed = flag ? text : count;\n",
    "const falseCondition = disabled ? text : count;\n",
    "const textCondition = key ? text : count;\n",
    "const numberCondition = choice ? text : count;\n",
    "const bigintCondition = magnitude ? text : count;\n",
    "const numeric = key ? count : magnitude;\n",
    "const absorbedBigint = flag ? 1n : magnitude;\n",
    "const parenthesized = (key) ? (text) : (count);\n",
    "const same = flag ? text : text;\n",
    "const reduced = flag ? \"x\" : text;\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/conditional-expressions.ts\""),
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

fn node_text<'source>(source: &'source str, parsed: &ParseResult, node: NodeRef) -> &'source str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn conditional(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let node = NodeRef::new(parsed.arena.id(), file, node);
            (record.kind == SyntaxKind::ConditionalExpression
                && node_text(SOURCE, parsed, node) == expected)
                .then_some(node)
        })
        .unwrap_or_else(|| panic!("missing conditional expression {expected:?}"))
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing resolved type for {node:?}"))
}

#[test]
fn direct_conditional_initializers_join_in_branch_order_and_replay_warm() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let (string, bigint, string_or_number, number_or_bigint) = {
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        (
            bootstrap.string_type,
            bootstrap.bigint_type,
            bootstrap.string_or_number_type,
            bootstrap.number_or_bigint_type,
        )
    };
    for (expression, expected_display, expected_type) in [
        ("flag ? text : count", "string | number", string_or_number),
        (
            "disabled ? text : count",
            "string | number",
            string_or_number,
        ),
        ("key ? text : count", "string | number", string_or_number),
        ("choice ? text : count", "string | number", string_or_number),
        (
            "magnitude ? text : count",
            "string | number",
            string_or_number,
        ),
        (
            "key ? count : magnitude",
            "number | bigint",
            number_or_bigint,
        ),
        ("flag ? 1n : magnitude", "bigint", bigint),
        (
            "(key) ? (text) : (count)",
            "string | number",
            string_or_number,
        ),
        ("flag ? text : text", "string", string),
        ("flag ? \"x\" : text", "string", string),
    ] {
        let node = conditional(&parsed, file, expression);
        assert_eq!(resolved_type(&context, node), expected_type);
        assert_eq!(
            context.type_to_string(expected_type).unwrap(),
            expected_display,
            "expression {expression}",
        );
        let data = parsed.arena.get(node.node).unwrap();
        let ts_ast::NodeData::ConditionalExpression(conditional) = &data.data else {
            unreachable!()
        };
        for child in [
            conditional.condition,
            conditional.when_true,
            conditional.when_false,
        ] {
            assert!(
                context
                    .store()
                    .type_node_links(NodeRef::new(parsed.arena.id(), file, child))
                    .is_none(),
                "conditional operands stay uncached"
            );
        }
    }
    assert!(context.diagnostics().is_empty());

    let resolved = [
        "flag ? text : count",
        "disabled ? text : count",
        "key ? text : count",
        "choice ? text : count",
        "magnitude ? text : count",
        "key ? count : magnitude",
        "flag ? 1n : magnitude",
        "(key) ? (text) : (count)",
        "flag ? text : text",
        "flag ? \"x\" : text",
    ]
    .map(|expression| resolved_type(&context, conditional(&parsed, file, expression)));
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let state = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().symbol_len(),
        context.store().symbol_store().checker_created_symbol_len(),
        context.store().symbol_store().symbol_table_len(),
        context.store().type_resolution_len(),
        context.store().type_resolution_start(),
        context.store().relation_state_snapshot(),
        bootstrap.string_literal_cache_len(),
        bootstrap.number_literal_cache_len(),
        bootstrap.bigint_literal_cache_len(),
    );
    let diagnostics = context.diagnostics().clone();
    context.recheck_source_file(file).unwrap();
    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().symbol_len(),
            context.store().symbol_store().checker_created_symbol_len(),
            context.store().symbol_store().symbol_table_len(),
            context.store().type_resolution_len(),
            context.store().type_resolution_start(),
            context.store().relation_state_snapshot(),
            bootstrap.string_literal_cache_len(),
            bootstrap.number_literal_cache_len(),
            bootstrap.bigint_literal_cache_len(),
        ),
        state
    );
    assert_eq!(
        [
            "flag ? text : count",
            "disabled ? text : count",
            "key ? text : count",
            "choice ? text : count",
            "magnitude ? text : count",
            "key ? count : magnitude",
            "flag ? 1n : magnitude",
            "(key) ? (text) : (count)",
            "flag ? text : text",
            "flag ? \"x\" : text",
        ]
        .map(|expression| resolved_type(&context, conditional(&parsed, file, expression))),
        resolved
    );
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
fn unsupported_contextual_narrowed_inferred_and_assigned_forms_fail_before_publication() {
    for (index, source) in [
        concat!(
            "let flag: boolean = true;\n",
            "const contextual: string | number = flag ? \"x\" : 1;\n",
        ),
        concat!(
            "let flag: boolean = true;\n",
            "const narrowed = flag ? flag : false;\n",
        ),
        concat!(
            "let flag = true;\n",
            "let text: string = \"x\";\n",
            "let count: number = 1;\n",
            "const unannotated = flag ? text : count;\n",
        ),
        concat!(
            "let flag: boolean = true as never;\n",
            "let text: string = \"x\";\n",
            "let count: number = 1;\n",
            "const neverCondition = flag ? text : count;\n",
        ),
        concat!(
            "var flag: boolean = true;\n",
            "var text: string = \"x\";\n",
            "var count: number = 1;\n",
            "flag = false;\n",
            "const assignedCondition = flag ? text : count;\n",
        ),
        concat!(
            "var flag: boolean = true;\n",
            "var text: string = \"x\";\n",
            "var count: number = 1;\n",
            "text = \"y\";\n",
            "const assignedBranch = flag ? text : count;\n",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(10 + u32::try_from(index).unwrap());
        let mut context = context(&parsed, file);
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let before = (
            [
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().symbol_len(),
                context.store().symbol_store().checker_created_symbol_len(),
                context.store().symbol_store().symbol_table_len(),
                context.store().type_resolution_len(),
                context.store().type_resolution_start(),
            ],
            context.store().relation_state_snapshot(),
            [
                bootstrap.string_literal_cache_len(),
                bootstrap.number_literal_cache_len(),
                bootstrap.bigint_literal_cache_len(),
            ],
            context.diagnostics().clone(),
        );
        let result = context.check_source_file(file);
        assert!(
            matches!(
                result,
                Err(SourceCheckError::Unsupported(
                    UnsupportedSourceSyntax::Syntax {
                        role: SourceSyntaxRole::VariableInitializer,
                        ..
                    }
                ))
            ),
            "source {source:?} returned {result:?}"
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        assert_eq!(
            (
                [
                    context.store().type_len(),
                    context.store().mapper_len(),
                    context.store().symbol_len(),
                    context.store().symbol_store().checker_created_symbol_len(),
                    context.store().symbol_store().symbol_table_len(),
                    context.store().type_resolution_len(),
                    context.store().type_resolution_start(),
                ],
                context.store().relation_state_snapshot(),
                [
                    bootstrap.string_literal_cache_len(),
                    bootstrap.number_literal_cache_len(),
                    bootstrap.bigint_literal_cache_len(),
                ],
                context.diagnostics().clone(),
            ),
            before,
            "source {source:?}",
        );
        assert!(context.diagnostics().is_empty());
        let conditional = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::ConditionalExpression).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .unwrap();
        assert!(context.store().type_node_links(conditional).is_none());
    }
}
