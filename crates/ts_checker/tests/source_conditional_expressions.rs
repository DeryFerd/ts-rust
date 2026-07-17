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
    "let text: string = \"x\";\n",
    "let count: number = 1;\n",
    "const mixed = flag ? text : count;\n",
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

    for (expression, expected) in [
        ("flag ? text : count", "string | number"),
        ("flag ? text : text", "string"),
        ("flag ? \"x\" : text", "string"),
    ] {
        let node = conditional(&parsed, file, expression);
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, node))
                .unwrap(),
            expected,
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

    let type_count = context.store().type_len();
    let symbol_count = context.store().symbol_len();
    let table_count = context.store().symbol_store().symbol_table_len();
    let diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(context.store().type_len(), type_count);
    assert_eq!(context.store().symbol_len(), symbol_count);
    assert_eq!(
        context.store().symbol_store().symbol_table_len(),
        table_count
    );
    assert_eq!(context.diagnostics(), &diagnostics);
}

#[test]
fn contextual_and_condition_narrowed_forms_fail_before_source_publication() {
    for (index, source) in [
        concat!(
            "let flag: boolean = true;\n",
            "const contextual: string | number = flag ? \"x\" : 1;\n",
        ),
        concat!(
            "let flag: boolean = true;\n",
            "const narrowed = flag ? flag : false;\n",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(10 + u32::try_from(index).unwrap());
        let mut context = context(&parsed, file);
        let type_count = context.store().type_len();
        let result = context.check_source_file(file);
        assert!(matches!(
            result,
            Err(SourceCheckError::Unsupported(
                UnsupportedSourceSyntax::Syntax {
                    role: SourceSyntaxRole::VariableInitializer,
                    ..
                }
            ))
        ));
        assert_eq!(context.store().type_len(), type_count);
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
