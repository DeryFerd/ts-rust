use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
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
    "function id(value: number): number { return value; }\n",
    "const sum = (1 + 2) * id(3);\n",
    "const concat = \"x\" + 1;\n",
    "const badPlus = 1 + true;\n",
    "const invalidBoth = \"a\" - false;\n",
    "const mixedLeft = \"b\" - 1n;\n",
    "const mixedRight = 1n - \"c\";\n",
    "const relation = 1 < 2n;\n",
    "const relationBad = 1 < \"d\";\n",
    "const equality = 1 === 2;\n",
    "const nested = (\"e\" - false) + true;\n",
    "const exponent = 2 ** 3;\n",
    "const annotated: string = 1 + 2;\n",
    "function returned(): number { return 2 + 3; }\n",
    "const arrow = (value: number): number => value + 1;\n",
);

const RECOVERY_SOURCE: &str = concat!(
    "const anyPlus = (1 + true) + false;\n",
    "const errorPlus = (1n - 2) + true;\n",
    "const anyString = (3 + false) + \"s\";\n",
    "const errorString = (3n - 4) + \"t\";\n",
    "const anyArithmetic = (5 + false) - \"u\";\n",
    "const errorArithmetic = \"v\" - (5n - 6);\n",
    "const anyBigint = (7 + false) - 1n;\n",
    "const errorBigint = 1n - (7n - 8);\n",
    "const anyRelational = (9 + false) < \"w\";\n",
    "const errorRelational = true < (9n - 10);\n",
    "const anyEquality = (11 + false) === \"x\";\n",
    "const errorEquality = true === (11n - 12);\n",
);

fn context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/primitive-operators.ts\""),
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

fn variable_initializer(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    let initializer = parsed
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
        })
        .unwrap_or_else(|| panic!("missing initializer for {expected}"));
    NodeRef::new(parsed.arena.id(), file, initializer)
}

fn node_text<'source>(source: &'source str, parsed: &ParseResult, node: NodeRef) -> &'source str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing resolved type for {node:?}"))
}

fn is_type_checked(context: &CanonicalCheckerContext<'_>, file: FileId) -> bool {
    context
        .source_file(file)
        .and_then(|source| context.store().source_file_links(source))
        .is_some_and(|links| links.type_checked)
}

#[test]
fn source_binary_operators_preserve_types_diagnostics_and_warm_replay() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);

    for (node, record) in parsed.arena.iter() {
        let NodeData::BinaryExpression(binary) = &record.data else {
            continue;
        };
        assert_eq!(record.kind, SyntaxKind::BinaryExpression);
        assert_eq!(record.flags.0, 0, "binary node {node:?}");
        assert_eq!(binary.facts, 0, "binary node {node:?}");
        assert!(binary.symbol.is_none(), "binary node {node:?}");
        assert!(binary.type_.is_none(), "binary node {node:?}");
        assert!(binary.modifiers.is_none(), "binary node {node:?}");
        let operator = parsed.arena.get(binary.operator_token).unwrap();
        assert!(matches!(operator.data, NodeData::Token(_)));
        assert_eq!(operator.flags.0, 0);
        assert_eq!(operator.parent, Some(node));
    }

    let mut context = context(&parsed, file);
    context.check_source_file(file).unwrap();

    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    let number = bootstrap.number_type;
    let string = bootstrap.string_type;
    let boolean = bootstrap.boolean_type;
    let any = bootstrap.any_type;
    let error = bootstrap.error_type;
    for (name, expected) in [
        ("sum", number),
        ("concat", string),
        ("badPlus", any),
        ("invalidBoth", number),
        ("mixedLeft", error),
        ("mixedRight", error),
        ("relation", boolean),
        ("relationBad", boolean),
        ("equality", boolean),
        ("nested", any),
        ("exponent", number),
        ("annotated", number),
    ] {
        assert_eq!(
            resolved_type(&context, variable_initializer(&parsed, file, name)),
            expected,
            "initializer {name}",
        );
    }
    let arrow_binary = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let node = NodeRef::new(parsed.arena.id(), file, node);
            (record.kind == SyntaxKind::BinaryExpression
                && node_text(SOURCE, &parsed, node) == "value + 1")
                .then_some(node)
        })
        .expect("concise arrow must retain its binary body");
    assert_eq!(resolved_type(&context, arrow_binary), number);

    let diagnostics = context.diagnostics().as_slice();
    let actual = diagnostics
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.diagnostic.code(),
                node_text(SOURCE, &parsed, diagnostic.node.unwrap()),
                diagnostic
                    .diagnostic
                    .arguments
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        actual,
        [
            (2365, "1 + true", vec!["+", "number", "boolean"]),
            (2362, "\"a\"", vec![]),
            (2363, "false", vec![]),
            (2362, "\"b\"", vec![]),
            (2365, "\"b\" - 1n", vec!["-", "string", "bigint"]),
            (2363, "\"c\"", vec![]),
            (2365, "1n - \"c\"", vec!["-", "bigint", "string"]),
            (2365, "1 < \"d\"", vec!["<", "number", "string"]),
            (2367, "1 === 2", vec!["1", "2"]),
            (2362, "\"e\"", vec![]),
            (2363, "false", vec![]),
            (
                2365,
                "(\"e\" - false) + true",
                vec!["+", "number", "boolean"],
            ),
            (2322, "annotated", vec!["number", "string"]),
        ]
    );
    for diagnostic in diagnostics {
        let node = diagnostic.node.unwrap();
        let record = parsed.arena.get(node.node).unwrap();
        let expected_start = SOURCE
            .get(..usize::try_from(record.range.end.get()).unwrap())
            .unwrap()
            .rfind(node_text(SOURCE, &parsed, node))
            .unwrap();
        assert_eq!(
            usize::try_from(record.range.start.get()).unwrap(),
            expected_start
        );
        assert_eq!(
            usize::try_from(record.range.end.get()).unwrap(),
            expected_start + node_text(SOURCE, &parsed, node).len(),
        );
        assert!(diagnostic.related_information.is_empty());
    }

    let warm = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
        context.diagnostics().as_slice().to_vec(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.diagnostics().as_slice().to_vec(),
        ),
        warm,
    );
}

#[test]
fn nested_kernel_recoveries_remain_exact_and_clear_after_downstream_resolution() {
    let parsed = parse_source_file(RECOVERY_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    for (name, expected) in [
        ("anyPlus", bootstrap.any_type),
        ("errorPlus", bootstrap.error_type),
        ("anyString", bootstrap.string_type),
        ("errorString", bootstrap.string_type),
        ("anyArithmetic", bootstrap.number_type),
        ("errorArithmetic", bootstrap.number_type),
        ("anyBigint", bootstrap.bigint_type),
        ("errorBigint", bootstrap.bigint_type),
        ("anyRelational", bootstrap.boolean_type),
        ("errorRelational", bootstrap.boolean_type),
        ("anyEquality", bootstrap.boolean_type),
        ("errorEquality", bootstrap.boolean_type),
    ] {
        assert_eq!(
            resolved_type(&context, variable_initializer(&parsed, file, name)),
            expected,
            "initializer {name}",
        );
    }

    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| (
                diagnostic.diagnostic.code(),
                node_text(RECOVERY_SOURCE, &parsed, diagnostic.node.unwrap()),
            ))
            .collect::<Vec<_>>(),
        [
            (2365, "1 + true"),
            (2365, "1n - 2"),
            (2365, "3 + false"),
            (2365, "3n - 4"),
            (2365, "5 + false"),
            (2363, "\"u\""),
            (2365, "5n - 6"),
            (2362, "\"v\""),
            (2365, "7 + false"),
            (2365, "7n - 8"),
            (2365, "9 + false"),
            (2365, "9n - 10"),
            (2365, "11 + false"),
            (2365, "11n - 12"),
        ],
    );
    assert!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .all(|diagnostic| diagnostic.related_information.is_empty())
    );

    let warm = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
        context.diagnostics().as_slice().to_vec(),
    );
    context.check_source_file(file).unwrap();
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context.diagnostics().as_slice().to_vec(),
        ),
        warm,
    );
}

#[test]
fn unknown_bigint_exponentiation_target_publishes_no_root_or_source_diagnostics() {
    let parsed = parse_source_file("const value = 1n ** 2n;");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2);
    let root = variable_initializer(&parsed, file, "value");
    let mut context = context(&parsed, file);

    assert_eq!(
        context.check_source_file(file),
        Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::BigIntExponentiationTarget(root),
        )),
    );

    assert!(context.store().type_node_links(root).is_none());
    assert!(context.diagnostics().is_empty());
    assert!(!is_type_checked(&context, file));
    let rejected = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );
    assert!(context.check_source_file(file).is_err());
    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        rejected,
    );
}

#[test]
fn unsupported_nested_binary_position_is_rejected_before_publication() {
    let parsed = parse_source_file("const value = [1 + 2];");
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3);
    let binary = parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            (record.kind == SyntaxKind::BinaryExpression)
                .then(|| NodeRef::new(parsed.arena.id(), file, node))
        })
        .unwrap();
    let mut context = context(&parsed, file);
    let before = (
        context.store().type_len(),
        context.store().mapper_len(),
        context.store().signature_len(),
    );

    assert_eq!(
        context.check_source_file(file),
        Err(SourceCheckError::Unsupported(
            UnsupportedSourceSyntax::Syntax {
                node: binary,
                kind: SyntaxKind::BinaryExpression,
                role: SourceSyntaxRole::BinaryExpression,
            },
        )),
    );

    assert_eq!(
        (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        ),
        before,
    );
    assert!(context.store().type_node_links(binary).is_none());
    assert!(context.diagnostics().is_empty());
    assert!(!is_type_checked(&context, file));
}
