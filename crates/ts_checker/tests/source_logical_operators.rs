use ts_ast::{FileId, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const SOURCE: &str = concat!(
    "interface LogicalObject { kind: \"a\"; }\n",
    "function andValue(value: string | null): unknown { return value && 1; }\n",
    "function orValue(value: string | null): unknown { return value || 1; }\n",
    "function nullishValue(value: string | null): unknown { return value ?? 1; }\n",
    "function unknownOr(unknownValue: unknown): unknown { return unknownValue || 1; }\n",
    "function unknownNullish(unknownValue: unknown): unknown { return unknownValue ?? 1; }\n",
    "function narrowedAnd(narrowedValue: number | null): unknown { return narrowedValue && narrowedValue + 1; }\n",
    "function narrowedChain(chainValue: number | null, gate: boolean): unknown { return chainValue && gate && chainValue + 1; }\n",
    "function voidUnion(value: void | boolean): unknown { return value && 13; }\n",
    "function contextualAnd(): LogicalObject { return true && { kind: \"a\" }; }\n",
    "function accept(value: unknown): void {}\n",
    "function nothing(): void {}\n",
    "const alwaysTruthy = {} || 1;\n",
    "const alwaysFalsy = \"\" && 2;\n",
    "const neverNullish = 2 ?? 3;\n",
    "const alwaysNullish = null ?? 4;\n",
    "const zero = 0 && 5;\n",
    "const nested = (null ?? \"x\") || 6;\n",
    "const alternateZero = 0x0 && 7;\n",
    "const alternateOne = 1.0 && 8;\n",
    "const voidTruthiness = nothing() && 9;\n",
    "const assertedVoid = (undefined as void) && 10;\n",
    "const assertedNeverNullish = (2 as number) ?? 11;\n",
    "const logicalCall = accept(true && 12);\n",
);

const NON_STRICT_SOURCE: &str = concat!(
    "function looseAnd(value: number): unknown { return value && 2; }\n",
    "function looseOr(value: string): unknown { return value || 1; }\n",
    "function looseNullish(value: string): unknown { return value ?? 1; }\n",
);

const MIXED_SOURCE: &str = "const mixed = 1 ?? 2 || 3;\n";

const MIXED_CHAIN_SOURCE: &str = concat!(
    "function chained(a: string | null, b: string | null, c: string | null, d: string | null): unknown { return a || b ?? c || d; }\n",
    "function leftAnd(a: string | null, b: string | null, c: string | null): unknown { return a && b ?? c; }\n",
    "function rightAnd(a: string | null, b: string | null, c: string | null): unknown { return a ?? b && c; }\n",
);

fn context(
    parsed: &ParseResult,
    file: FileId,
    strict_null_checks: bool,
) -> CanonicalCheckerContext<'_> {
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/logical-operators.ts\""),
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
                strict_null_checks,
                exact_optional_property_types: false,
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

fn logical_expression(source: &str, parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let node = NodeRef::new(parsed.arena.id(), file, node);
            (record.kind == SyntaxKind::BinaryExpression
                && node_text(source, parsed, node) == expected)
                .then_some(node)
        })
        .unwrap_or_else(|| panic!("missing logical expression {expected:?}"))
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
fn source_logical_operators_preserve_types_diagnostics_and_warm_replay() {
    let parsed = parse_source_file(SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(0);

    let mut context = context(&parsed, file, true);
    context.check_source_file(file).unwrap();

    for (expression, expected) in [
        ("value && 1", "\"\" | 1 | null"),
        ("value || 1", "string | 1"),
        ("value ?? 1", "string | 1"),
        ("unknownValue || 1", "{}"),
        ("unknownValue ?? 1", "{}"),
        ("narrowedValue + 1", "number"),
        ("narrowedValue && narrowedValue + 1", "number | null"),
        ("chainValue + 1", "number"),
        ("true && { kind: \"a\" }", "{ kind: \"a\"; }"),
        ("{} || 1", "{}"),
        ("\"\" && 2", "\"\""),
        ("2 ?? 3", "2"),
        ("null ?? 4", "4"),
        ("0 && 5", "0"),
        ("null ?? \"x\"", "\"x\""),
        ("(null ?? \"x\") || 6", "\"x\""),
        ("0x0 && 7", "0"),
        ("1.0 && 8", "8"),
        ("nothing() && 9", "void"),
        ("(undefined as void) && 10", "void"),
        ("(2 as number) ?? 11", "number"),
        ("true && 12", "12"),
    ] {
        let node = logical_expression(SOURCE, &parsed, file, expression);
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, node))
                .unwrap(),
            expected,
            "expression {expression}",
        );
    }

    let diagnostics = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.diagnostic.code(),
                node_text(SOURCE, &parsed, diagnostic.node.unwrap()),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        diagnostics,
        [
            (2872, "{}"),
            (2873, "\"\""),
            (2869, "2"),
            (2871, "null"),
            (2871, "null"),
            (2872, "0x0"),
            (2872, "1.0"),
            (1345, "nothing()"),
            (1345, "(undefined as void)"),
            (2869, "2"),
        ],
    );
    assert!(is_type_checked(&context, file));

    let type_count = context.store().type_len();
    let diagnostics = context.diagnostics().clone();
    context.check_source_file(file).unwrap();
    assert_eq!(context.store().type_len(), type_count);
    assert_eq!(context.diagnostics(), &diagnostics);
    assert!(is_type_checked(&context, file));
}

#[test]
fn source_logical_operators_preserve_non_strict_result_rules() {
    let parsed = parse_source_file(NON_STRICT_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(1);
    let mut context = context(&parsed, file, false);

    context.check_source_file(file).unwrap();

    for (expression, expected) in [
        ("value && 2", "0 | 2"),
        ("value || 1", "string | 1"),
        ("value ?? 1", "string | 1"),
    ] {
        let node = logical_expression(NON_STRICT_SOURCE, &parsed, file, expression);
        assert_eq!(
            context
                .type_to_string(resolved_type(&context, node))
                .unwrap(),
            expected,
            "expression {expression}",
        );
    }
    assert!(context.diagnostics().is_empty());
    assert!(is_type_checked(&context, file));

    let type_count = context.store().type_len();
    context.check_source_file(file).unwrap();
    assert_eq!(context.store().type_len(), type_count);
    assert!(context.diagnostics().is_empty());
}

#[test]
fn source_nullish_mixing_emits_the_pinned_grammar_diagnostic() {
    let parsed = parse_source_file(MIXED_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(2);
    let mut context = context(&parsed, file, true);

    context.check_source_file(file).unwrap();

    let diagnostics = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.diagnostic.code(),
                node_text(MIXED_SOURCE, &parsed, diagnostic.node.unwrap()),
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
        diagnostics,
        [(5076, "1 ?? 2", vec!["??", "||"]), (2869, "1", vec![]),],
    );
    assert_eq!(
        context
            .type_to_string(resolved_type(
                &context,
                logical_expression(MIXED_SOURCE, &parsed, file, "1 ?? 2 || 3"),
            ))
            .unwrap(),
        "1",
    );
    assert!(is_type_checked(&context, file));
}

#[test]
fn source_nullish_mixing_owns_one_diagnostic_per_coalesce_chain() {
    let parsed = parse_source_file(MIXED_CHAIN_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(3);
    let mut context = context(&parsed, file, true);

    context.check_source_file(file).unwrap();

    let diagnostics = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.diagnostic.code(),
                node_text(MIXED_CHAIN_SOURCE, &parsed, diagnostic.node.unwrap()),
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
        diagnostics,
        [
            (5076, "a || b ?? c", vec!["??", "||"]),
            (5076, "a && b", vec!["&&", "??"]),
            (5076, "b && c", vec!["??", "&&"]),
        ],
    );
    assert!(is_type_checked(&context, file));
}
