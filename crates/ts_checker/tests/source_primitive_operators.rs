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

use ts_ast::{FlowFlags, FlowNodePayload};
use ts_checker::semantic::IntrinsicBootstrapOptions;
use ts_checker::semantic::artifact_queries::CanonicalArtifactQueryError;

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

const POSITION_SOURCE: &str = concat!(
    "function takeNumber(value: number): void {}\n",
    "function takeString(value: string): void {}\n",
    "function pair(left: number, right: number): void {}\n",
    "function identity<T>(value: T): T { return value; }\n",
    "\n",
    "var assignedNumber: number = 0;\n",
    "var assignedString: string = \"\";\n",
    "\n",
    "assignedNumber = (1 + true) - \"a\";\n",
    "assignedString = (1n - 2) + true;\n",
    "assignedNumber = (\"b\" - false) + true;\n",
    "\n",
    "const callNumber = takeNumber((3 + true) - \"c\");\n",
    "const callError = takeString((3n - 4) + true);\n",
    "const callAny = takeNumber((\"d\" - false) + true);\n",
    "const callMismatch = takeString(5 + 6);\n",
    "const callPair = pair((7 + true) - \"e\", (8n - 9) + true);\n",
    "\n",
    "const genericClean = identity(1 + 2);\n",
    "const genericAny = identity((10 + true) + false);\n",
    "const genericError = identity((11n - 12) + true);\n",
);

const BITWISE_COMPOUND_SOURCE: &str =
    include_str!("fixtures/bitwiseCompoundAssignmentOperators.ts");

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

fn expression_by_text(source: &str, parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(node, record)| {
            let node = NodeRef::new(parsed.arena.id(), file, node);
            (matches!(
                record.kind,
                SyntaxKind::BinaryExpression | SyntaxKind::CallExpression
            ) && node_text(source, parsed, node) == expected)
                .then_some(node)
        })
        .unwrap_or_else(|| panic!("missing expression {expected:?}"))
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
fn upstream_bitwise_compound_assignments_keep_exact_diagnostics_and_spans() {
    let parsed = parse_source_file(BITWISE_COMPOUND_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(10);
    let mut context = context(&parsed, file);
    context.check_source_file(file).unwrap();

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
                range.start.get(),
                range.end.get() - range.start.get(),
                diagnostic
                    .diagnostic
                    .arguments
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<Vec<_>>();
    // The unchanged fixture retains its 19-byte target directive before the baseline source.
    assert_eq!(
        actual,
        [
            (2447, 46, 2, vec!["^=", "!=="]),
            (2362, 77, 1, vec![]),
            (2363, 100, 1, vec![]),
            (2447, 139, 2, vec!["&=", "&&"]),
            (2362, 171, 1, vec![]),
            (2363, 195, 1, vec![]),
            (2447, 226, 2, vec!["|=", "||"]),
            (2362, 257, 1, vec![]),
        ],
    );

    let number = context.store().intrinsic_bootstrap().unwrap().number_type;
    for (node, record) in parsed.arena.iter() {
        let NodeData::BinaryExpression(binary) = &record.data else {
            continue;
        };
        if matches!(
            parsed.arena.get(binary.operator_token).unwrap().kind,
            SyntaxKind::CaretEqualsToken
                | SyntaxKind::AmpersandEqualsToken
                | SyntaxKind::BarEqualsToken
        ) {
            assert_eq!(
                resolved_type(&context, NodeRef::new(parsed.arena.id(), file, node)),
                number,
            );
        }
    }

    let diagnostics = context.diagnostics().as_slice().to_vec();
    context.recheck_source_file(file).unwrap();
    assert_eq!(context.diagnostics().as_slice(), diagnostics);
}

#[test]
fn compound_assignments_keep_numeric_bigint_results_and_valid_assignment_checks() {
    let source = concat!(
        "var n = 7; n ^= 2; n &= 3; n |= 4;\n",
        "var b = 7n; b ^= 2n; b &= 3n; b |= 4n;\n",
        "var exact: 1 = 1; exact ^= 2;\n",
        "var count: number = 0; count += 'x';\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(11);
    let mut context = context(&parsed, file);
    context.check_source_file(file).unwrap();

    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    for (expression, expected) in [
        ("n ^= 2", bootstrap.number_type),
        ("n &= 3", bootstrap.number_type),
        ("n |= 4", bootstrap.number_type),
        ("b ^= 2n", bootstrap.bigint_type),
        ("b &= 3n", bootstrap.bigint_type),
        ("b |= 4n", bootstrap.bigint_type),
        ("exact ^= 2", bootstrap.number_type),
        ("count += 'x'", bootstrap.string_type),
    ] {
        assert_eq!(
            resolved_type(
                &context,
                expression_by_text(source, &parsed, file, expression)
            ),
            expected,
            "{expression}",
        );
    }
    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| (
                diagnostic.diagnostic.code(),
                node_text(source, &parsed, diagnostic.node.unwrap()),
                diagnostic
                    .diagnostic
                    .arguments
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>(),
            ))
            .collect::<Vec<_>>(),
        [
            (2322, "exact", vec!["number", "1"]),
            (2322, "count", vec!["string", "number"]),
        ],
    );
}

fn strict_nullish_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/nullish-assignment.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            )
            .with_always_strict(true),
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
            no_implicit_any: true,
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

// Compare a cold artifact query with a source-first check under strict null checks.
fn nullish_context(
    parsed: &ParseResult,
    file: FileId,
    first_query: Option<NodeRef>,
) -> CanonicalCheckerContext<'_> {
    let mut context = strict_nullish_context(parsed, file);
    assert!(!is_type_checked(&context, file));
    let first = first_query.map(|node| (node, context.get_type_at_location(node).unwrap()));
    context.check_source_file(file).unwrap();
    assert!(is_type_checked(&context, file));
    if let Some((node, type_)) = first {
        assert_eq!(context.get_type_at_location(node), Ok(type_));
    }
    context
}

fn assert_nullish_diagnostics(
    context: &CanonicalCheckerContext<'_>,
    source: &str,
    parsed: &ParseResult,
    expected: &[(u32, &str, &[&str])],
) {
    let actual = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            assert!(diagnostic.range_override.is_none());
            assert!(diagnostic.related_information.is_empty());
            (
                diagnostic.diagnostic.code(),
                node_text(source, parsed, diagnostic.node.unwrap()),
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
        expected
            .iter()
            .map(|&(code, text, arguments)| (code, text, arguments.to_vec()))
            .collect::<Vec<_>>(),
    );
    for (diagnostic, &(_, text, _)) in context.diagnostics().as_slice().iter().zip(expected) {
        // Each expected error is on the final occurrence of its text in these inputs.
        let start = source.rfind(text).unwrap();
        let range = parsed
            .arena
            .get(diagnostic.node.unwrap().node)
            .unwrap()
            .range;
        assert_eq!(usize::try_from(range.start.get()).unwrap(), start);
        assert_eq!(
            usize::try_from(range.end.get()).unwrap(),
            start + text.len()
        );
    }
}

fn nullish_state(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
) -> impl PartialEq + std::fmt::Debug + use<> {
    let store = context.store();
    (
        [
            store.type_len(),
            store.type_alias_len(),
            store.mapper_len(),
            store.signature_len(),
            store.symbol_len(),
            store.symbol_store().symbol_table_len(),
            store.index_info_len(),
            store.type_resolution_len(),
        ],
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = NodeRef::new(parsed.arena.id(), file, id);
                (
                    node,
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect::<Vec<_>>(),
        store
            .source_file_links(context.source_file(file).unwrap())
            .cloned(),
        store.relation_state_snapshot(),
        context.file(file).unwrap().1.flow_graph().clone(),
        context.diagnostics().clone(),
    )
}

fn assert_nullish_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    file: FileId,
    nodes: &[NodeRef],
) {
    let types = nodes
        .iter()
        .map(|&node| (node, context.get_type_at_location(node).unwrap()))
        .collect::<Vec<_>>();
    let before = nullish_state(context, parsed, file);
    context.check_source_file(file).unwrap();
    assert_eq!(nullish_state(context, parsed, file), before);
    context.recheck_source_file(file).unwrap();
    for (node, type_) in types {
        assert_eq!(context.get_type_at_location(node), Ok(type_));
    }
    assert_eq!(nullish_state(context, parsed, file), before);
}

#[test]
fn nullish_later_member_read_stops_before_unproved_flow_publication() {
    // Go accepts this source. Until member writes narrow later reads, reject the source.
    let source = concat!(
        "const object: { value: number | undefined } = { value: undefined };\n",
        "object.value ??= 1;\n",
        "const good: number = object.value;\n",
    );
    let parsed = parse_source_file(source);
    let file = FileId::new(202_941);
    let assignment = expression_by_text(source, &parsed, file, "object.value ??= 1");
    let read = variable_initializer(&parsed, file, "good");
    assert_eq!(node_text(source, &parsed, read), "object.value");
    let expected = SourceCheckError::Unsupported(UnsupportedSourceSyntax::Property(read));

    for cold_query_first in [false, true] {
        let mut context = strict_nullish_context(&parsed, file);
        let before = nullish_state(&context, &parsed, file);
        if cold_query_first {
            assert_eq!(
                context.get_type_at_location(read),
                Err(CanonicalArtifactQueryError::SourceCheck(expected)),
            );
            assert_eq!(nullish_state(&context, &parsed, file), before);
        }
        assert_eq!(context.check_source_file(file), Err(expected));
        assert_eq!(nullish_state(&context, &parsed, file), before);
        assert!(context.store().type_node_links(assignment).is_none());
        assert!(context.store().type_node_links(read).is_none());
        assert!(context.diagnostics().is_empty());
        assert!(!is_type_checked(&context, file));
        assert_eq!(
            context.get_type_at_location(read),
            Err(CanonicalArtifactQueryError::SourceCheck(expected)),
        );
        assert_eq!(nullish_state(&context, &parsed, file), before);
        assert_eq!(context.recheck_source_file(file), Err(expected));
        assert_eq!(nullish_state(&context, &parsed, file), before);
    }
}

#[test]
fn nullish_statement_assignment_narrows_the_following_read() {
    let source = concat!(
        "let value: string | undefined;\n",
        "value ??= 'fallback';\n",
        "const good: string = value;\n",
    );
    let parsed = parse_source_file(source);
    let file = FileId::new(202_935);
    let assignment = expression_by_text(source, &parsed, file, "value ??= 'fallback'");
    let read = variable_initializer(&parsed, file, "good");
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(assignment.node).unwrap().data
    else {
        panic!("expected the actual nullish assignment");
    };
    let left = NodeRef::new(parsed.arena.id(), file, binary.left);

    for first in [None, Some(assignment), Some(read)] {
        let mut context = nullish_context(&parsed, file, first);
        assert!(context.diagnostics().is_empty());
        for node in [assignment, read] {
            let type_ = context.get_type_at_location(node).unwrap();
            assert_eq!(context.type_to_string(type_).unwrap(), "string");
        }
        let owner = context.get_symbol_at_location(left).unwrap().unwrap();
        assert_eq!(context.get_symbol_at_location(read), Ok(Some(owner)));
        let write_type = context.get_type_at_location(left).unwrap();
        assert_eq!(
            context.type_to_string(write_type).unwrap(),
            "string | undefined",
        );
        assert_nullish_replay(&mut context, &parsed, file, &[assignment, left, read]);
    }
}

#[test]
fn nullish_assignments_check_rhs_types_even_when_the_left_is_not_nullish() {
    let source = concat!(
        "let value: string | undefined;\n",
        "value ??= 1;\n",
        "let present: string = 'ready';\n",
        "present ??= 2;\n",
    );
    let parsed = parse_source_file(source);
    let file = FileId::new(202_936);
    let nullable = expression_by_text(source, &parsed, file, "value ??= 1");
    let present = expression_by_text(source, &parsed, file, "present ??= 2");

    for first in [None, Some(nullable), Some(present)] {
        let mut context = nullish_context(&parsed, file, first);
        assert_nullish_diagnostics(
            &context,
            source,
            &parsed,
            &[
                (2322, "value", &["number", "string"]),
                (2322, "present", &["number", "string"]),
            ],
        );
        let type_ = context.get_type_at_location(present).unwrap();
        assert_eq!(context.type_to_string(type_).unwrap(), "string");
        assert_nullish_replay(&mut context, &parsed, file, &[nullable, present]);
    }
}

#[test]
fn nullish_member_assignments_publish_results_and_native_assignment_errors() {
    let source = concat!(
        "const cache: { [key: string]: number | undefined } = {};\n",
        "const good: number = (cache['x'] ??= 1);\n",
        "const bad: string = (cache['y'] ??= 2);\n",
        "const object: { value: number | undefined } = { value: undefined };\n",
        "const property: number = (object.value ??= 3);\n",
        "function cached(cache: { [key: string]: number | undefined }): number {\n",
        "  return cache['z'] ??= 4;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    let file = FileId::new(202_937);
    let good = expression_by_text(source, &parsed, file, "cache['x'] ??= 1");
    let bad = expression_by_text(source, &parsed, file, "cache['y'] ??= 2");
    let property = expression_by_text(source, &parsed, file, "object.value ??= 3");
    let returned = expression_by_text(source, &parsed, file, "cache['z'] ??= 4");

    for first in [None, Some(good), Some(bad), Some(returned)] {
        let mut context = nullish_context(&parsed, file, first);
        assert_nullish_diagnostics(
            &context,
            source,
            &parsed,
            &[(2322, "bad", &["number", "string"])],
        );
        for node in [good, bad, property, returned] {
            let type_ = context.get_type_at_location(node).unwrap();
            assert_eq!(context.type_to_string(type_).unwrap(), "number");
        }
        assert_nullish_replay(
            &mut context,
            &parsed,
            file,
            &[good, bad, property, returned],
        );
    }
}

#[test]
fn nullish_assignments_preserve_readonly_property_and_index_errors() {
    let source = concat!(
        "const frozen: { readonly value: number | undefined } = { value: undefined };\n",
        "frozen.value ??= 1;\n",
        "const cache: { readonly [key: string]: number | undefined } = {};\n",
        "cache['x'] ??= 1;\n",
    );
    let parsed = parse_source_file(source);
    let file = FileId::new(202_938);
    let property = expression_by_text(source, &parsed, file, "frozen.value ??= 1");
    let index = expression_by_text(source, &parsed, file, "cache['x'] ??= 1");

    for first in [None, Some(property), Some(index)] {
        let mut context = nullish_context(&parsed, file, first);
        assert_nullish_diagnostics(
            &context,
            source,
            &parsed,
            &[
                (2540, "value", &["value"]),
                (
                    2542,
                    "cache['x']",
                    &["{ readonly [key: string]: number | undefined; }"],
                ),
            ],
        );
        let bootstrap = context.store().intrinsic_bootstrap().unwrap();
        let error = bootstrap.error_type;
        let number = bootstrap.number_type;
        assert_eq!(context.get_type_at_location(property), Ok(error));
        assert_eq!(context.get_type_at_location(index), Ok(number));
        assert_nullish_replay(&mut context, &parsed, file, &[property, index]);
    }
}

#[test]
fn nullish_computed_targets_keep_one_call_diagnostic_and_real_signatures() {
    let source = concat!(
        "function receiver(): { [key: string]: number | undefined } { return {}; }\n",
        "function index(value: number): string { return 'x'; }\n",
        "const result: number = (receiver()[index('bad')] ??= 1);\n",
    );
    let parsed = parse_source_file(source);
    let file = FileId::new(202_940);
    let assignment = expression_by_text(source, &parsed, file, "receiver()[index('bad')] ??= 1");
    let receiver = expression_by_text(source, &parsed, file, "receiver()");
    let index = expression_by_text(source, &parsed, file, "index('bad')");

    for first in [None, Some(assignment), Some(index)] {
        let mut context = nullish_context(&parsed, file, first);
        assert_nullish_diagnostics(
            &context,
            source,
            &parsed,
            &[(2345, "'bad'", &["string", "number"])],
        );
        let type_ = context.get_type_at_location(assignment).unwrap();
        assert_eq!(context.type_to_string(type_).unwrap(), "number");
        for (call, expected_name) in [(receiver, "receiver"), (index, "index")] {
            let signature = context
                .store()
                .signature_links(call)
                .and_then(|links| links.resolved_signature.signature())
                .unwrap();
            let declaration = context
                .store()
                .signature(signature)
                .unwrap()
                .declaration()
                .unwrap();
            let NodeData::FunctionDeclaration(function) =
                &parsed.arena.get(declaration.node).unwrap().data
            else {
                panic!("expected the called function's declaration");
            };
            let NodeData::Identifier(name) =
                &parsed.arena.get(function.name.unwrap()).unwrap().data
            else {
                panic!("expected the declared function name");
            };
            assert_eq!(name.text, expected_name);
        }
        assert_nullish_replay(&mut context, &parsed, file, &[assignment, receiver, index]);
    }
}

#[test]
fn nested_nullish_assignments_keep_rhs_writes_conditional() {
    let source = concat!(
        "function conditional(value: number | undefined, side: number | undefined): void {\n",
        "  value ??= (side ??= 1);\n",
        "  const good: number = value;\n",
        "  const stillOptional: number | undefined = side;\n",
        "  const bad: number = side;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    let file = FileId::new(202_939);
    let outer = expression_by_text(source, &parsed, file, "value ??= (side ??= 1)");
    let inner = expression_by_text(source, &parsed, file, "side ??= 1");
    let good = variable_initializer(&parsed, file, "good");
    let optional = variable_initializer(&parsed, file, "stillOptional");
    let bad = variable_initializer(&parsed, file, "bad");

    for first in [None, Some(inner), Some(bad)] {
        let mut context = nullish_context(&parsed, file, first);
        assert_nullish_diagnostics(
            &context,
            source,
            &parsed,
            &[(2322, "bad", &["number | undefined", "number"])],
        );
        for (node, expected) in [
            (outer, "number"),
            (inner, "number"),
            (good, "number"),
            (optional, "number | undefined"),
            (bad, "number | undefined"),
        ] {
            let type_ = context.get_type_at_location(node).unwrap();
            assert_eq!(context.type_to_string(type_).unwrap(), expected);
        }

        let graph = context.file(file).unwrap().1.flow_graph();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());
        let NodeData::BinaryExpression(outer_binary) = &parsed.arena.get(outer.node).unwrap().data
        else {
            panic!("expected the outer nullish assignment");
        };
        let NodeData::BinaryExpression(inner_binary) = &parsed.arena.get(inner.node).unwrap().data
        else {
            panic!("expected the inner nullish assignment");
        };
        let outer_left = NodeRef::new(parsed.arena.id(), file, outer_binary.left);
        let inner_left = NodeRef::new(parsed.arena.id(), file, inner_binary.left);
        let inner_entry = graph
            .nodes()
            .get(graph.flow_at(inner_left).unwrap())
            .unwrap();
        assert!(inner_entry.flags.contains(FlowFlags::FALSE_CONDITION));
        assert_eq!(inner_entry.payload, Some(FlowNodePayload::Ast(outer_left)));
        for expression in [outer, inner] {
            let NodeData::BinaryExpression(binary) =
                &parsed.arena.get(expression.node).unwrap().data
            else {
                panic!("expected the actual nullish assignment");
            };
            let left = NodeRef::new(parsed.arena.id(), file, binary.left);
            let writes = graph
                .nodes()
                .iter()
                .filter(|flow| {
                    flow.flags.contains(FlowFlags::ASSIGNMENT)
                        && flow.payload == Some(FlowNodePayload::Ast(left))
                })
                .count();
            assert_eq!(writes, 1, "one bound write for each assignment target");
            assert!(graph.nodes().iter().any(|flow| {
                flow.flags.contains(FlowFlags::TRUE_CONDITION)
                    && flow.payload == Some(FlowNodePayload::Ast(left))
            }));
            assert!(graph.nodes().iter().any(|flow| {
                flow.flags.contains(FlowFlags::FALSE_CONDITION)
                    && flow.payload == Some(FlowNodePayload::Ast(left))
            }));
        }
        assert_nullish_replay(
            &mut context,
            &parsed,
            file,
            &[outer, inner, good, optional, bad],
        );
    }
}

#[test]
fn boolean_bitwise_operators_use_token_suggestions_but_shifts_keep_operand_errors() {
    let source = concat!(
        "const xor = true ^ false;\n",
        "const and = false & true;\n",
        "const or = false | true;\n",
        "const shift = true << false;\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(12);
    let mut context = context(&parsed, file);
    context.check_source_file(file).unwrap();

    assert_eq!(
        context
            .diagnostics()
            .as_slice()
            .iter()
            .map(|diagnostic| (
                diagnostic.diagnostic.code(),
                node_text(source, &parsed, diagnostic.node.unwrap()),
                diagnostic
                    .diagnostic
                    .arguments
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<_>>(),
            ))
            .collect::<Vec<_>>(),
        [
            (2447, "^", vec!["^", "!=="]),
            (2447, "&", vec!["&", "&&"]),
            (2447, "|", vec!["|", "||"]),
            (2362, "true", vec![]),
            (2363, "false", vec![]),
        ],
    );
}

#[test]
#[allow(clippy::too_many_lines)] // One operator matrix proves diagnostics and warm cache identity.
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
#[allow(clippy::too_many_lines)] // One source proves assignment and call recovery together.
fn assignment_and_call_roots_preserve_recovery_call_relations_and_warm_replay() {
    let parsed = parse_source_file(POSITION_SOURCE);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let file = FileId::new(4);
    let mut context = context(&parsed, file);

    context.check_source_file(file).unwrap();

    let bootstrap = context.store().intrinsic_bootstrap().unwrap();
    for (text, expected) in [
        ("(1 + true) - \"a\"", bootstrap.number_type),
        ("(1n - 2) + true", bootstrap.error_type),
        ("(\"b\" - false) + true", bootstrap.any_type),
        ("(3 + true) - \"c\"", bootstrap.number_type),
        ("(3n - 4) + true", bootstrap.error_type),
        ("(\"d\" - false) + true", bootstrap.any_type),
        ("5 + 6", bootstrap.number_type),
        ("(7 + true) - \"e\"", bootstrap.number_type),
        ("(8n - 9) + true", bootstrap.error_type),
    ] {
        assert_eq!(
            resolved_type(
                &context,
                expression_by_text(POSITION_SOURCE, &parsed, file, text),
            ),
            expected,
            "expression {text}",
        );
    }
    for (name, expected) in [
        ("genericClean", bootstrap.number_type),
        ("genericAny", bootstrap.any_type),
        ("genericError", bootstrap.error_type),
    ] {
        assert_eq!(
            resolved_type(&context, variable_initializer(&parsed, file, name)),
            expected,
            "generic call {name}",
        );
    }
    for call in [
        "takeNumber((3 + true) - \"c\")",
        "takeString((3n - 4) + true)",
        "takeNumber((\"d\" - false) + true)",
        "takeString(5 + 6)",
        "pair((7 + true) - \"e\", (8n - 9) + true)",
    ] {
        assert_eq!(
            resolved_type(
                &context,
                expression_by_text(POSITION_SOURCE, &parsed, file, call),
            ),
            bootstrap.void_type,
            "fixed call {call}",
        );
    }

    let actual = context
        .diagnostics()
        .as_slice()
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.diagnostic.code(),
                node_text(POSITION_SOURCE, &parsed, diagnostic.node.unwrap()),
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
            (2363, "\"a\"", vec![]),
            (2365, "1n - 2", vec!["-", "bigint", "number"]),
            (2362, "\"b\"", vec![]),
            (2363, "false", vec![]),
            (
                2365,
                "(\"b\" - false) + true",
                vec!["+", "number", "boolean"],
            ),
            (2365, "3 + true", vec!["+", "number", "boolean"]),
            (2363, "\"c\"", vec![]),
            (2365, "3n - 4", vec!["-", "bigint", "number"]),
            (2362, "\"d\"", vec![]),
            (2363, "false", vec![]),
            (
                2365,
                "(\"d\" - false) + true",
                vec!["+", "number", "boolean"],
            ),
            (2345, "5 + 6", vec!["number", "string"]),
            (2365, "7 + true", vec!["+", "number", "boolean"]),
            (2363, "\"e\"", vec![]),
            (2365, "8n - 9", vec!["-", "bigint", "number"]),
            (2365, "10 + true", vec!["+", "number", "boolean"]),
            (2365, "11n - 12", vec!["-", "bigint", "number"]),
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
fn trusted_assignment_and_call_roots_fail_atomically_on_operator_spelling_poison() {
    for (file, text) in [
        (FileId::new(6), "var target: number = 0; target = 1 + 2;"),
        (
            FileId::new(7),
            concat!(
                "function take(value: number): number { return value; } ",
                "const result = take(1 + 2);",
            ),
        ),
    ] {
        let mut parsed = parse_source_file(text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let (binary_id, operator_id) = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::BinaryExpression(binary) = &record.data else {
                    return None;
                };
                (parsed.arena.get(binary.operator_token)?.kind == SyntaxKind::PlusToken)
                    .then_some((node, binary.operator_token))
            })
            .expect("fixture must contain a primitive plus expression");
        parsed.arena.get_mut(operator_id).unwrap().kind = SyntaxKind::MinusToken;
        let binary = NodeRef::new(parsed.arena.id(), file, binary_id);
        let operator = NodeRef::new(parsed.arena.id(), file, operator_id);
        let mut context = context(&parsed, file);
        let before = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
        );
        let expected = SourceCheckError::PrimitiveOperator(operator);

        assert_eq!(context.check_source_file(file), Err(expected));
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

        assert_eq!(context.check_source_file(file), Err(expected));
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
            ),
            before,
        );
        assert!(context.diagnostics().is_empty());
    }
}

#[test]
fn unsupported_nested_binary_position_is_rejected_before_publication() {
    for (file, text) in [
        (FileId::new(3), "const value = [1 + 2];"),
        (FileId::new(5), "const value = { item: 1 + 2 };"),
    ] {
        let parsed = parse_source_file(text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
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
}
