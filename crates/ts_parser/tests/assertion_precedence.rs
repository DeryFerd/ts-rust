use ts_ast::{NodeData, NodeId, SyntaxKind};
use ts_parser::{ParseResult, parse_source_file};

const FIXTURE: &str = include_str!("fixtures/disallowUnerasableAssertion.ts");
const CONTROLS: &str = include_str!("fixtures/assertion-precedence-controls.ts");

fn initializer(parsed: &ParseResult, name: &str) -> NodeId {
    parsed
        .arena
        .iter()
        .find_map(|(_, node)| {
            let NodeData::VariableDeclaration(declaration) = &node.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(declaration.name)?.data else {
                return None;
            };
            (identifier.text == name)
                .then_some(declaration.initializer)
                .flatten()
        })
        .unwrap_or_else(|| panic!("missing initializer for {name}"))
}

fn source_text(parsed: &ParseResult, node: NodeId) -> &str {
    let range = parsed.arena.get(node).unwrap().range;
    &parsed.arena.source_text().unwrap()[range.start.get() as usize..range.end.get() as usize]
}

fn expression_shape(parsed: &ParseResult, node: NodeId) -> String {
    let record = parsed.arena.get(node).unwrap();
    let child = |child| {
        let child_record = parsed.arena.get(child).unwrap();
        assert_eq!(child_record.parent, Some(node));
        assert!(record.range.start <= child_record.range.start);
        assert!(child_record.range.end <= record.range.end);
        expression_shape(parsed, child)
    };
    match &record.data {
        NodeData::NumericLiteral(_) => source_text(parsed, node).to_owned(),
        NodeData::BinaryExpression(binary) => format!(
            "({} {} {})",
            source_text(parsed, binary.operator_token),
            child(binary.left),
            child(binary.right),
        ),
        NodeData::ParenthesizedExpression(parenthesized) => {
            format!("(paren {})", child(parenthesized.expression))
        }
        NodeData::AsExpression(assertion) => format!(
            "(as {} {})",
            child(assertion.expression),
            source_text(parsed, assertion.type_),
        ),
        NodeData::SatisfiesExpression(assertion) => format!(
            "(satisfies {} {})",
            child(assertion.expression),
            source_text(parsed, assertion.type_),
        ),
        _ => panic!(
            "unexpected expression {:?}: {}",
            record.kind,
            source_text(parsed, node)
        ),
    }
}

#[test]
fn original_fixture_reports_exact_comma_diagnostics() {
    let parsed = parse_source_file(FIXTURE);
    let expected = [
        (9, 36),
        (10, 43),
        (33, 37),
        (34, 44),
        (39, 43),
        (40, 57),
        (63, 44),
        (64, 58),
    ]
    .map(|(line, column)| {
        let start = FIXTURE
            .split_inclusive('\n')
            .take(line - 1)
            .map(str::len)
            .sum::<usize>()
            + column
            - 1;
        let start = u32::try_from(start).unwrap();
        (Some(1005), start, start + 1, "',' expected.")
    });
    assert_eq!(
        parsed
            .diagnostics
            .iter()
            .map(|diagnostic| (
                diagnostic.code,
                diagnostic.range.start.get(),
                diagnostic.range.end.get(),
                diagnostic.message.as_str(),
            ))
            .collect::<Vec<_>>(),
        expected,
    );
    assert_eq!(parsed.arena.source_text(), Some(FIXTURE));
    assert_eq!(
        parsed
            .arena
            .get(parsed.source_file)
            .unwrap()
            .range
            .end
            .get() as usize,
        FIXTURE.len()
    );
}

#[test]
fn original_fixture_keeps_assertion_ranges_before_unerasable_operators() {
    let parsed = parse_source_file(FIXTURE);
    for (name, expected, kind) in [
        ("x03", "1 + 1 as number", SyntaxKind::AsExpression),
        ("x04", "1 + 1 as any as number", SyntaxKind::AsExpression),
        ("x23", "1 >> 1 as number", SyntaxKind::AsExpression),
        ("x24", "1 >> 1 as any as number", SyntaxKind::AsExpression),
        (
            "y03",
            "1 + 1 satisfies number",
            SyntaxKind::SatisfiesExpression,
        ),
        (
            "y04",
            "1 + 1 satisfies any satisfies number",
            SyntaxKind::SatisfiesExpression,
        ),
        (
            "y23",
            "1 >> 1 satisfies number",
            SyntaxKind::SatisfiesExpression,
        ),
        (
            "y24",
            "1 >> 1 satisfies any satisfies number",
            SyntaxKind::SatisfiesExpression,
        ),
    ] {
        let node = initializer(&parsed, name);
        let record = parsed.arena.get(node).unwrap();
        let prefix = format!("export const {name} = ");
        let start = FIXTURE.find(&prefix).unwrap() + prefix.len();
        assert_eq!(source_text(&parsed, node), expected, "{name}");
        assert_eq!(record.kind, kind, "{name}");
        assert_eq!(record.range.start.get() as usize, start, "{name}");
        assert_eq!(
            record.range.end.get() as usize,
            start + expected.len(),
            "{name}"
        );
    }
}

#[test]
fn original_fixture_preserves_all_48_assertion_trees() {
    let parsed = parse_source_file(FIXTURE);
    let expected = [
        "(* (ASSERT 1 number) 2)",
        "(* (ASSERT (ASSERT 1 any) number) 2)",
        "(ASSERT (+ 1 1) number)",
        "(ASSERT (ASSERT (+ 1 1) any) number)",
        "(+ (ASSERT 1 number) (* 1 2))",
        "(+ (ASSERT (ASSERT 1 any) number) (* 1 2))",
        "(+ (ASSERT (* 1 1) number) 2)",
        "(+ (ASSERT (ASSERT (* 1 1) any) number) 2)",
        "(+ (* (ASSERT 1 number) 1) 2)",
        "(+ (* (ASSERT (ASSERT 1 any) number) 1) 2)",
        "(* (paren (ASSERT (+ 1 1) number)) 2)",
        "(* (paren (ASSERT (ASSERT (+ 1 1) any) number)) 2)",
        "(* (paren (+ (ASSERT 1 number) 1)) 2)",
        "(* (paren (+ (ASSERT (ASSERT 1 any) number) 1)) 2)",
        "(=== (ASSERT (+ 1 1) number) 2)",
        "(=== (ASSERT (ASSERT (+ 1 1) any) number) 2)",
        "(> (ASSERT (+ 1 1) number) 2)",
        "(> (ASSERT (ASSERT (+ 1 1) any) number) 2)",
        "(>= (ASSERT (+ 1 1) number) 2)",
        "(>= (ASSERT (ASSERT (+ 1 1) any) number) 2)",
        "(>> (ASSERT (+ 1 1) number) 2)",
        "(>> (ASSERT (ASSERT (+ 1 1) any) number) 2)",
        "(ASSERT (>> 1 1) number)",
        "(ASSERT (ASSERT (>> 1 1) any) number)",
    ];
    for (prefix, assertion) in [("x", "as"), ("y", "satisfies")] {
        for (index, expected) in expected.iter().enumerate() {
            let name = format!("{prefix}{:02}", index + 1);
            assert_eq!(
                expression_shape(&parsed, initializer(&parsed, &name)),
                expected.replace("ASSERT", assertion),
                "{name}",
            );
        }
    }
}

#[test]
fn mixed_assertions_track_the_last_binary_operand_and_rescan_operators() {
    let parsed = parse_source_file(CONTROLS);
    let expected = [(1, 56, 1), (2, 56, 1), (5, 39, 2), (6, 38, 2), (9, 52, 1)].map(
        |(line, column, length)| {
            let start = CONTROLS
                .split_inclusive('\n')
                .take(line - 1)
                .map(str::len)
                .sum::<usize>()
                + column
                - 1;
            let start = u32::try_from(start).unwrap();
            (Some(1005), start, start + length, "',' expected.")
        },
    );
    assert_eq!(
        parsed
            .diagnostics
            .iter()
            .map(|diagnostic| (
                diagnostic.code,
                diagnostic.range.start.get(),
                diagnostic.range.end.get(),
                diagnostic.message.as_str(),
            ))
            .collect::<Vec<_>>(),
        expected,
    );
    for (name, expected) in [
        ("mixed1", "(satisfies (as (+ 1 1) number) number)"),
        ("mixed2", "(as (satisfies (+ 1 1) number) number)"),
        ("shift", "(as (< 1 1) boolean)"),
        ("power", "(as (+ 1 1) number)"),
        ("later", "(as (+ (as (* 1 1) number) 2) number)"),
        (
            "grouped",
            "(* (paren (satisfies (as (+ 1 1) number) number)) 2)",
        ),
        ("unary", "(* (satisfies (as 1 number) number) 2)"),
        ("equal", "(* (as (* 1 1) number) 2)"),
        ("lower", "(+ (as (* 1 1) number) 2)"),
        ("equalPower", "(** (as (** 2 3) number) 2)"),
    ] {
        assert_eq!(
            expression_shape(&parsed, initializer(&parsed, name)),
            expected,
            "{name}"
        );
    }
}

#[test]
fn assertion_keywords_after_line_breaks_remain_separate_calls() {
    let parsed = parse_source_file(CONTROLS);
    for (variable, callee, text) in [
        ("line1", "as", "as(2)"),
        ("line2", "satisfies", "satisfies(3)"),
    ] {
        let value = initializer(&parsed, variable);
        assert_eq!(
            parsed.arena.get(value).unwrap().kind,
            SyntaxKind::NumericLiteral
        );
        let call = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::CallExpression(call) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(identifier) = &parsed.arena.get(call.expression)?.data
                else {
                    return None;
                };
                (identifier.text == callee).then_some(node)
            })
            .unwrap();
        assert_eq!(source_text(&parsed, call), text);
        let statement = parsed.arena.get(call).unwrap().parent.unwrap();
        assert_eq!(
            parsed.arena.get(statement).unwrap().kind,
            SyntaxKind::ExpressionStatement
        );
    }
}
