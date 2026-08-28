use ts_ast::{Node, NodeData, SyntaxKind};
use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};

fn initializer<'a>(parsed: &'a ParseResult, expected: &str) -> &'a Node {
    parsed
        .arena
        .iter()
        .find_map(|(_, node)| {
            let NodeData::VariableDeclaration(declaration) = &node.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(declaration.name)?.data else {
                return None;
            };
            if name.text == expected {
                parsed.arena.get(declaration.initializer?)
            } else {
                None
            }
        })
        .expect("expected variable initializer")
}

fn assert_missing_body_spans(
    parsed: &ParseResult,
    expected: &[(&str, u32)],
    diagnostics: &[(u32, u32, u32)],
    after_end: u32,
) {
    let actual = parsed
        .diagnostics
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.code.expect("expected a catalog diagnostic"),
                diagnostic.range.start.get(),
                diagnostic.range.end.get(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(actual, diagnostics);
    for &(name, end) in expected {
        let node = initializer(parsed, name);
        let NodeData::ArrowFunction(arrow) = &node.data else {
            panic!("expected recovered arrow");
        };
        let body = parsed.arena.get(arrow.body).unwrap();
        let NodeData::Identifier(identifier) = &body.data else {
            panic!("expected missing identifier body");
        };
        eprintln!(
            "{name}: body={:?} span={:?} arrow_end={} expected_end={end}",
            identifier.text,
            body.range,
            node.range.end.get(),
        );
        assert!(identifier.text.is_empty(), "{name}");
        assert_eq!(
            (body.range.start.get(), body.range.end.get()),
            (end, end),
            "{name}",
        );
        assert_eq!(node.range.end.get(), end, "{name}");
        let token = parsed.arena.get(arrow.equals_greater_than_token).unwrap();
        assert_eq!(token.kind, SyntaxKind::EqualsGreaterThanToken);
        assert_eq!(
            (token.range.start.get(), token.range.end.get()),
            (end, end),
            "{name} arrow token",
        );
    }
    let after = initializer(parsed, "after");
    assert_eq!(after.kind, SyntaxKind::NumericLiteral);
    assert_eq!(after.range.end.get(), after_end);
}

#[test]
fn rejected_await_and_yield_bodies_end_before_leading_trivia() {
    let source = concat!(
        "function plain() {\n",
        "  const awaitBody = (value: unknown): number await;\n",
        "  const yieldBody = (value: unknown): number yield;\n",
        "}\n",
        "async function asyncOuter() {\n",
        "  const blockedAwait = (value: unknown): number await;\n",
        "  await action();\n",
        "}\n",
        "function* generatorOuter() {\n",
        "  const blockedYield = (value: unknown): number yield;\n",
        "  yield 1;\n",
        "}\n",
        "const after = 1;\n",
    );
    for parse in [parse_source_file, parse_jsx_source_file] {
        assert_missing_body_spans(
            &parse(source),
            &[("blockedAwait", 202), ("blockedYield", 306)],
            &[
                (1005, 64, 69),
                (1005, 116, 121),
                (1005, 203, 208),
                (1005, 307, 312),
            ],
            342,
        );
    }
}

#[test]
fn missing_body_ends_before_a_multiline_comment() {
    let source = concat!(
        "async function outer() {\n",
        "  const blocked = (value: unknown): number /*\n",
        "  */ await action();\n",
        "}\n",
        "const after = 1;\n",
    );
    for parse in [parse_source_file, parse_jsx_source_file] {
        let parsed = parse(source);
        assert_missing_body_spans(&parsed, &[("blocked", 67)], &[(1005, 76, 81)], 109);
        let NodeData::SourceFile(root) = &parsed.arena.get(parsed.source_file).unwrap().data else {
            panic!("expected source file");
        };
        assert_eq!(root.statements.nodes.len(), 2);
        let NodeData::FunctionDeclaration(function) =
            &parsed.arena.get(root.statements.nodes[0]).unwrap().data
        else {
            panic!("expected enclosing function");
        };
        let NodeData::Block(body) = &parsed.arena.get(function.body.unwrap()).unwrap().data else {
            panic!("expected enclosing block");
        };
        assert_eq!(body.statements.nodes.len(), 2);
        let NodeData::ExpressionStatement(statement) =
            &parsed.arena.get(body.statements.nodes[1]).unwrap().data
        else {
            panic!("expected following value expression");
        };
        assert_eq!(
            parsed.arena.get(statement.expression).unwrap().kind,
            SyntaxKind::AwaitExpression,
        );
    }
}
