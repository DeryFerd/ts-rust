use ts_ast::{NodeData, NodeId, SyntaxKind};
use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};

fn diagnostic_locations(parsed: &ParseResult) -> Vec<(u32, u32, u32)> {
    parsed
        .diagnostics
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.code.expect("expected a catalog diagnostic"),
                diagnostic.range.start.get(),
                diagnostic.range.end.get(),
            )
        })
        .collect()
}

fn variable_initializers(parsed: &ParseResult) -> Vec<(&str, NodeId)> {
    parsed
        .arena
        .iter()
        .filter_map(|(_, node)| {
            let NodeData::VariableDeclaration(declaration) = &node.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(declaration.name)?.data else {
                return None;
            };
            Some((name.text.as_str(), declaration.initializer?))
        })
        .collect()
}

fn function_expressions(parsed: &ParseResult, index: usize) -> Vec<SyntaxKind> {
    let NodeData::SourceFile(root) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected source file");
    };
    let NodeData::FunctionDeclaration(function) =
        &parsed.arena.get(root.statements.nodes[index]).unwrap().data
    else {
        panic!("expected function");
    };
    let NodeData::Block(body) = &parsed.arena.get(function.body.unwrap()).unwrap().data else {
        panic!("expected function body");
    };
    body.statements
        .nodes
        .iter()
        .filter_map(|statement| {
            let NodeData::ExpressionStatement(statement) = &parsed.arena.get(*statement)?.data
            else {
                return None;
            };
            Some(parsed.arena.get(statement.expression)?.kind)
        })
        .collect()
}

#[test]
fn missing_arrow_recovery_keeps_await_and_yield_name_contexts() {
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
    for (mode, parsed) in [
        ("ts", parse_source_file(source)),
        ("tsx", parse_jsx_source_file(source)),
    ] {
        assert_eq!(
            diagnostic_locations(&parsed),
            [
                (1005, 64, 69),
                (1005, 116, 121),
                (1005, 203, 208),
                (1005, 307, 312)
            ],
            "{mode}",
        );
        let initializers = variable_initializers(&parsed);
        assert_eq!(initializers.len(), 5);
        for ((name, initializer), (expected_name, expected_body, end)) in
            initializers[..4].iter().zip([
                ("awaitBody", "await", Some(69)),
                ("yieldBody", "yield", Some(121)),
                ("blockedAwait", "", None),
                ("blockedYield", "", None),
            ])
        {
            assert_eq!(*name, expected_name);
            let initializer = parsed.arena.get(*initializer).unwrap();
            let NodeData::ArrowFunction(arrow) = &initializer.data else {
                panic!("expected arrow initializer");
            };
            let body = parsed.arena.get(arrow.body).unwrap();
            let NodeData::Identifier(identifier) = &body.data else {
                panic!("expected identifier recovery body");
            };
            eprintln!(
                "{mode} {name}: body={:?} range={:?} arrow_end={}",
                identifier.text,
                body.range,
                initializer.range.end.get(),
            );
            assert_eq!(identifier.text, expected_body);
            if let Some(end) = end {
                assert_eq!(initializer.range.end.get(), end);
                assert_eq!(body.range.end.get(), end);
            } else {
                // Missing-node offsets differ before this repair as well.
                assert_eq!(body.range.start, body.range.end);
            }
        }
        assert_eq!(initializers[4].0, "after");
        let after = parsed.arena.get(initializers[4].1).unwrap();
        assert_eq!(after.kind, SyntaxKind::NumericLiteral);
        assert_eq!(after.range.end.get(), 342);
        assert_eq!(
            function_expressions(&parsed, 1),
            [SyntaxKind::AwaitExpression]
        );
        assert_eq!(
            function_expressions(&parsed, 2),
            [SyntaxKind::YieldExpression]
        );
    }
}

#[test]
fn comment_line_breaks_end_bindings_but_not_missing_arrow_recovery() {
    let source = concat!(
        "const sameLine = 0 /* same line */ string = 1;\n",
        "const newLine = 0 /*\n",
        "*/ string = 2;\n",
        "const predicate = (value: unknown): number /*\n",
        "*/ body;\n",
        "const after = 1;\n",
    );
    for parse in [parse_source_file, parse_jsx_source_file] {
        let parsed = parse(source);
        assert_eq!(
            diagnostic_locations(&parsed),
            [(1005, 35, 41), (1005, 132, 136)]
        );
        let shapes: Vec<_> = variable_initializers(&parsed)
            .iter()
            .map(|(name, initializer)| {
                let node = parsed.arena.get(*initializer).unwrap();
                (*name, node.kind, node.range.end.get())
            })
            .collect();
        assert_eq!(
            shapes,
            [
                ("sameLine", SyntaxKind::NumericLiteral, 18),
                ("string", SyntaxKind::NumericLiteral, 45),
                ("newLine", SyntaxKind::NumericLiteral, 64),
                ("predicate", SyntaxKind::ArrowFunction, 136),
                ("after", SyntaxKind::NumericLiteral, 153),
            ],
        );
        let NodeData::SourceFile(root) = &parsed.arena.get(parsed.source_file).unwrap().data else {
            panic!("expected source file");
        };
        assert_eq!(root.statements.nodes.len(), 5);
        let NodeData::ExpressionStatement(statement) =
            &parsed.arena.get(root.statements.nodes[2]).unwrap().data
        else {
            panic!("expected assignment after comment line break");
        };
        assert_eq!(
            parsed.arena.get(statement.expression).unwrap().kind,
            SyntaxKind::BinaryExpression,
        );
    }
}

#[test]
fn explicit_commas_keep_of_and_valid_predicate_bodies() {
    let source = concat!(
        "async function* outer(value: unknown) {\n",
        "  const predicate = (entry: unknown): entry is string => true;\n",
        "  const asserted = (entry: unknown): asserts entry is string => true;\n",
        "  const sameLine = 0, string = 1, of = 2;\n",
        "  await action();\n",
        "  yield 1;\n",
        "}\n",
        "const after = 1;\n",
    );
    for parse in [parse_source_file, parse_jsx_source_file] {
        let parsed = parse(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let shapes: Vec<_> = variable_initializers(&parsed)
            .iter()
            .map(|(name, initializer)| {
                let node = parsed.arena.get(*initializer).unwrap();
                (*name, node.kind, node.range.end.get())
            })
            .collect();
        assert_eq!(
            shapes,
            [
                ("predicate", SyntaxKind::ArrowFunction, 101),
                ("asserted", SyntaxKind::ArrowFunction, 171),
                ("sameLine", SyntaxKind::NumericLiteral, 193),
                ("string", SyntaxKind::NumericLiteral, 205),
                ("of", SyntaxKind::NumericLiteral, 213),
                ("after", SyntaxKind::NumericLiteral, 261),
            ],
        );
        assert_eq!(
            function_expressions(&parsed, 0),
            [SyntaxKind::AwaitExpression, SyntaxKind::YieldExpression],
        );
    }
}
