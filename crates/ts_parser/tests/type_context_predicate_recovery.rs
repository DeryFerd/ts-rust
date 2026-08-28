use ts_ast::{ArrowFunctionData, NodeData, NodeId, SyntaxKind};
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

fn recovered_arrow(parsed: &ParseResult) -> (NodeId, &ArrowFunctionData) {
    let initializer = parsed
        .arena
        .iter()
        .find_map(|(_, node)| {
            let NodeData::VariableDeclaration(declaration) = &node.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(declaration.name)?.data else {
                return None;
            };
            if name.text == "predicate" {
                declaration.initializer
            } else {
                None
            }
        })
        .expect("expected predicate initializer");
    let NodeData::ArrowFunction(arrow) = &parsed.arena.get(initializer).unwrap().data else {
        panic!("expected recovered arrow");
    };
    (initializer, arrow)
}

fn variable_names(parsed: &ParseResult, statement: NodeId) -> Vec<&str> {
    let NodeData::VariableStatement(statement) = &parsed.arena.get(statement).unwrap().data else {
        panic!("expected variable statement");
    };
    let NodeData::VariableDeclarationList(declarations) =
        &parsed.arena.get(statement.declaration_list).unwrap().data
    else {
        panic!("expected declaration list");
    };
    declarations
        .declarations
        .nodes
        .iter()
        .map(|declaration| {
            let NodeData::VariableDeclaration(declaration) =
                &parsed.arena.get(*declaration).unwrap().data
            else {
                panic!("expected declaration");
            };
            let NodeData::Identifier(name) = &parsed.arena.get(declaration.name).unwrap().data
            else {
                panic!("expected variable name");
            };
            name.text.as_str()
        })
        .collect()
}

fn assert_following_statements(
    parsed: &ParseResult,
    source: &str,
    following: Option<(SyntaxKind, &str)>,
) {
    let NodeData::SourceFile(root) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected source file");
    };
    assert_eq!(root.statements.nodes.len(), 2);
    let NodeData::VariableStatement(statement) =
        &parsed.arena.get(root.statements.nodes[1]).unwrap().data
    else {
        panic!("expected following top-level variable");
    };
    let NodeData::VariableDeclarationList(declarations) =
        &parsed.arena.get(statement.declaration_list).unwrap().data
    else {
        panic!("expected following declaration list");
    };
    let [declaration] = declarations.declarations.nodes.as_slice() else {
        panic!("expected one following declaration");
    };
    let NodeData::VariableDeclaration(declaration) = &parsed.arena.get(*declaration).unwrap().data
    else {
        panic!("expected following declaration");
    };
    let NodeData::Identifier(name) = &parsed.arena.get(declaration.name).unwrap().data else {
        panic!("expected following name");
    };
    assert_eq!(name.text, "after");
    let initializer = parsed.arena.get(declaration.initializer.unwrap()).unwrap();
    assert_eq!(initializer.kind, SyntaxKind::NumericLiteral);
    let start = source.rfind("1;").unwrap();
    assert_eq!(initializer.range.start.get() as usize, start);
    assert_eq!(initializer.range.end.get() as usize, start + 1);

    if let Some((kind, text)) = following {
        let NodeData::FunctionDeclaration(function) =
            &parsed.arena.get(root.statements.nodes[0]).unwrap().data
        else {
            panic!("expected enclosing function");
        };
        let NodeData::Block(body) = &parsed.arena.get(function.body.unwrap()).unwrap().data else {
            panic!("expected enclosing body");
        };
        let statement = parsed
            .arena
            .get(*body.statements.nodes.last().unwrap())
            .unwrap();
        let NodeData::ExpressionStatement(expression) = &statement.data else {
            panic!("expected following value expression");
        };
        assert_eq!(parsed.arena.get(expression.expression).unwrap().kind, kind);
        let start = source.find(text).unwrap();
        assert_eq!(statement.range.start.get() as usize, start);
        assert_eq!(statement.range.end.get() as usize, start + text.len());
    }
}

fn assert_recovery(
    source: &str,
    expected: &[(u32, u32, u32)],
    expected_body: &str,
    following: Option<(SyntaxKind, &str)>,
) {
    let modes = [
        ("ts", parse_source_file(source)),
        ("tsx", parse_jsx_source_file(source)),
    ];
    for (mode, parsed) in &modes {
        let (initializer, arrow) = recovered_arrow(parsed);
        let body = parsed.arena.get(arrow.body).unwrap();
        let text = source
            .get(body.range.start.get() as usize..body.range.end.get() as usize)
            .unwrap_or("<invalid range>");
        eprintln!(
            "mode={mode} diagnostics={:?} arrow_end={} body={:?} range={:?} text={text:?}",
            diagnostic_locations(parsed),
            parsed.arena.get(initializer).unwrap().range.end.get(),
            body.kind,
            body.range,
        );
    }
    for (mode, parsed) in modes {
        assert_eq!(diagnostic_locations(&parsed), expected, "{mode}: {source}");
        let (initializer, arrow) = recovered_arrow(&parsed);
        let body = parsed.arena.get(arrow.body).unwrap();
        let NodeData::Identifier(name) = &body.data else {
            panic!("expected identifier recovery body");
        };
        assert_eq!(name.text, expected_body, "{mode}");
        assert_eq!(
            (body.range.start.get(), body.range.end.get()),
            (expected[0].1, expected[0].2),
            "{mode}",
        );
        assert_eq!(
            parsed.arena.get(initializer).unwrap().range.end.get(),
            expected[0].2,
            "{mode}",
        );
        assert_following_statements(&parsed, source, following);
    }
}

#[test]
fn await_predicate_recovery_matches_exact_go_ranges() {
    assert_recovery(
        concat!(
            "async function outer() {\n",
            "  const predicate = (value: unknown): await is string => true;\n",
            "  await action();\n",
            "}\n",
            "const after = 1;\n",
        ),
        &[(1005, 69, 71), (1005, 72, 78), (1005, 79, 81)],
        "is",
        Some((SyntaxKind::AwaitExpression, "await action();")),
    );
}

#[test]
fn yield_predicate_recovery_matches_exact_go_ranges() {
    assert_recovery(
        concat!(
            "function* outer() {\n",
            "  const predicate = (value: unknown): yield is string => true;\n",
            "  yield 1;\n",
            "}\n",
            "const after = 1;\n",
        ),
        &[(1005, 64, 66), (1005, 67, 73), (1005, 74, 76)],
        "is",
        Some((SyntaxKind::YieldExpression, "yield 1;")),
    );
}

#[test]
fn missing_arrow_consumes_an_ordinary_identifier_body() {
    assert_recovery(
        "const predicate = (value: unknown): number body;\nconst after = 1;\n",
        &[(1005, 43, 47)],
        "body",
        None,
    );
}

#[test]
fn missing_comma_keeps_contextual_names_in_the_declaration_list() {
    let source = concat!(
        "async function* outer() {\n",
        "  const before = 0 string = 1;\n",
        "  const next = 0 await = 1;\n",
        "  const third = 0 yield = 1;\n",
        "}\n",
        "const after = 1;\n",
    );
    for parse in [parse_source_file, parse_jsx_source_file] {
        let parsed = parse(source);
        assert_eq!(
            diagnostic_locations(&parsed),
            [(1005, 45, 51), (1005, 74, 79), (1005, 103, 108)],
        );
        assert_following_statements(&parsed, source, None);
        let NodeData::SourceFile(root) = &parsed.arena.get(parsed.source_file).unwrap().data else {
            panic!("expected source file");
        };
        let NodeData::FunctionDeclaration(function) =
            &parsed.arena.get(root.statements.nodes[0]).unwrap().data
        else {
            panic!("expected enclosing function");
        };
        let NodeData::Block(body) = &parsed.arena.get(function.body.unwrap()).unwrap().data else {
            panic!("expected enclosing body");
        };
        assert_eq!(body.statements.nodes.len(), 3);
        for (statement, names) in body.statements.nodes.iter().zip([
            ["before", "string"],
            ["next", "await"],
            ["third", "yield"],
        ]) {
            assert_eq!(variable_names(&parsed, *statement), names);
        }
    }
}

#[test]
fn line_break_and_of_end_a_variable_declaration_list() {
    for (source, expected, expression_kind) in [
        (
            "const before = 0\nstring = 1;\nconst after = 1;\n",
            vec![],
            SyntaxKind::BinaryExpression,
        ),
        (
            "const before = 0 of;\nconst after = 1;\n",
            vec![(1005, 17, 19)],
            SyntaxKind::Identifier,
        ),
    ] {
        for parse in [parse_source_file, parse_jsx_source_file] {
            let parsed = parse(source);
            assert_eq!(diagnostic_locations(&parsed), expected, "{source}");
            let NodeData::SourceFile(root) = &parsed.arena.get(parsed.source_file).unwrap().data
            else {
                panic!("expected source file");
            };
            assert_eq!(root.statements.nodes.len(), 3);
            assert_eq!(
                variable_names(&parsed, root.statements.nodes[0]),
                ["before"]
            );
            assert_eq!(variable_names(&parsed, root.statements.nodes[2]), ["after"]);
            let NodeData::ExpressionStatement(statement) =
                &parsed.arena.get(root.statements.nodes[1]).unwrap().data
            else {
                panic!("expected following expression");
            };
            assert_eq!(
                parsed.arena.get(statement.expression).unwrap().kind,
                expression_kind,
            );
        }
    }
}
