use ts_ast::{NodeData, NodeId, SyntaxKind};
use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};

const ORIGINAL_SOURCE: &str = concat!(
    "const fn = <T,>(value: T): (<U>() => void) => () => {};\n",
    "const after = 1;\n",
);

#[test]
fn parenthesized_generic_return_type_in_typescript() {
    assert_original_return_type(&parse_source_file(ORIGINAL_SOURCE));
}

#[test]
fn parenthesized_generic_return_type_in_tsx() {
    assert_original_return_type(&parse_jsx_source_file(ORIGINAL_SOURCE));
}

#[test]
fn nested_generic_types_keep_the_outer_arrow_boundary() {
    for (type_text, type_kind) in [
        ("((<U>() => void))", SyntaxKind::ParenthesizedType),
        (
            "(<U extends T = T>(value: U) => U)",
            SyntaxKind::ParenthesizedType,
        ),
        ("value is (<U>() => void)", SyntaxKind::TypePredicate),
        ("(callback: <U>() => U) => T", SyntaxKind::FunctionType),
    ] {
        let source =
            format!("const fn = <const T,>(value: T): {type_text} => value;\nconst after = 1;\n");
        for parsed in [parse_source_file(&source), parse_jsx_source_file(&source)] {
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}: {:?}",
                parsed.diagnostics
            );
            let statements = source_statements(&parsed);
            assert_eq!(statements.len(), 2, "{source}");
            let node = parsed
                .arena
                .get(initializer(&parsed, statements, "fn"))
                .unwrap();
            let NodeData::ArrowFunction(arrow) = &node.data else {
                panic!("expected generic arrow: {source}");
            };
            assert_eq!(
                node.range.end.get() as usize,
                source.find(";\nconst after").unwrap()
            );
            assert_eq!(
                parsed.arena.get(arrow.type_.unwrap()).unwrap().kind,
                type_kind
            );
            let NodeData::Identifier(body) = &parsed.arena.get(arrow.body).unwrap().data else {
                panic!("expected outer arrow body: {source}");
            };
            assert_eq!(body.text, "value");
            assert_eq!(
                parsed
                    .arena
                    .get(initializer(&parsed, statements, "after"))
                    .unwrap()
                    .kind,
                SyntaxKind::NumericLiteral
            );
        }
    }
}

#[test]
fn parenthesized_generic_types_restore_enclosing_value_contexts() {
    for (prefix, return_type, body_text, value, value_kind) in [
        (
            "async function",
            "(<await>() => void)",
            "() => {}",
            "await action();",
            SyntaxKind::AwaitExpression,
        ),
        (
            "function*",
            "value is (<yield>() => void)",
            "false",
            "yield 1;",
            SyntaxKind::YieldExpression,
        ),
        (
            "async function*",
            "(<await, yield>() => void)",
            "() => {}",
            "yield await action();",
            SyntaxKind::YieldExpression,
        ),
    ] {
        let source = format!(
            "{prefix} outer() {{ const fn = <T,>(value: T): {return_type} => {body_text}; {value} const innerAfter = 1; }}\nconst after = 2;\n"
        );
        for parsed in [parse_source_file(&source), parse_jsx_source_file(&source)] {
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}: {:?}",
                parsed.diagnostics
            );
            let statements = source_statements(&parsed);
            assert_eq!(statements.len(), 2);
            let NodeData::FunctionDeclaration(outer) =
                &parsed.arena.get(statements[0]).unwrap().data
            else {
                panic!("expected outer function");
            };
            let NodeData::Block(body) = &parsed.arena.get(outer.body.unwrap()).unwrap().data else {
                panic!("expected function body");
            };
            let body = &body.statements.nodes;
            assert_eq!(body.len(), 3);
            assert_eq!(
                parsed
                    .arena
                    .get(initializer(&parsed, body, "fn"))
                    .unwrap()
                    .kind,
                SyntaxKind::ArrowFunction
            );
            let NodeData::ExpressionStatement(statement) = &parsed.arena.get(body[1]).unwrap().data
            else {
                panic!("expected value expression");
            };
            let expression = parsed.arena.get(statement.expression).unwrap();
            assert_eq!(expression.kind, value_kind);
            if prefix == "async function*" {
                let NodeData::YieldExpression(expression) = &expression.data else {
                    panic!("expected yield expression");
                };
                assert_eq!(
                    parsed
                        .arena
                        .get(expression.expression.unwrap())
                        .unwrap()
                        .kind,
                    SyntaxKind::AwaitExpression
                );
            }
            assert_eq!(
                parsed
                    .arena
                    .get(initializer(&parsed, body, "innerAfter"))
                    .unwrap()
                    .kind,
                SyntaxKind::NumericLiteral
            );
            assert_eq!(
                parsed
                    .arena
                    .get(initializer(&parsed, statements, "after"))
                    .unwrap()
                    .kind,
                SyntaxKind::NumericLiteral
            );
        }
    }
}

#[test]
fn malformed_parenthesized_generic_types_keep_following_declarations() {
    for declaration in [
        "const fn = <T,>(value: T): (<U>() => void);",
        "const fn = <T,>(value: T): (<U>() => ) => () => {};",
        "const fn = <T,>(value: T): (<,>() => void) => () => {};",
        "const fn = <T,>(value: T): (<U() => void) => () => {};",
    ] {
        let source = format!("{declaration}\nconst after = 1;\n");
        for parsed in [parse_source_file(&source), parse_jsx_source_file(&source)] {
            assert!(!parsed.diagnostics.is_empty(), "{source}");
            let statements = source_statements(&parsed);
            let after = parsed
                .arena
                .get(initializer(&parsed, statements, "after"))
                .unwrap();
            assert_eq!(after.kind, SyntaxKind::NumericLiteral, "{source}");
            assert_eq!(after.range.start.get() as usize, source.rfind('1').unwrap());
            assert!(
                parsed.diagnostics.iter().all(|diagnostic| {
                    diagnostic.range.end.get() as usize <= source.find("const after").unwrap()
                }),
                "{source}: {:?}",
                parsed.diagnostics
            );
        }
    }
}

fn assert_original_return_type(parsed: &ParseResult) {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let statements = source_statements(parsed);
    assert_eq!(statements.len(), 2);
    let node = parsed
        .arena
        .get(initializer(parsed, statements, "fn"))
        .unwrap();
    let NodeData::ArrowFunction(arrow) = &node.data else {
        panic!("expected generic arrow");
    };
    assert_eq!(node.range.end.get(), 54);
    let NodeData::ParenthesizedTypeNode(parenthesized) =
        &parsed.arena.get(arrow.type_.unwrap()).unwrap().data
    else {
        panic!("expected parenthesized return type");
    };
    let NodeData::FunctionTypeNode(function) = &parsed.arena.get(parenthesized.type_).unwrap().data
    else {
        panic!("expected generic function type");
    };
    let parameters = function.type_parameters.as_ref().unwrap();
    assert_eq!(parameters.nodes.len(), 1);
    let NodeData::TypeParameterDeclaration(parameter) =
        &parsed.arena.get(parameters.nodes[0]).unwrap().data
    else {
        panic!("expected type parameter");
    };
    let NodeData::Identifier(name) = &parsed.arena.get(parameter.name).unwrap().data else {
        panic!("expected type parameter name");
    };
    assert_eq!(name.text, "U");
    assert_eq!(
        parsed.arena.get(function.type_.unwrap()).unwrap().kind,
        SyntaxKind::VoidKeyword
    );
    assert_eq!(
        parsed.arena.get(arrow.body).unwrap().kind,
        SyntaxKind::ArrowFunction
    );
    assert_eq!(
        parsed
            .arena
            .get(initializer(parsed, statements, "after"))
            .unwrap()
            .kind,
        SyntaxKind::NumericLiteral
    );
}

fn source_statements(parsed: &ParseResult) -> &[NodeId] {
    let NodeData::SourceFile(root) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected source file");
    };
    &root.statements.nodes
}

fn initializer(parsed: &ParseResult, statements: &[NodeId], name: &str) -> NodeId {
    statements
        .iter()
        .find_map(|statement| {
            let NodeData::VariableStatement(statement) = &parsed.arena.get(*statement)?.data else {
                return None;
            };
            let NodeData::VariableDeclarationList(declarations) =
                &parsed.arena.get(statement.declaration_list)?.data
            else {
                return None;
            };
            declarations
                .declarations
                .nodes
                .iter()
                .find_map(|declaration| {
                    let NodeData::VariableDeclaration(declaration) =
                        &parsed.arena.get(*declaration)?.data
                    else {
                        return None;
                    };
                    let NodeData::Identifier(identifier) =
                        &parsed.arena.get(declaration.name)?.data
                    else {
                        return None;
                    };
                    (identifier.text == name).then_some(declaration.initializer?)
                })
        })
        .unwrap()
}
