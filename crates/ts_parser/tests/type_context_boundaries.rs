use ts_ast::{NodeData, NodeId, SyntaxKind};
use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};

#[test]
fn nested_type_forms_restore_value_expression_context() {
    for (name, prefix, value, value_kind) in [
        (
            "await",
            "async function",
            "await action();",
            SyntaxKind::AwaitExpression,
        ),
        (
            "yield",
            "function*",
            "yield 1;",
            SyntaxKind::YieldExpression,
        ),
    ] {
        for (type_text, type_kind) in [
            (format!("<{name}>() => void"), SyntaxKind::FunctionType),
            (
                format!("new <{name}>() => object"),
                SyntaxKind::ConstructorType,
            ),
            (format!("{{ <{name}>(): void; }}"), SyntaxKind::TypeLiteral),
            (
                format!("{{ run<{name}>(): void; }}"),
                SyntaxKind::TypeLiteral,
            ),
            (
                format!("T extends unknown ? (<{name}>() => void) : never"),
                SyntaxKind::ConditionalType,
            ),
        ] {
            let source = format!(
                "{prefix} outer() {{ type Fn<T> = {type_text}; {value} const innerAfter = 1; }}\nconst after = 2;\n"
            );
            for parse in [parse_source_file, parse_jsx_source_file] {
                let parsed = parse(&source);
                assert!(
                    parsed.diagnostics.is_empty(),
                    "{source}: {:?}",
                    parsed.diagnostics
                );
                let body = outer_body_with_following_declarations(&parsed);
                assert_eq!(body.len(), 3, "{source}");
                let NodeData::TypeAliasDeclaration(alias) =
                    &parsed.arena.get(body[0]).unwrap().data
                else {
                    panic!("expected nested type alias");
                };
                assert_eq!(parsed.arena.get(alias.type_).unwrap().kind, type_kind);
                assert_value_expression_kind(&parsed, body[1], value_kind);
                assert_type_parameter_range(&parsed, &source, name);
            }
        }
    }
}

#[test]
fn async_generator_types_restore_both_value_contexts() {
    let source = concat!(
        "async function* outer() { type Fn = <await, yield>() => void; ",
        "yield await action(); const innerAfter = 1; }\nconst after = 2;\n",
    );
    for parse in [parse_source_file, parse_jsx_source_file] {
        let parsed = parse(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let body = outer_body_with_following_declarations(&parsed);
        assert_eq!(body.len(), 3);
        let NodeData::ExpressionStatement(statement) = &parsed.arena.get(body[1]).unwrap().data
        else {
            panic!("expected yield statement");
        };
        let NodeData::YieldExpression(expression) =
            &parsed.arena.get(statement.expression).unwrap().data
        else {
            panic!("expected yield expression");
        };
        assert_eq!(
            parsed
                .arena
                .get(expression.expression.unwrap())
                .unwrap()
                .kind,
            SyntaxKind::AwaitExpression,
        );
        let names = parsed
            .arena
            .iter()
            .filter_map(|(_, node)| {
                let NodeData::TypeParameterDeclaration(parameter) = &node.data else {
                    return None;
                };
                Some(identifier_text(&parsed, parameter.name))
            })
            .collect::<Vec<_>>();
        assert_eq!(names, ["await", "yield"]);
    }
}

#[test]
fn a_type_does_not_admit_reserved_value_declarations_afterwards() {
    for (name, prefix) in [("await", "async function"), ("yield", "function*")] {
        let source = format!(
            "{prefix} outer() {{ type Fn = <{name}>() => void; const invalid = <const {name},>(value: any) => value; const innerAfter = 1; }}\nconst after = 2;\n"
        );
        let start = u32::try_from(source.find("<const ").unwrap() + "<const ".len()).unwrap();
        let end = start + u32::try_from(name.len()).unwrap();
        for (parsed, expected_kind) in [
            (
                parse_source_file(&source),
                SyntaxKind::TypeAssertionExpression,
            ),
            (parse_jsx_source_file(&source), SyntaxKind::ArrowFunction),
        ] {
            let diagnostic = parsed
                .diagnostics
                .first()
                .expect("expected value-name error");
            assert_eq!(
                (diagnostic.range.start.get(), diagnostic.range.end.get()),
                (start, end),
                "{source}: {:?}",
                parsed.diagnostics,
            );
            let body = outer_body_with_following_declarations(&parsed);
            let declaration = variable_declaration(&parsed, body, "invalid").unwrap();
            let NodeData::VariableDeclaration(declaration) =
                &parsed.arena.get(declaration).unwrap().data
            else {
                panic!("expected invalid value declaration");
            };
            assert_eq!(
                parsed
                    .arena
                    .get(declaration.initializer.unwrap())
                    .unwrap()
                    .kind,
                expected_kind,
                "{source}",
            );
        }
    }
}

#[test]
fn generic_arrow_type_probes_preserve_enclosing_value_context() {
    for (name, prefix, value, value_kind) in [
        (
            "await",
            "async function",
            "await action();",
            SyntaxKind::AwaitExpression,
        ),
        (
            "yield",
            "function*",
            "yield 1;",
            SyntaxKind::YieldExpression,
        ),
    ] {
        for (return_type, expression, type_kind) in [
            (
                format!("<{name}>() => void"),
                "() => {}",
                SyntaxKind::FunctionType,
            ),
            (
                format!("value is (<{name}>() => void) & T"),
                "false",
                SyntaxKind::TypePredicate,
            ),
        ] {
            let source = format!(
                "{prefix} outer() {{ const fn = <T,>(value: T): {return_type} => {expression}; {value} const innerAfter = 1; }}\nconst after = 2;\n"
            );
            for parse in [parse_source_file, parse_jsx_source_file] {
                let parsed = parse(&source);
                assert!(
                    parsed.diagnostics.is_empty(),
                    "{source}: {:?}",
                    parsed.diagnostics
                );
                let body = outer_body_with_following_declarations(&parsed);
                assert_eq!(body.len(), 3, "{source}");
                let declaration = variable_declaration(&parsed, body, "fn").unwrap();
                let NodeData::VariableDeclaration(declaration) =
                    &parsed.arena.get(declaration).unwrap().data
                else {
                    panic!("expected arrow declaration");
                };
                let NodeData::ArrowFunction(arrow) = &parsed
                    .arena
                    .get(declaration.initializer.unwrap())
                    .unwrap()
                    .data
                else {
                    panic!("expected arrow initializer");
                };
                assert_eq!(
                    parsed.arena.get(arrow.type_.unwrap()).unwrap().kind,
                    type_kind
                );
                assert_value_expression_kind(&parsed, body[1], value_kind);
                assert_type_parameter_range(&parsed, &source, name);
            }
        }
    }
}

fn outer_body_with_following_declarations(parsed: &ParseResult) -> &[NodeId] {
    let NodeData::SourceFile(root) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected source file");
    };
    assert_eq!(root.statements.nodes.len(), 2);
    assert!(variable_declaration(parsed, &root.statements.nodes[1..], "after").is_some());
    let NodeData::FunctionDeclaration(outer) =
        &parsed.arena.get(root.statements.nodes[0]).unwrap().data
    else {
        panic!("expected outer function");
    };
    let NodeData::Block(body) = &parsed.arena.get(outer.body.unwrap()).unwrap().data else {
        panic!("expected outer function body");
    };
    assert!(variable_declaration(parsed, &body.statements.nodes, "innerAfter").is_some());
    &body.statements.nodes
}

fn variable_declaration(parsed: &ParseResult, statements: &[NodeId], name: &str) -> Option<NodeId> {
    statements.iter().find_map(|statement| {
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
            .copied()
            .find(|declaration| {
                let NodeData::VariableDeclaration(declaration) =
                    &parsed.arena.get(*declaration).unwrap().data
                else {
                    return false;
                };
                identifier_text(parsed, declaration.name) == name
            })
    })
}

fn assert_value_expression_kind(parsed: &ParseResult, statement: NodeId, expected: SyntaxKind) {
    let NodeData::ExpressionStatement(statement) = &parsed.arena.get(statement).unwrap().data
    else {
        panic!("expected value expression statement");
    };
    assert_eq!(
        parsed.arena.get(statement.expression).unwrap().kind,
        expected
    );
}

fn assert_type_parameter_range(parsed: &ParseResult, source: &str, name: &str) {
    let name_node = parsed
        .arena
        .iter()
        .find_map(|(_, node)| {
            let NodeData::TypeParameterDeclaration(parameter) = &node.data else {
                return None;
            };
            (identifier_text(parsed, parameter.name) == name).then_some(parameter.name)
        })
        .expect("expected nested type parameter");
    let range = parsed.arena.get(name_node).unwrap().range;
    let start = source.find(&format!("<{name}>")).unwrap() + 1;
    assert_eq!(range.start.get() as usize, start);
    assert_eq!(range.end.get() as usize, start + name.len());
}

fn identifier_text(parsed: &ParseResult, name: NodeId) -> &str {
    let NodeData::Identifier(identifier) = &parsed.arena.get(name).unwrap().data else {
        panic!("expected identifier");
    };
    &identifier.text
}
