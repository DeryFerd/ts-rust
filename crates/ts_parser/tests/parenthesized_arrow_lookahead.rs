use ts_ast::{Node, NodeData, NodeId, SyntaxKind};
use ts_parser::{ParseResult, parse_source_file};

fn node(parsed: &ParseResult, id: NodeId) -> &Node {
    parsed.arena.get(id).expect("node belongs to this parse")
}

fn source_text(parsed: &ParseResult, id: NodeId) -> &str {
    let range = node(parsed, id).range;
    &parsed.arena.source_text().unwrap()[range.start.get() as usize..range.end.get() as usize]
}

fn child(parsed: &ParseResult, parent: NodeId, id: NodeId) -> &Node {
    let record = node(parsed, id);
    let owner = node(parsed, parent);
    assert_eq!(record.parent, Some(parent));
    assert!(owner.range.start <= record.range.start);
    assert!(record.range.end <= owner.range.end);
    record
}

fn exact(parsed: &ParseResult, id: NodeId, kind: SyntaxKind, text: &str) {
    assert_eq!(node(parsed, id).kind, kind);
    assert_eq!(source_text(parsed, id), text);
}

fn unique_range(parsed: &ParseResult, id: NodeId, text: &str) {
    let source = parsed.arena.source_text().unwrap();
    assert_eq!(source.matches(text).count(), 1, "{text}");
    let start = source.find(text).unwrap();
    assert_eq!(node(parsed, id).range.start.get() as usize, start);
    assert_eq!(
        node(parsed, id).range.end.get() as usize,
        start + text.len()
    );
}

fn statements(parsed: &ParseResult, owner: NodeId) -> &[NodeId] {
    let list = match &node(parsed, owner).data {
        NodeData::SourceFile(file) => &file.statements,
        NodeData::Block(block) => &block.statements,
        other => panic!("expected statement owner, got {other:?}"),
    };
    for &id in &list.nodes {
        child(parsed, owner, id);
    }
    &list.nodes
}

fn initializer(parsed: &ParseResult, statement: NodeId, name: &str) -> NodeId {
    let NodeData::VariableStatement(statement_data) = &node(parsed, statement).data else {
        panic!("expected variable statement");
    };
    let list_id = statement_data.declaration_list;
    let NodeData::VariableDeclarationList(list) = &child(parsed, statement, list_id).data else {
        panic!("expected declaration list");
    };
    let [declaration] = list.declarations.nodes.as_slice() else {
        panic!("expected one declaration");
    };
    let NodeData::VariableDeclaration(variable) = &child(parsed, list_id, *declaration).data else {
        panic!("expected variable");
    };
    child(parsed, *declaration, variable.name);
    exact(parsed, variable.name, SyntaxKind::Identifier, name);
    let value = variable.initializer.unwrap();
    child(parsed, *declaration, value);
    value
}

fn returned_expression(parsed: &ParseResult, owner: NodeId, body: NodeId) -> NodeId {
    assert_eq!(child(parsed, owner, body).kind, SyntaxKind::Block);
    let [statement] = statements(parsed, body) else {
        panic!("expected one return statement");
    };
    let NodeData::ReturnStatement(returned) = &node(parsed, *statement).data else {
        panic!("expected return");
    };
    let expression = returned.expression.unwrap();
    child(parsed, *statement, expression);
    expression
}

fn grouped_cast(parsed: &ParseResult, parent: NodeId, group: NodeId) -> (NodeId, NodeId) {
    let NodeData::ParenthesizedExpression(grouped) = &child(parsed, parent, group).data else {
        panic!("expected grouped expression");
    };
    let cast_id = grouped.expression;
    let NodeData::AsExpression(cast) = &child(parsed, group, cast_id).data else {
        panic!("expected cast inside the group");
    };
    let grouped_text = source_text(parsed, group);
    exact(
        parsed,
        cast_id,
        SyntaxKind::AsExpression,
        &grouped_text[1..grouped_text.len() - 1],
    );
    assert_eq!(
        node(parsed, cast_id).range.start.get(),
        node(parsed, group).range.start.get() + 1
    );
    assert_eq!(
        node(parsed, cast_id).range.end.get() + 1,
        node(parsed, group).range.end.get()
    );
    child(parsed, cast_id, cast.expression);
    child(parsed, cast_id, cast.type_);
    (cast.expression, cast.type_)
}

fn assert_arrow(parsed: &ParseResult, arrow_id: NodeId, count: usize, body: &str) {
    let NodeData::ArrowFunction(arrow) = &node(parsed, arrow_id).data else {
        panic!("expected real arrow");
    };
    assert_eq!(arrow.parameters.nodes.len(), count);
    for &parameter in &arrow.parameters.nodes {
        assert_eq!(
            child(parsed, arrow_id, parameter).kind,
            SyntaxKind::Parameter
        );
    }
    child(parsed, arrow_id, arrow.equals_greater_than_token);
    exact(
        parsed,
        arrow.equals_greater_than_token,
        SyntaxKind::EqualsGreaterThanToken,
        "=>",
    );
    child(parsed, arrow_id, arrow.body);
    assert_eq!(source_text(parsed, arrow.body), body);
}

fn arrow_count(parsed: &ParseResult) -> usize {
    parsed
        .arena
        .iter()
        .filter(|(_, node)| node.kind == SyntaxKind::ArrowFunction)
        .count()
}

#[test]
#[allow(clippy::too_many_lines)] // Checks the complete class and cast ownership in four source variants.
fn grouped_new_cast_keeps_its_ternary_and_later_class_member() {
    for semicolon in ["", ";"] {
        for later_arrow in [false, true] {
            let later = if later_arrow {
                "(value: string) => value"
            } else {
                "value"
            };
            let source = format!(
                "class Reply {{\n  text(text) {{\n    return ready ? (new Response(text) as ReturnType<TextRespond>) : fallback{semicolon}\n  }}\n  later() {{\n    const after = {later}\n  }}\n}}\n"
            );
            let parsed = parse_source_file(&source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}\n{:#?}",
                parsed.diagnostics
            );
            assert_eq!(parsed.arena.source_text(), Some(source.as_str()));
            let [class_id] = statements(&parsed, parsed.source_file) else {
                panic!("expected one class");
            };
            let NodeData::ClassDeclaration(class) = &node(&parsed, *class_id).data else {
                panic!("expected class");
            };
            let [first, second] = class.members.nodes.as_slice() else {
                panic!("expected both original methods");
            };
            let NodeData::MethodDeclaration(method) = &child(&parsed, *class_id, *first).data
            else {
                panic!("expected text method");
            };
            child(&parsed, *first, method.name);
            exact(&parsed, method.name, SyntaxKind::Identifier, "text");
            let conditional_id = returned_expression(&parsed, *first, method.body.unwrap());
            let NodeData::ConditionalExpression(conditional) = &node(&parsed, conditional_id).data
            else {
                panic!("expected ternary");
            };
            unique_range(
                &parsed,
                conditional_id,
                "ready ? (new Response(text) as ReturnType<TextRespond>) : fallback",
            );
            for id in [
                conditional.condition,
                conditional.question_token,
                conditional.colon_token,
                conditional.when_false,
            ] {
                child(&parsed, conditional_id, id);
            }
            exact(
                &parsed,
                conditional.condition,
                SyntaxKind::Identifier,
                "ready",
            );
            exact(
                &parsed,
                conditional.question_token,
                SyntaxKind::QuestionToken,
                "?",
            );
            exact(
                &parsed,
                conditional.colon_token,
                SyntaxKind::ColonToken,
                ":",
            );
            exact(
                &parsed,
                conditional.when_false,
                SyntaxKind::Identifier,
                "fallback",
            );
            unique_range(
                &parsed,
                conditional.when_true,
                "(new Response(text) as ReturnType<TextRespond>)",
            );
            let (constructed, type_id) =
                grouped_cast(&parsed, conditional_id, conditional.when_true);
            exact(
                &parsed,
                constructed,
                SyntaxKind::NewExpression,
                "new Response(text)",
            );
            unique_range(&parsed, constructed, "new Response(text)");
            let NodeData::NewExpression(new) = &node(&parsed, constructed).data else {
                unreachable!()
            };
            assert!(new.type_arguments.is_none());
            child(&parsed, constructed, new.expression);
            exact(&parsed, new.expression, SyntaxKind::Identifier, "Response");
            let [argument] = new.arguments.as_ref().unwrap().nodes.as_slice() else {
                panic!("expected text argument");
            };
            child(&parsed, constructed, *argument);
            exact(&parsed, *argument, SyntaxKind::Identifier, "text");
            unique_range(&parsed, type_id, "ReturnType<TextRespond>");
            let NodeData::TypeReferenceNode(type_) = &node(&parsed, type_id).data else {
                panic!("expected written generic type");
            };
            child(&parsed, type_id, type_.type_name);
            exact(
                &parsed,
                type_.type_name,
                SyntaxKind::Identifier,
                "ReturnType",
            );
            let [type_argument] = type_.type_arguments.as_ref().unwrap().nodes.as_slice() else {
                panic!("expected one type argument");
            };
            child(&parsed, type_id, *type_argument);
            exact(
                &parsed,
                *type_argument,
                SyntaxKind::TypeReference,
                "TextRespond",
            );
            let NodeData::MethodDeclaration(later_method) =
                &child(&parsed, *class_id, *second).data
            else {
                panic!("expected later method");
            };
            child(&parsed, *second, later_method.name);
            exact(&parsed, later_method.name, SyntaxKind::Identifier, "later");
            let body = later_method.body.unwrap();
            child(&parsed, *second, body);
            let [statement] = statements(&parsed, body) else {
                panic!("expected later declaration")
            };
            let after = initializer(&parsed, *statement, "after");
            assert!(node(&parsed, conditional_id).range.end < node(&parsed, after).range.start);
            if later_arrow {
                assert_arrow(&parsed, after, 1, "value");
                unique_range(&parsed, after, later);
            } else {
                exact(&parsed, after, SyntaxKind::Identifier, "value");
            }
            assert_eq!(arrow_count(&parsed), usize::from(later_arrow));
        }
    }
}

#[test]
#[allow(clippy::too_many_lines)] // Checks both ternary arms and the separate callback in four source variants.
fn grouped_member_call_cast_keeps_optional_access_and_later_callback() {
    for semicolon in ["", ";"] {
        for later_arrow in [false, true] {
            let callback = if later_arrow {
                "(value) => value"
            } else {
                "identity"
            };
            let source = format!(
                "function pick<T>(values, context) {{\n  return values?.length ? (values.at(-1) as T) : context.values[0]{semicolon}\n}}\nconst later = source.map({callback})\n"
            );
            let parsed = parse_source_file(&source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}\n{:#?}",
                parsed.diagnostics
            );
            let [function_id, later_statement] = statements(&parsed, parsed.source_file) else {
                panic!("expected function and later declaration");
            };
            let NodeData::FunctionDeclaration(function) = &node(&parsed, *function_id).data else {
                panic!("expected function");
            };
            let conditional_id = returned_expression(&parsed, *function_id, function.body.unwrap());
            let NodeData::ConditionalExpression(conditional) = &node(&parsed, conditional_id).data
            else {
                panic!("expected ternary");
            };
            unique_range(
                &parsed,
                conditional_id,
                "values?.length ? (values.at(-1) as T) : context.values[0]",
            );
            let NodeData::PropertyAccessExpression(condition) =
                &child(&parsed, conditional_id, conditional.condition).data
            else {
                panic!("expected optional property access");
            };
            for id in [
                condition.expression,
                condition.name,
                condition.question_dot_token.unwrap(),
            ] {
                child(&parsed, conditional.condition, id);
            }
            exact(
                &parsed,
                condition.expression,
                SyntaxKind::Identifier,
                "values",
            );
            exact(&parsed, condition.name, SyntaxKind::Identifier, "length");
            exact(
                &parsed,
                condition.question_dot_token.unwrap(),
                SyntaxKind::QuestionDotToken,
                "?.",
            );
            for (id, kind, text) in [
                (conditional.question_token, SyntaxKind::QuestionToken, "?"),
                (conditional.colon_token, SyntaxKind::ColonToken, ":"),
            ] {
                child(&parsed, conditional_id, id);
                exact(&parsed, id, kind, text);
            }
            unique_range(&parsed, conditional.when_true, "(values.at(-1) as T)");
            let (call_id, type_id) = grouped_cast(&parsed, conditional_id, conditional.when_true);
            unique_range(&parsed, call_id, "values.at(-1)");
            exact(&parsed, type_id, SyntaxKind::TypeReference, "T");
            let NodeData::CallExpression(call) = &node(&parsed, call_id).data else {
                panic!("expected original member call");
            };
            assert!(call.question_dot_token.is_none());
            assert!(call.type_arguments.is_none());
            let NodeData::PropertyAccessExpression(access) =
                &child(&parsed, call_id, call.expression).data
            else {
                panic!("expected member access");
            };
            assert!(access.question_dot_token.is_none());
            child(&parsed, call.expression, access.expression);
            child(&parsed, call.expression, access.name);
            exact(&parsed, access.expression, SyntaxKind::Identifier, "values");
            exact(&parsed, access.name, SyntaxKind::Identifier, "at");
            let [argument] = call.arguments.nodes.as_slice() else {
                panic!("expected one argument")
            };
            let NodeData::PrefixUnaryExpression(negative) =
                &child(&parsed, call_id, *argument).data
            else {
                panic!("expected negative index");
            };
            exact(&parsed, *argument, SyntaxKind::PrefixUnaryExpression, "-1");
            assert_eq!(negative.operator, SyntaxKind::MinusToken);
            child(&parsed, *argument, negative.operand);
            exact(&parsed, negative.operand, SyntaxKind::NumericLiteral, "1");
            let NodeData::ElementAccessExpression(fallback) =
                &child(&parsed, conditional_id, conditional.when_false).data
            else {
                panic!("expected indexed fallback");
            };
            unique_range(&parsed, conditional.when_false, "context.values[0]");
            assert!(fallback.question_dot_token.is_none());
            child(
                &parsed,
                conditional.when_false,
                fallback.argument_expression,
            );
            exact(
                &parsed,
                fallback.argument_expression,
                SyntaxKind::NumericLiteral,
                "0",
            );
            let NodeData::PropertyAccessExpression(property) =
                &child(&parsed, conditional.when_false, fallback.expression).data
            else {
                panic!("expected fallback property");
            };
            child(&parsed, fallback.expression, property.expression);
            child(&parsed, fallback.expression, property.name);
            exact(
                &parsed,
                property.expression,
                SyntaxKind::Identifier,
                "context",
            );
            exact(&parsed, property.name, SyntaxKind::Identifier, "values");
            let later = initializer(&parsed, *later_statement, "later");
            let NodeData::CallExpression(map) = &node(&parsed, later).data else {
                panic!("expected later map call")
            };
            let NodeData::PropertyAccessExpression(map_name) =
                &child(&parsed, later, map.expression).data
            else {
                panic!("expected map member access");
            };
            child(&parsed, map.expression, map_name.expression);
            child(&parsed, map.expression, map_name.name);
            exact(
                &parsed,
                map_name.expression,
                SyntaxKind::Identifier,
                "source",
            );
            exact(&parsed, map_name.name, SyntaxKind::Identifier, "map");
            let [argument] = map.arguments.nodes.as_slice() else {
                panic!("expected callback argument")
            };
            child(&parsed, later, *argument);
            assert!(node(&parsed, conditional_id).range.end < node(&parsed, *argument).range.start);
            if later_arrow {
                assert_arrow(&parsed, *argument, 1, "value");
                unique_range(&parsed, *argument, callback);
            } else {
                exact(&parsed, *argument, SyntaxKind::Identifier, "identity");
            }
            assert_eq!(arrow_count(&parsed), usize::from(later_arrow));
        }
    }
}

#[test]
fn definite_and_uncertain_heads_keep_real_arrows_and_grouped_expressions() {
    for (head, count) in [
        ("()", 0),
        ("(...values)", 1),
        ("(value?)", 1),
        ("(value: string)", 1),
        ("(value)", 1),
        ("(value = 1)", 1),
        ("(left, right)", 2),
        ("({ value })", 1),
        ("([value])", 1),
    ] {
        let source = format!("const arrow = {head} => value;\nconst after = 1;\n");
        let parsed = parse_source_file(&source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}\n{:#?}",
            parsed.diagnostics
        );
        let [first, after] = statements(&parsed, parsed.source_file) else {
            panic!("expected two statements")
        };
        let arrow_id = initializer(&parsed, *first, "arrow");
        assert_arrow(&parsed, arrow_id, count, "value");
        unique_range(&parsed, arrow_id, &format!("{head} => value"));
        assert_eq!(arrow_count(&parsed), 1);
        exact(
            &parsed,
            initializer(&parsed, *after, "after"),
            SyntaxKind::NumericLiteral,
            "1",
        );
        let NodeData::ArrowFunction(arrow) = &node(&parsed, arrow_id).data else {
            unreachable!()
        };
        if let Some(&parameter_id) = arrow.parameters.nodes.first() {
            let NodeData::ParameterDeclaration(parameter) = &node(&parsed, parameter_id).data
            else {
                unreachable!()
            };
            child(&parsed, parameter_id, parameter.name);
            assert_eq!(parameter.dot_dot_dot_token.is_some(), head == "(...values)");
            assert_eq!(parameter.question_token.is_some(), head == "(value?)");
            assert_eq!(parameter.type_.is_some(), head == "(value: string)");
            assert_eq!(parameter.initializer.is_some(), head == "(value = 1)");
            for id in [
                parameter.dot_dot_dot_token,
                parameter.question_token,
                parameter.type_,
                parameter.initializer,
            ]
            .into_iter()
            .flatten()
            {
                child(&parsed, parameter_id, id);
            }
        }
    }
    for (expression, inner_kind) in [
        ("(value)", SyntaxKind::Identifier),
        ("(value = 1)", SyntaxKind::BinaryExpression),
        ("(left, right)", SyntaxKind::BinaryExpression),
        ("({ value })", SyntaxKind::ObjectLiteralExpression),
        ("([value])", SyntaxKind::ArrayLiteralExpression),
        ("(async as T)", SyntaxKind::AsExpression),
        ("(readonly as T)", SyntaxKind::AsExpression),
    ] {
        let source = format!("const grouped = {expression};\nconst after = 1;\n");
        let parsed = parse_source_file(&source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}\n{:#?}",
            parsed.diagnostics
        );
        let [first, after] = statements(&parsed, parsed.source_file) else {
            panic!("expected two statements")
        };
        let group_id = initializer(&parsed, *first, "grouped");
        let NodeData::ParenthesizedExpression(grouped) = &node(&parsed, group_id).data else {
            panic!("expected ordinary grouping");
        };
        unique_range(&parsed, group_id, expression);
        assert_eq!(
            child(&parsed, group_id, grouped.expression).kind,
            inner_kind
        );
        assert_eq!(arrow_count(&parsed), 0);
        exact(
            &parsed,
            initializer(&parsed, *after, "after"),
            SyntaxKind::NumericLiteral,
            "1",
        );
    }
}
