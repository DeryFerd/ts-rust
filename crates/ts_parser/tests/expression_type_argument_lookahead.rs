use std::collections::HashSet;

use ts_ast::{BinaryExpressionData, NodeData, NodeId, SyntaxKind, TypeReferenceNodeData};
use ts_core::TextRange;
use ts_parser::{ParseResult, parse_source_file};

fn text(parsed: &ParseResult, range: TextRange) -> &str {
    &parsed.arena.source_text().unwrap()[range.start.get() as usize..range.end.get() as usize]
}

fn node_text(parsed: &ParseResult, id: NodeId) -> &str {
    text(parsed, parsed.arena.get(id).unwrap().range)
}

fn statements(parsed: &ParseResult) -> &[NodeId] {
    let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected a source file");
    };
    &source.statements.nodes
}

fn initializer(parsed: &ParseResult, statement: NodeId, name: &str) -> NodeId {
    let NodeData::VariableStatement(statement) = &parsed.arena.get(statement).unwrap().data else {
        panic!("expected a variable statement");
    };
    let NodeData::VariableDeclarationList(list) =
        &parsed.arena.get(statement.declaration_list).unwrap().data
    else {
        panic!("expected a declaration list");
    };
    assert_eq!(list.declarations.nodes.len(), 1);
    let NodeData::VariableDeclaration(declaration) =
        &parsed.arena.get(list.declarations.nodes[0]).unwrap().data
    else {
        panic!("expected a variable declaration");
    };
    assert_eq!(node_text(parsed, declaration.name), name);
    declaration.initializer.unwrap()
}

fn binary(parsed: &ParseResult, id: NodeId, operator: SyntaxKind) -> &BinaryExpressionData {
    let NodeData::BinaryExpression(expression) = &parsed.arena.get(id).unwrap().data else {
        panic!("expected a binary expression: {}", node_text(parsed, id));
    };
    assert_eq!(
        parsed.arena.get(expression.operator_token).unwrap().kind,
        operator
    );
    expression
}

fn reference(parsed: &ParseResult, id: NodeId) -> &TypeReferenceNodeData {
    let NodeData::TypeReferenceNode(reference) = &parsed.arena.get(id).unwrap().data else {
        panic!("expected a type reference: {}", node_text(parsed, id));
    };
    reference
}

fn assert_complete_tree(parsed: &ParseResult, source: &str) {
    assert_eq!(parsed.arena.source_text(), Some(source));
    let root = parsed.arena.get(parsed.source_file).unwrap();
    assert_eq!(root.range.start.get(), 0);
    assert_eq!(root.range.end.get() as usize, source.len());
    let NodeData::SourceFile(file) = &root.data else {
        panic!("expected a source file");
    };
    let eof = parsed.arena.get(file.end_of_file_token).unwrap();
    assert_eq!(eof.kind, SyntaxKind::EndOfFile);
    assert_eq!(eof.range.start.get() as usize, source.len());
    assert_eq!(eof.range.end.get() as usize, source.len());
    let mut pending = vec![parsed.source_file];
    let mut visited = HashSet::new();
    while let Some(id) = pending.pop() {
        assert!(visited.insert(id), "repeated child {id:?}");
        let node = parsed.arena.get(id).unwrap();
        assert!(node.range.start <= node.range.end);
        assert!(source.is_char_boundary(node.range.start.get() as usize));
        assert!(source.is_char_boundary(node.range.end.get() as usize));
        node.for_each_child(|child| {
            let record = parsed.arena.get(child).unwrap();
            assert_eq!(record.parent, Some(id));
            assert!(node.range.start <= record.range.start);
            assert!(record.range.end <= node.range.end);
            pending.push(child);
        });
    }
}

fn assert_ip_conditional(parsed: &ParseResult, id: NodeId) {
    let NodeData::ConditionalExpression(conditional) = &parsed.arena.get(id).unwrap().data else {
        panic!("expected the IP character conditional");
    };
    assert_eq!(
        node_text(parsed, id),
        "i < end ? ipv4.charCodeAt(i) : CHAR_CODE_DOT"
    );
    let comparison = binary(parsed, conditional.condition, SyntaxKind::LessThanToken);
    assert_eq!(
        parsed.arena.get(comparison.left).unwrap().kind,
        SyntaxKind::Identifier
    );
    assert_eq!(
        parsed.arena.get(comparison.right).unwrap().kind,
        SyntaxKind::Identifier
    );
    assert_eq!(node_text(parsed, comparison.left), "i");
    assert_eq!(node_text(parsed, comparison.right), "end");
    assert_eq!(node_text(parsed, conditional.question_token), "?");
    assert_eq!(node_text(parsed, conditional.colon_token), ":");
    assert_eq!(node_text(parsed, conditional.when_false), "CHAR_CODE_DOT");
    let NodeData::CallExpression(call) = &parsed.arena.get(conditional.when_true).unwrap().data
    else {
        panic!("expected charCodeAt to remain a value call");
    };
    assert_eq!(
        parsed.arena.get(call.expression).unwrap().kind,
        SyntaxKind::PropertyAccessExpression
    );
    assert_eq!(node_text(parsed, call.expression), "ipv4.charCodeAt");
    assert!(call.type_arguments.is_none());
    assert_eq!(call.arguments.nodes.len(), 1);
    assert_eq!(node_text(parsed, call.arguments.nodes[0]), "i");
}

#[test]
fn comparison_before_a_next_line_greater_equal_is_not_a_type_argument_list() {
    for separator in ["", ";"] {
        let source = format!(
            concat!(
                "  for (let i = start; i <= end; i++) {{\n",
                "    const code = i < end ? ipv4.charCodeAt(i) : CHAR_CODE_DOT{separator}\n",
                "    if (code >= CHAR_CODE_0 && code <= CHAR_CODE_9) {{}}\n",
                "  }}\n",
                "const after = 1;\n",
            ),
            separator = separator,
        );
        let parsed = parse_source_file(&source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}\n{:?}",
            parsed.diagnostics
        );
        assert_complete_tree(&parsed, &source);
        let statements = statements(&parsed);
        assert_eq!(statements.len(), 2);
        let NodeData::ForStatement(loop_) = &parsed.arena.get(statements[0]).unwrap().data else {
            panic!("expected the original for loop");
        };
        binary(
            &parsed,
            loop_.condition.unwrap(),
            SyntaxKind::LessThanEqualsToken,
        );
        assert_eq!(node_text(&parsed, loop_.incrementor.unwrap()), "i++");
        let NodeData::Block(body) = &parsed.arena.get(loop_.statement).unwrap().data else {
            panic!("expected a loop body");
        };
        assert_eq!(body.statements.nodes.len(), 2);
        assert_ip_conditional(
            &parsed,
            initializer(&parsed, body.statements.nodes[0], "code"),
        );
        let NodeData::IfStatement(if_) = &parsed.arena.get(body.statements.nodes[1]).unwrap().data
        else {
            panic!("expected the following if statement");
        };
        let and = binary(&parsed, if_.expression, SyntaxKind::AmpersandAmpersandToken);
        for (id, operator, right) in [
            (and.left, SyntaxKind::GreaterThanEqualsToken, "CHAR_CODE_0"),
            (and.right, SyntaxKind::LessThanEqualsToken, "CHAR_CODE_9"),
        ] {
            let comparison = binary(&parsed, id, operator);
            assert_eq!(node_text(&parsed, comparison.left), "code");
            assert_eq!(node_text(&parsed, comparison.right), right);
        }
        assert_eq!(
            node_text(&parsed, initializer(&parsed, statements[1], "after")),
            "1"
        );
        assert!(parsed.arena.iter().all(|(_, node)| !matches!(
            node.data,
            NodeData::ExpressionWithTypeArguments(_) | NodeData::TypeReferenceNode(_)
        )));
    }
}

fn assert_nested_argument(parsed: &ParseResult, argument: NodeId) {
    let outer = reference(parsed, argument);
    assert_eq!(node_text(parsed, outer.type_name), "Outer");
    let outer_arguments = outer.type_arguments.as_ref().unwrap();
    assert_eq!(outer_arguments.nodes.len(), 1);
    let inner = reference(parsed, outer_arguments.nodes[0]);
    assert_eq!(node_text(parsed, inner.type_name), "Inner");
    let inner_arguments = inner.type_arguments.as_ref().unwrap();
    assert_eq!(inner_arguments.nodes.len(), 1);
    let string = parsed.arena.get(inner_arguments.nodes[0]).unwrap();
    assert_eq!(string.kind, SyntaxKind::StringKeyword);
    assert!(matches!(string.data, NodeData::KeywordTypeNode(_)));
}

#[test]
fn real_nested_conditional_and_multiline_type_arguments_keep_their_grammar() {
    for type_text in [
        "Outer<Inner<string>>",
        "T extends U ? V : W",
        "\n  Outer<\n    Inner<string>\n  >\n",
    ] {
        let source = format!("const result = read<{type_text}>(value);\nconst after = 1;\n");
        let parsed = parse_source_file(&source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}\n{:?}",
            parsed.diagnostics
        );
        assert_complete_tree(&parsed, &source);
        let statements = statements(&parsed);
        assert_eq!(statements.len(), 2);
        let call_id = initializer(&parsed, statements[0], "result");
        let NodeData::CallExpression(call) = &parsed.arena.get(call_id).unwrap().data else {
            panic!("expected a generic call");
        };
        assert_eq!(
            node_text(&parsed, call_id),
            format!("read<{type_text}>(value)")
        );
        assert_eq!(node_text(&parsed, call.expression), "read");
        assert_eq!(call.arguments.nodes.len(), 1);
        assert_eq!(node_text(&parsed, call.arguments.nodes[0]), "value");
        let arguments = call.type_arguments.as_ref().unwrap();
        assert_eq!(text(&parsed, arguments.range), format!("<{type_text}>"));
        assert_eq!(arguments.nodes.len(), 1);
        assert!(!arguments.has_trailing_comma);
        let argument = arguments.nodes[0];
        if type_text.contains("extends") {
            let NodeData::ConditionalTypeNode(conditional) =
                &parsed.arena.get(argument).unwrap().data
            else {
                panic!("expected a conditional type argument");
            };
            for (id, name) in [
                (conditional.check_type, "T"),
                (conditional.extends_type, "U"),
                (conditional.true_type, "V"),
                (conditional.false_type, "W"),
            ] {
                assert_eq!(node_text(&parsed, reference(&parsed, id).type_name), name);
            }
        } else {
            assert_nested_argument(&parsed, argument);
        }
        assert_eq!(
            node_text(&parsed, initializer(&parsed, statements[1], "after")),
            "1"
        );
    }
}

#[test]
fn accepted_type_argument_followers_keep_optional_calls_templates_and_assignments() {
    let source = concat!(
        "read?.<number>(value);\n",
        "tag<string>`value`;\n",
        "holder.read<number> = replacement;\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_complete_tree(&parsed, source);
    let expressions = statements(&parsed)
        .iter()
        .map(|id| {
            let NodeData::ExpressionStatement(statement) = &parsed.arena.get(*id).unwrap().data
            else {
                panic!("expected an expression statement");
            };
            statement.expression
        })
        .collect::<Vec<_>>();
    assert_eq!(expressions.len(), 3);
    let NodeData::CallExpression(call) = &parsed.arena.get(expressions[0]).unwrap().data else {
        panic!("expected an optional generic call");
    };
    assert_eq!(node_text(&parsed, call.question_dot_token.unwrap()), "?.");
    assert_eq!(
        text(&parsed, call.type_arguments.as_ref().unwrap().range),
        "<number>"
    );
    assert_eq!(call.arguments.nodes.len(), 1);
    assert_eq!(node_text(&parsed, call.arguments.nodes[0]), "value");
    let NodeData::TaggedTemplateExpression(tagged) =
        &parsed.arena.get(expressions[1]).unwrap().data
    else {
        panic!("expected a generic tagged template");
    };
    assert_eq!(
        text(&parsed, tagged.type_arguments.as_ref().unwrap().range),
        "<string>"
    );
    assert_eq!(node_text(&parsed, tagged.template), "`value`");
    let assignment = binary(&parsed, expressions[2], SyntaxKind::EqualsToken);
    let NodeData::ExpressionWithTypeArguments(instantiation) =
        &parsed.arena.get(assignment.left).unwrap().data
    else {
        panic!("expected an instantiation on the left of assignment");
    };
    assert_eq!(node_text(&parsed, instantiation.expression), "holder.read");
    assert_eq!(
        text(
            &parsed,
            instantiation.type_arguments.as_ref().unwrap().range
        ),
        "<number>"
    );
    assert_eq!(node_text(&parsed, assignment.right), "replacement");
}

#[test]
fn a_real_closing_angle_keeps_recoverable_type_errors_in_the_live_parse() {
    let source = concat!(
        "const result = read<\n",
        "  // @ts-expect-error checked once\n",
        "  { value: }\n",
        ">(item);\n",
        "const after = 1;\n",
    );
    let parsed = parse_source_file(source);
    let error_start = u32::try_from(source.find('}').unwrap()).unwrap();
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
        [(Some(1110), error_start, error_start + 1, "Type expected.")]
    );
    assert_eq!(parsed.comment_directives.len(), 1);
    assert!(parsed.comment_directives[0].expect_error);
    assert_eq!(
        text(&parsed, parsed.comment_directives[0].range),
        "// @ts-expect-error checked once"
    );
    assert_complete_tree(&parsed, source);
    let statements = statements(&parsed);
    assert_eq!(statements.len(), 2);
    let call_id = initializer(&parsed, statements[0], "result");
    let NodeData::CallExpression(call) = &parsed.arena.get(call_id).unwrap().data else {
        panic!("expected a recovered generic call with a real closing angle");
    };
    let arguments = call.type_arguments.as_ref().unwrap();
    assert_eq!(arguments.nodes.len(), 1);
    assert_eq!(
        arguments.range.start.get() as usize,
        source.find('<').unwrap()
    );
    assert_eq!(
        arguments.range.end.get() as usize,
        source.find('>').unwrap() + 1
    );
    let NodeData::TypeLiteralNode(literal) = &parsed.arena.get(arguments.nodes[0]).unwrap().data
    else {
        panic!("expected the recovered object type");
    };
    assert_eq!(literal.members.nodes.len(), 1);
    let NodeData::PropertyDeclaration(property) =
        &parsed.arena.get(literal.members.nodes[0]).unwrap().data
    else {
        panic!("expected the written property");
    };
    assert_eq!(node_text(&parsed, property.name), "value");
    let missing = property.type_.unwrap();
    assert_eq!(
        parsed.arena.get(missing).unwrap().range.start.get(),
        error_start
    );
    assert_eq!(
        parsed.arena.get(missing).unwrap().range.end.get(),
        error_start
    );
    assert_eq!(
        node_text(&parsed, reference(&parsed, missing).type_name),
        ""
    );
    assert_eq!(call.arguments.nodes.len(), 1);
    assert_eq!(node_text(&parsed, call.arguments.nodes[0]), "item");
    assert_eq!(
        node_text(&parsed, initializer(&parsed, statements[1], "after")),
        "1"
    );
}

fn sole_call_type_argument(
    parsed: &ParseResult,
    statement: NodeId,
    name: &str,
    expected_type: &str,
) -> NodeId {
    let call_id = initializer(parsed, statement, name);
    let NodeData::CallExpression(call) = &parsed.arena.get(call_id).unwrap().data else {
        panic!("expected a generic call for {name}");
    };
    assert_eq!(
        node_text(parsed, call_id),
        format!("read<{expected_type}>(value)")
    );
    assert_eq!(node_text(parsed, call.expression), "read");
    assert_eq!(
        parsed.arena.get(call.expression).unwrap().kind,
        SyntaxKind::Identifier
    );
    assert_eq!(call.arguments.nodes.len(), 1);
    assert_eq!(node_text(parsed, call.arguments.nodes[0]), "value");
    assert_eq!(
        parsed.arena.get(call.arguments.nodes[0]).unwrap().kind,
        SyntaxKind::Identifier
    );
    let arguments = call.type_arguments.as_ref().unwrap();
    assert_eq!(arguments.nodes.len(), 1);
    assert!(!arguments.has_trailing_comma);
    assert_eq!(text(parsed, arguments.range), format!("<{expected_type}>"));
    assert_eq!(node_text(parsed, arguments.nodes[0]), expected_type);
    arguments.nodes[0]
}

fn assert_nested_generic_function_type(parsed: &ParseResult, id: NodeId) {
    let outer = reference(parsed, id);
    assert_eq!(node_text(parsed, outer.type_name), "Outer");
    let arguments = outer.type_arguments.as_ref().unwrap();
    assert_eq!(arguments.nodes.len(), 1);
    assert_eq!(text(parsed, arguments.range), "<<T>(x: T) => T>");
    let function_id = arguments.nodes[0];
    assert_eq!(node_text(parsed, function_id), "<T>(x: T) => T");
    let NodeData::FunctionTypeNode(function) = &parsed.arena.get(function_id).unwrap().data else {
        panic!("expected the nested generic function type");
    };
    let type_parameters = function.type_parameters.as_ref().unwrap();
    assert_eq!(type_parameters.nodes.len(), 1);
    assert_eq!(text(parsed, type_parameters.range), "<T>");
    let type_parameter_id = type_parameters.nodes[0];
    let NodeData::TypeParameterDeclaration(type_parameter) =
        &parsed.arena.get(type_parameter_id).unwrap().data
    else {
        panic!("expected the function's type parameter");
    };
    assert_eq!(node_text(parsed, type_parameter_id), "T");
    assert_eq!(node_text(parsed, type_parameter.name), "T");
    assert_eq!(
        parsed.arena.get(type_parameter.name).unwrap().kind,
        SyntaxKind::Identifier
    );
    assert!(type_parameter.constraint.is_none());
    assert!(type_parameter.default_type.is_none());
    assert_eq!(function.parameters.nodes.len(), 1);
    assert_eq!(text(parsed, function.parameters.range), "(x: T)");
    let parameter_id = function.parameters.nodes[0];
    assert_eq!(node_text(parsed, parameter_id), "x: T");
    let NodeData::ParameterDeclaration(parameter) = &parsed.arena.get(parameter_id).unwrap().data
    else {
        panic!("expected the function's value parameter");
    };
    assert_eq!(node_text(parsed, parameter.name), "x");
    assert!(parameter.initializer.is_none());
    assert!(parameter.dot_dot_dot_token.is_none());
    assert!(parameter.question_token.is_none());
    let parameter_type = parameter.type_.unwrap();
    let return_type = function.type_.unwrap();
    assert_ne!(parameter_type, return_type);
    for type_id in [parameter_type, return_type] {
        assert_eq!(node_text(parsed, type_id), "T");
        let type_ = reference(parsed, type_id);
        assert_eq!(node_text(parsed, type_.type_name), "T");
        assert!(type_.type_arguments.is_none());
    }
}

#[test]
fn nested_generic_function_arguments_keep_computed_and_following_value_shifts() {
    let source = concat!(
        "const generic = read<Outer<<T>(x: T) => T>>(value);\n",
        "const member = read<{ value: Outer<<T>(x: T) => T> }>(value);\n",
        "const computed = read<{ [key << amount]: number }>(value);\n",
        "const shifted = left << right;\n",
        "const compared = left < right;\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_complete_tree(&parsed, source);
    let statements = statements(&parsed);
    assert_eq!(statements.len(), 5);
    let generic =
        sole_call_type_argument(&parsed, statements[0], "generic", "Outer<<T>(x: T) => T>");
    assert_nested_generic_function_type(&parsed, generic);
    let member = sole_call_type_argument(
        &parsed,
        statements[1],
        "member",
        "{ value: Outer<<T>(x: T) => T> }",
    );
    let NodeData::TypeLiteralNode(literal) = &parsed.arena.get(member).unwrap().data else {
        panic!("expected the object containing the nested generic function");
    };
    assert_eq!(literal.members.nodes.len(), 1);
    let NodeData::PropertyDeclaration(property) =
        &parsed.arena.get(literal.members.nodes[0]).unwrap().data
    else {
        panic!("expected the written value property");
    };
    assert_eq!(node_text(&parsed, property.name), "value");
    assert_eq!(
        node_text(&parsed, property.type_.unwrap()),
        "Outer<<T>(x: T) => T>"
    );
    assert_nested_generic_function_type(&parsed, property.type_.unwrap());
    let computed = sole_call_type_argument(
        &parsed,
        statements[2],
        "computed",
        "{ [key << amount]: number }",
    );
    let NodeData::TypeLiteralNode(literal) = &parsed.arena.get(computed).unwrap().data else {
        panic!("expected an object type argument");
    };
    assert_eq!(literal.members.nodes.len(), 1);
    let property_id = literal.members.nodes[0];
    assert_eq!(node_text(&parsed, property_id), "[key << amount]: number");
    let NodeData::PropertyDeclaration(property) = &parsed.arena.get(property_id).unwrap().data
    else {
        panic!("expected the computed property");
    };
    assert_eq!(node_text(&parsed, property.name), "[key << amount]");
    let NodeData::ComputedPropertyName(name) = &parsed.arena.get(property.name).unwrap().data
    else {
        panic!("expected a computed property name, not an index signature");
    };
    let shift = binary(&parsed, name.expression, SyntaxKind::LessThanLessThanToken);
    assert_eq!(node_text(&parsed, shift.operator_token), "<<");
    assert_eq!(node_text(&parsed, shift.left), "key");
    assert_eq!(node_text(&parsed, shift.right), "amount");
    assert_eq!(node_text(&parsed, property.type_.unwrap()), "number");
    assert_eq!(
        parsed.arena.get(property.type_.unwrap()).unwrap().kind,
        SyntaxKind::NumberKeyword
    );
    for (statement, name, operator, token) in [
        (
            statements[3],
            "shifted",
            SyntaxKind::LessThanLessThanToken,
            "<<",
        ),
        (statements[4], "compared", SyntaxKind::LessThanToken, "<"),
    ] {
        let expression = initializer(&parsed, statement, name);
        let value = binary(&parsed, expression, operator);
        assert_eq!(node_text(&parsed, value.operator_token), token);
        assert_eq!(node_text(&parsed, value.left), "left");
        assert_eq!(node_text(&parsed, value.right), "right");
    }
}
