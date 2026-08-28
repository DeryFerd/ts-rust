use ts_ast::{NodeData, NodeId, SyntaxKind};
use ts_parser::{
    ParseResult, parse_javascript_source_file, parse_jsx_source_file, parse_source_file,
};

const CALLS: &str = "Foo<number>();\nFoo<number>(1);\nFoo<number>``;\n";
const ORIGINAL: &str = concat!(
    "Foo<number>();\n",
    "Foo<number>(1);\n",
    "Foo<number>``;\n",
    "<Foo<number>></Foo>;\n",
    "<Foo<number>/>;\n",
);

fn expressions(parsed: &ParseResult) -> Vec<NodeId> {
    let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected a source file")
    };
    source
        .statements
        .nodes
        .iter()
        .map(|statement| {
            let NodeData::ExpressionStatement(statement) =
                &parsed.arena.get(*statement).unwrap().data
            else {
                panic!("expected an expression statement")
            };
            statement.expression
        })
        .collect()
}

#[test]
fn javascript_type_arguments_remain_relational_expressions() {
    let parsed = parse_javascript_source_file(CALLS);
    assert_eq!(parsed.diagnostics.len(), 1, "{:?}", parsed.diagnostics);
    assert_eq!(parsed.diagnostics[0].code, Some(1109));
    assert_eq!(parsed.diagnostics[0].range.start.get(), 12);
    for expression in expressions(&parsed) {
        let NodeData::BinaryExpression(greater) = &parsed.arena.get(expression).unwrap().data
        else {
            panic!("JavaScript must retain the greater-than expression")
        };
        assert_eq!(
            parsed.arena.get(greater.operator_token).unwrap().kind,
            SyntaxKind::GreaterThanToken
        );
        let NodeData::BinaryExpression(less) = &parsed.arena.get(greater.left).unwrap().data else {
            panic!("JavaScript must retain the less-than expression")
        };
        assert_eq!(
            parsed.arena.get(less.operator_token).unwrap().kind,
            SyntaxKind::LessThanToken
        );
    }
}

#[test]
fn typescript_and_tsx_keep_expression_and_element_type_arguments() {
    for parsed in [parse_source_file(CALLS), parse_jsx_source_file(ORIGINAL)] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let expressions = expressions(&parsed);
        for expression in &expressions[..2] {
            let NodeData::CallExpression(call) = &parsed.arena.get(*expression).unwrap().data
            else {
                panic!("TypeScript must keep its generic calls")
            };
            assert_eq!(call.type_arguments.as_ref().unwrap().nodes.len(), 1);
        }
        let NodeData::TaggedTemplateExpression(tagged) =
            &parsed.arena.get(expressions[2]).unwrap().data
        else {
            panic!("TypeScript must keep its generic tagged template")
        };
        assert_eq!(tagged.type_arguments.as_ref().unwrap().nodes.len(), 1);
        if expressions.len() == 5 {
            let NodeData::JsxElement(element) = &parsed.arena.get(expressions[3]).unwrap().data
            else {
                panic!("TSX must retain the generic element")
            };
            let NodeData::JsxOpeningElement(opening) =
                &parsed.arena.get(element.opening_element).unwrap().data
            else {
                panic!("expected an opening element")
            };
            assert_eq!(opening.type_arguments.as_ref().unwrap().nodes.len(), 1);
            let NodeData::JsxSelfClosingElement(element) =
                &parsed.arena.get(expressions[4]).unwrap().data
            else {
                panic!("TSX must retain the generic self-closing element")
            };
            assert_eq!(element.type_arguments.as_ref().unwrap().nodes.len(), 1);
        }
    }
}

#[test]
fn original_javascript_jsx_recovery_keeps_all_pinned_error_spans() {
    let parsed = parse_javascript_source_file(ORIGINAL);
    let mut diagnostics = parsed
        .diagnostics
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.range.start.get(),
                diagnostic.range.end.get() - diagnostic.range.start.get(),
                diagnostic.code.unwrap(),
            )
        })
        .collect::<Vec<_>>();
    diagnostics.sort_unstable();
    assert_eq!(
        diagnostics,
        [
            (12, 1, 1109),
            (46, 19, 2657),
            (50, 1, 1003),
            (58, 1, 1382),
            (61, 3, 17002),
            (67, 16, 2657),
            (71, 1, 1003),
            (72, 6, 17008),
            (80, 1, 1382),
            (83, 0, 1005),
        ],
        "{:?}",
        parsed.diagnostics
    );
    assert_eq!(expressions(&parsed).len(), 5);
}

#[test]
fn valid_jsx_and_unary_contexts_keep_their_existing_parse() {
    for source in [
        "const view = <Foo value={Foo(1)} />;",
        "const view = <Foo><Bar /></Foo>;",
        "const value = !<Foo />;",
    ] {
        for parsed in [
            parse_javascript_source_file(source),
            parse_jsx_source_file(source),
        ] {
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}\n{:?}",
                parsed.diagnostics
            );
        }
    }
}

#[test]
fn javascript_signature_semicolons_and_asi_keep_their_ranges() {
    for (source, typescript, javascript) in [
        (
            "function F(); class C { method(); }",
            ["function F()", "method()"],
            ["function F();", "method();"],
        ),
        (
            "function F()\nclass C { method()\n}",
            ["function F()", "method()"],
            ["function F()", "method()"],
        ),
    ] {
        let ranges = |parsed: &ParseResult| {
            assert!(parsed.diagnostics.is_empty());
            parsed
                .arena
                .iter()
                .filter(|(_, node)| {
                    matches!(
                        node.data,
                        NodeData::FunctionDeclaration(_) | NodeData::MethodDeclaration(_)
                    )
                })
                .map(|(_, node)| {
                    &source[node.range.start.get() as usize..node.range.end.get() as usize]
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(ranges(&parse_source_file(source)), typescript);
        assert_eq!(ranges(&parse_javascript_source_file(source)), javascript);
    }
}
