use ts_ast::{NodeData, NodeId, SyntaxKind};
use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};

fn initializer(parsed: &ParseResult, name: &str) -> NodeId {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (identifier.text == name).then_some(variable.initializer?)
        })
        .unwrap()
}

#[test]
fn const_type_parameters_are_preserved_on_generic_arrows() {
    for (source, expected_constants) in [
        ("const fn = <const T>(value: T) => value;", 1),
        (
            "const fn = <Input, const T extends string>(value: T) => value;",
            1,
        ),
        (
            "const fn = <const T extends string = 'default', const U = T>(value: U) => value;",
            2,
        ),
        (
            "const fn = async <const T extends string>(value: T) => value;",
            1,
        ),
    ] {
        let parsed = parse_source_file(source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
        let node = initializer(&parsed, "fn");
        let NodeData::ArrowFunction(arrow) = &parsed.arena.get(node).unwrap().data else {
            panic!("{source}: expected an arrow");
        };
        let arrow_token = parsed.arena.get(arrow.equals_greater_than_token).unwrap();
        assert_eq!(arrow_token.parent, Some(node));
        assert_eq!(
            &source[arrow_token.range.start.get() as usize..arrow_token.range.end.get() as usize],
            "=>"
        );
        let parameters = arrow.type_parameters.as_ref().unwrap();
        assert!(!parameters.nodes.is_empty());
        let mut constants = 0;
        for &parameter in &parameters.nodes {
            let record = parsed.arena.get(parameter).unwrap();
            assert_eq!(record.parent, Some(node));
            let NodeData::TypeParameterDeclaration(data) = &record.data else {
                unreachable!()
            };
            for &modifier in data
                .modifiers
                .iter()
                .flat_map(|modifiers| &modifiers.list.nodes)
            {
                let modifier = parsed.arena.get(modifier).unwrap();
                assert_eq!(modifier.kind, SyntaxKind::ConstKeyword);
                assert_eq!(modifier.parent, Some(parameter));
                assert_eq!(
                    &source[modifier.range.start.get() as usize..modifier.range.end.get() as usize],
                    "const"
                );
                constants += 1;
            }
        }
        assert_eq!(constants, expected_constants);
    }
}

#[test]
fn generic_arrow_lookahead_preserves_template_type_boundaries() {
    for source in [
        "const fn = <Input, const T extends string>(value: T): Box<Input, `${T}${string}`> => value;",
        "const fn = <const T extends `${string}-${number}` = `x-${1}`>(value: T) => value;",
        "const fn = <const T extends string>(value: T): Box<`outer-${`inner-${T}`}-${string}`> => value;",
        "const fn = <const T>(value: `prefix-${{ value: T }['value']}`) => value;",
        "const fn = async <const T extends string>(value: T): Box<`${T}${string}`> => value;",
        "const fn = <const T extends `${string})>;`>(value: T) => value;",
        "const fn = async <const T extends `outer-${`inner-${string}`}`>(value: T) => value;",
        "const fn = async <const T>(value: `prefix-${{ value: T }['value']}`) => value;",
        "const fn = async <const T>(value: T): Promise<{ value: `${T & string}`; }> => value;",
    ] {
        let parsed = parse_source_file(source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
        assert_eq!(
            parsed.arena.get(initializer(&parsed, "fn")).unwrap().kind,
            SyntaxKind::ArrowFunction
        );
    }
}

#[test]
fn const_generic_arrows_keep_jsx_disambiguation() {
    for source in [
        "const fn = <const T,>(value: T) => value;",
        "const fn = <const T extends unknown>(value: T) => value;",
        "const fn = <const T = unknown>(value: T) => value;",
        "const fn = async <const T,>(value: T) => value;",
    ] {
        let parsed = parse_jsx_source_file(source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
        assert_eq!(
            parsed.arena.get(initializer(&parsed, "fn")).unwrap().kind,
            SyntaxKind::ArrowFunction
        );
    }
    for source in [
        "const view = <const />;",
        "const view = <const T />;",
        "const view = <const T extends />;",
        "const view = <const T extends='x' />;",
    ] {
        let parsed = parse_jsx_source_file(source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
        assert_eq!(
            parsed.arena.get(initializer(&parsed, "view")).unwrap().kind,
            SyntaxKind::JsxSelfClosingElement
        );
    }

    let source = "const view = <const T extends></const>;";
    let parsed = parse_jsx_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_eq!(
        parsed.arena.get(initializer(&parsed, "view")).unwrap().kind,
        SyntaxKind::JsxElement
    );
}

#[test]
fn ambiguous_const_generic_arrows_remain_jsx() {
    let parsed = parse_jsx_source_file("const fn = <const T>(value: T) => value;");
    assert_eq!(
        parsed.arena.get(initializer(&parsed, "fn")).unwrap().kind,
        SyntaxKind::JsxElement
    );
    let mut diagnostics = parsed
        .diagnostics
        .iter()
        .map(|diagnostic| {
            (
                diagnostic.code,
                diagnostic.range.start.get(),
                diagnostic.range.end.get(),
            )
        })
        .collect::<Vec<_>>();
    diagnostics.sort_unstable();
    assert_eq!(
        diagnostics,
        [
            (Some(1005), 40, 40),
            (Some(1382), 32, 33),
            (Some(17008), 12, 17)
        ]
    );
}

#[test]
fn const_generic_arrow_recovers_a_missing_arrow_token() {
    let source = "const fn = <const T>(value: T) { return value; }; const after = 1;";
    let parsed = parse_source_file(source);
    assert_eq!(parsed.diagnostics.len(), 1, "{:?}", parsed.diagnostics);
    let diagnostic = &parsed.diagnostics[0];
    assert_eq!(
        (
            diagnostic.code,
            diagnostic.range.start.get(),
            diagnostic.range.end.get()
        ),
        (Some(1005), 31, 32)
    );
    let NodeData::ArrowFunction(arrow) =
        &parsed.arena.get(initializer(&parsed, "fn")).unwrap().data
    else {
        panic!("expected recovered arrow");
    };
    assert_eq!(
        parsed.arena.get(arrow.body).unwrap().kind,
        SyntaxKind::Block
    );
    assert_eq!(
        parsed
            .arena
            .get(initializer(&parsed, "after"))
            .unwrap()
            .kind,
        SyntaxKind::NumericLiteral
    );
}

#[test]
fn malformed_const_generic_arrows_keep_diagnostic_ranges_and_later_declarations() {
    // The TSX prefix selects an arrow before error recovery starts.
    for (source, expected) in [
        (
            "const fn = <const T,>(value: T => value; const after = 1;",
            (Some(1005), 31, 33),
        ),
        (
            "const fn = <const T,>(value: T): => value; const after = 1;",
            (Some(1110), 33, 35),
        ),
        (
            "const fn = <const T,>(value: T) { return value; }; const after = 1;",
            (Some(1005), 32, 33),
        ),
        (
            "const fn = <const T,>(value: T) => ; const after = 1;",
            (Some(1109), 35, 36),
        ),
        (
            "const fn = <const T,>(value: T)\nconst after = 1;",
            (Some(1005), 32, 37),
        ),
        (
            "const fn = <const T,>(value: T): T { return value; }; const after = 1;",
            (Some(1005), 35, 36),
        ),
        (
            "const fn = async <const T,>(value: T): T { return value; }; const after = 1;",
            (Some(1005), 41, 42),
        ),
    ] {
        let parsed = parse_jsx_source_file(source);
        assert_eq!(
            parsed
                .diagnostics
                .iter()
                .map(|diagnostic| {
                    (
                        diagnostic.code,
                        diagnostic.range.start.get(),
                        diagnostic.range.end.get(),
                    )
                })
                .collect::<Vec<_>>(),
            [expected],
            "{source}"
        );
        let node = parsed.arena.get(initializer(&parsed, "fn")).unwrap();
        assert_eq!(node.kind, SyntaxKind::ArrowFunction, "{source}");
        assert!(
            node.range.end.get() <= u32::try_from(source.find("const after").unwrap()).unwrap()
        );
        assert_eq!(
            parsed
                .arena
                .get(initializer(&parsed, "after"))
                .unwrap()
                .kind,
            SyntaxKind::NumericLiteral,
            "{source}"
        );
    }
}

#[test]
fn const_generic_arrow_with_a_missing_return_type_remains_a_type_assertion() {
    let source = "const fn = <const T,>(value: T): => value; const after = 1;";
    let parsed = parse_source_file(source);
    assert!(!parsed.diagnostics.is_empty());
    assert_eq!(
        parsed.arena.get(initializer(&parsed, "fn")).unwrap().kind,
        SyntaxKind::TypeAssertionExpression
    );
    assert_eq!(
        parsed
            .arena
            .get(initializer(&parsed, "after"))
            .unwrap()
            .kind,
        SyntaxKind::NumericLiteral
    );
}

#[test]
fn generic_arrow_lookahead_keeps_type_assertions_and_async_line_breaks() {
    let parsed = parse_source_file(concat!(
        "const cast = <const>(value);\n",
        "const fn = async <out>(value) => value;\n",
        "const generic = <T>(value: T) => value;\n",
    ));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    for (name, kind) in [
        ("cast", SyntaxKind::TypeAssertionExpression),
        ("fn", SyntaxKind::ArrowFunction),
        ("generic", SyntaxKind::ArrowFunction),
    ] {
        assert_eq!(
            parsed.arena.get(initializer(&parsed, name)).unwrap().kind,
            kind
        );
    }

    for parsed in [
        parse_source_file("const fn = async\n<const T,>(value: T) => value;"),
        parse_jsx_source_file("const fn = async <const T>(value: T) => value;"),
    ] {
        assert!(!parsed.diagnostics.is_empty());
        assert_ne!(
            parsed.arena.get(initializer(&parsed, "fn")).unwrap().kind,
            SyntaxKind::ArrowFunction
        );
    }
}

#[test]
fn generic_arrow_lookahead_rewinds_comment_directives() {
    let source = concat!(
        "const fn = <\n",
        "// @ts-expect-error parameter\n",
        "const T extends `x-${string}// @ts-ignore template text`\n",
        ">(value: T): `${T}/* @ts-ignore template text */` => value;\n",
        "const cast = <const /* @ts-ignore assertion */>(value);\n",
        "// @ts-ignore after\n",
        "const after = 1;\n",
    );
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    assert_eq!(
        parsed
            .comment_directives
            .iter()
            .map(|directive| {
                (
                    &source
                        [directive.range.start.get() as usize..directive.range.end.get() as usize],
                    directive.expect_error,
                )
            })
            .collect::<Vec<_>>(),
        [
            ("// @ts-expect-error parameter", true),
            ("/* @ts-ignore assertion */", false),
            ("// @ts-ignore after", false),
        ]
    );
}
