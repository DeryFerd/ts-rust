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

fn assert_after_is_outside_arrow(parsed: &ParseResult, source: &str, arrow: NodeId) {
    let NodeData::SourceFile(root) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        unreachable!()
    };
    assert_eq!(root.statements.nodes.len(), 2);
    assert!(
        parsed.arena.get(arrow).unwrap().range.end.get()
            <= u32::try_from(source.find("const after").unwrap()).unwrap()
    );
    assert_eq!(
        parsed.arena.get(initializer(parsed, "after")).unwrap().kind,
        SyntaxKind::NumericLiteral
    );
}

#[test]
fn typed_const_generic_arrows_recover_a_missing_arrow_outside_tsx() {
    for (source, start, end) in [
        (
            "const fn = <const T,>(value: T): T { return value; }; const after = 1;",
            35,
            36,
        ),
        (
            "const fn = async <const T,>(value: T): T { return value; }; const after = 1;",
            41,
            42,
        ),
    ] {
        let parsed = parse_source_file(source);
        assert_eq!(
            parsed
                .diagnostics
                .iter()
                .map(|diagnostic| (
                    diagnostic.code,
                    diagnostic.range.start.get(),
                    diagnostic.range.end.get(),
                ))
                .collect::<Vec<_>>(),
            [(Some(1005), start, end)],
            "{source}"
        );
        let arrow = initializer(&parsed, "fn");
        let NodeData::ArrowFunction(data) = &parsed.arena.get(arrow).unwrap().data else {
            panic!("expected a recovered arrow: {source}")
        };
        assert_eq!(parsed.arena.get(data.body).unwrap().kind, SyntaxKind::Block);
        assert_after_is_outside_arrow(&parsed, source, arrow);
    }
}

#[test]
fn async_const_generic_arrow_recovery_keeps_the_next_declaration_outside_its_body() {
    let source = "const fn = async <const T,>(value: T)\nconst after = 1;";
    let parsed = parse_jsx_source_file(source);
    let start = u32::try_from(source.find("const after").unwrap()).unwrap();
    assert_eq!(
        parsed
            .diagnostics
            .iter()
            .map(|diagnostic| (
                diagnostic.code,
                diagnostic.range.start.get(),
                diagnostic.range.end.get(),
            ))
            .collect::<Vec<_>>(),
        [(Some(1005), start, start + 5)]
    );
    let arrow = initializer(&parsed, "fn");
    let NodeData::ArrowFunction(data) = &parsed.arena.get(arrow).unwrap().data else {
        panic!("expected a recovered async arrow")
    };
    let body = parsed.arena.get(data.body).unwrap();
    assert_eq!(body.kind, SyntaxKind::Identifier);
    assert_eq!(body.range.start, body.range.end);
    assert_after_is_outside_arrow(&parsed, source, arrow);
}

#[test]
fn object_and_function_return_types_keep_the_outer_arrow_boundary() {
    for prefix in ["", "async "] {
        for (return_type, body) in [
            ("{ value: T }", "({ value })"),
            ("T | { value: T }", "value"),
            ("T & { value: T }", "value"),
            ("keyof { value: T }", "'value'"),
            (
                "T extends { value: unknown } ? { value: T } : { other: T }",
                "value",
            ),
            ("() => { value: T }", "() => ({ value })"),
            ("{ [P in keyof T]: T[P] }", "value"),
            ("value is { value: T }", "true"),
        ] {
            let source = format!(
                "const fn = {prefix}<const T,>(value: T): {return_type} => {body}; const after = 1;"
            );
            let parsed = parse_source_file(&source);
            assert!(
                parsed.diagnostics.is_empty(),
                "{source}: {:?}",
                parsed.diagnostics
            );
            let arrow = initializer(&parsed, "fn");
            let NodeData::ArrowFunction(data) = &parsed.arena.get(arrow).unwrap().data else {
                panic!("expected an arrow: {source}");
            };
            let range = parsed.arena.get(data.type_.unwrap()).unwrap().range;
            assert_eq!(
                &source[range.start.get() as usize..range.end.get() as usize],
                return_type
            );
            assert_after_is_outside_arrow(&parsed, &source, arrow);
        }
    }
}

#[test]
fn compound_return_annotations_recover_the_following_body_brace() {
    for prefix in ["", "async "] {
        for return_type in [
            "{ value: T }",
            "T | { value: T }",
            "T & { value: T }",
            "keyof { value: T }",
            "T extends { value: unknown } ? { value: T } : { other: T }",
            "() => { value: T }",
            "`value-${T & string}`",
        ] {
            let source = format!(
                "const fn = {prefix}<const T,>(value: T): {return_type} {{ return value; }}; const after = 1;"
            );
            let parsed = parse_source_file(&source);
            let start = u32::try_from(source.find("{ return value; }").unwrap()).unwrap();
            assert_eq!(
                parsed
                    .diagnostics
                    .iter()
                    .map(|diagnostic| (
                        diagnostic.code,
                        diagnostic.range.start.get(),
                        diagnostic.range.end.get()
                    ))
                    .collect::<Vec<_>>(),
                [(Some(1005), start, start + 1)],
                "{source}"
            );
            let arrow = initializer(&parsed, "fn");
            let NodeData::ArrowFunction(data) = &parsed.arena.get(arrow).unwrap().data else {
                panic!("expected a recovered arrow: {source}");
            };
            assert_eq!(parsed.arena.get(data.body).unwrap().kind, SyntaxKind::Block);
            let range = parsed.arena.get(data.type_.unwrap()).unwrap().range;
            assert_eq!(
                &source[range.start.get() as usize..range.end.get() as usize],
                return_type
            );
            assert_after_is_outside_arrow(&parsed, &source, arrow);
        }
    }
}

#[test]
fn nonblocking_return_type_errors_keep_outer_arrow_recovery() {
    for (return_type, token) in [("T |", "=>"), ("{ value: }", "}")] {
        let source =
            format!("const fn = <const T,>(value: T): {return_type} => value; const after = 1;");
        let parsed = parse_source_file(&source);
        let start = u32::try_from(source.find(token).unwrap()).unwrap();
        let end = start + u32::try_from(token.len()).unwrap();
        assert_eq!(
            parsed
                .diagnostics
                .iter()
                .map(|diagnostic| (
                    diagnostic.code,
                    diagnostic.range.start.get(),
                    diagnostic.range.end.get()
                ))
                .collect::<Vec<_>>(),
            [(Some(1110), start, end)],
            "{source}"
        );
        let arrow = initializer(&parsed, "fn");
        assert_eq!(
            parsed.arena.get(arrow).unwrap().kind,
            SyntaxKind::ArrowFunction
        );
        assert_after_is_outside_arrow(&parsed, &source, arrow);
    }
}
