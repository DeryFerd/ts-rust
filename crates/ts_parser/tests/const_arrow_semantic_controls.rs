use ts_ast::{NodeData, NodeId, SyntaxKind};
use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};

fn initializer(parsed: &ParseResult, name: &str) -> NodeId {
    parsed
        .arena
        .iter()
        .find_map(|(_, node)| {
            let NodeData::VariableDeclaration(variable) = &node.data else {
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
fn reserved_const_type_parameter_names_keep_syntax_errors() {
    for name in ["return", "class", "if", "function"] {
        let source = format!("const fn = <const {name},>(value: any) => value; const after = 1;");
        for parsed in [parse_source_file(&source), parse_jsx_source_file(&source)] {
            assert!(!parsed.diagnostics.is_empty(), "{source}");
        }
    }
    let source = "const fn = <const out,>(value: out) => value; const after = 1;";
    for parsed in [parse_source_file(source), parse_jsx_source_file(source)] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        assert_eq!(
            parsed.arena.get(initializer(&parsed, "fn")).unwrap().kind,
            SyntaxKind::ArrowFunction
        );
    }
}

#[test]
fn async_tsx_missing_arrow_keeps_the_next_declaration_top_level() {
    let source = "const fn = async <const T,>(value: T)\nconst after = 1;";
    let parsed = parse_jsx_source_file(source);
    let NodeData::SourceFile(root) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected source file");
    };
    assert_eq!(root.statements.nodes.len(), 2);
    let arrow = parsed.arena.get(initializer(&parsed, "fn")).unwrap();
    assert_eq!(arrow.kind, SyntaxKind::ArrowFunction);
    assert!(arrow.range.end.get() as usize <= source.find("const after").unwrap());
    assert_eq!(parsed.diagnostics.len(), 1);
    let diagnostic = &parsed.diagnostics[0];
    assert_eq!(
        (
            diagnostic.code,
            diagnostic.range.start.get(),
            diagnostic.range.end.get()
        ),
        (Some(1005), 38, 43)
    );
}

#[test]
fn missing_arrow_retains_an_identifier_body() {
    let source = "const fn = <const T,>(value: T) value; const after = 1;";
    let parsed = parse_jsx_source_file(source);
    let NodeData::ArrowFunction(arrow) =
        &parsed.arena.get(initializer(&parsed, "fn")).unwrap().data
    else {
        panic!("expected recovered arrow");
    };
    let NodeData::Identifier(body) = &parsed.arena.get(arrow.body).unwrap().data else {
        panic!("expected identifier body");
    };
    assert_eq!(body.text, "value");
    let NodeData::SourceFile(root) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected source file");
    };
    assert_eq!(root.statements.nodes.len(), 2);
}

#[test]
fn a_function_return_type_does_not_supply_the_outer_arrow_token() {
    let source = "const fn = <const T,>(value: T): () => T; const after = 1;";
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
fn reserved_type_parameter_names_keep_their_diagnostic_ranges() {
    for name in ["return", "class", "if", "function"] {
        let source = format!("const fn = <const {name},>(value: any) => value; const after = 1;");
        let start = u32::try_from(source.find(name).unwrap()).unwrap();
        let end = start + u32::try_from(name.len()).unwrap();
        let standard = parse_source_file(&source);
        assert_eq!(
            standard
                .arena
                .get(initializer(&standard, "fn"))
                .unwrap()
                .kind,
            SyntaxKind::TypeAssertionExpression,
            "{source}"
        );
        let diagnostic = &standard.diagnostics[0];
        assert_eq!(
            (
                diagnostic.code,
                diagnostic.range.start.get(),
                diagnostic.range.end.get()
            ),
            (Some(1005), start, end),
            "{source}"
        );
        let jsx = parse_jsx_source_file(&source);
        let diagnostic = &jsx.diagnostics[0];
        assert_eq!(
            (
                diagnostic.code,
                diagnostic.range.start.get(),
                diagnostic.range.end.get()
            ),
            (Some(1359), start, end),
            "{source}"
        );
    }
}

#[test]
fn contextual_type_parameter_names_use_the_enclosing_context() {
    for prefix in ["", "async "] {
        for name in [
            "out",
            "as",
            "async",
            "await",
            "yield",
            "implements",
            "interface",
            "let",
            "private",
        ] {
            let source = format!("const fn = {prefix}<const {name},>(value: any) => value;");
            for parsed in [parse_source_file(&source), parse_jsx_source_file(&source)] {
                assert!(
                    parsed.diagnostics.is_empty(),
                    "{source}: {:?}",
                    parsed.diagnostics
                );
                assert_eq!(
                    parsed.arena.get(initializer(&parsed, "fn")).unwrap().kind,
                    SyntaxKind::ArrowFunction,
                    "{source}"
                );
            }
        }
    }
    for source in [
        "async function f<await>(value: any) {}",
        "function* f<yield>(value: any) {}",
        "const fn = async function<await>(value: any) {};",
        "const fn = function*<yield>(value: any) {};",
        "const value = { async method<await>(value: any) {}, *generator<yield>(value: any) {} };",
        "class Value { async method<await>(value: any) {} *generator<yield>(value: any) {} }",
    ] {
        let parsed = parse_source_file(source);
        assert!(
            parsed.diagnostics.is_empty(),
            "{source}: {:?}",
            parsed.diagnostics
        );
    }
    for source in [
        "async function outer() { const fn = <const await,>(value: any) => value; }",
        "function* outer() { const fn = <const yield,>(value: any) => value; }",
    ] {
        for parsed in [parse_source_file(source), parse_jsx_source_file(source)] {
            assert!(!parsed.diagnostics.is_empty(), "{source}");
        }
    }
}
