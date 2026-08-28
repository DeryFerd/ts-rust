use ts_ast::{NodeData, NodeId, SyntaxKind, TypeAliasDeclarationData};
use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};

#[test]
fn parses_exported_infer_type_alias() {
    // Unchanged declaration from ts-pattern src/patterns.ts:116.
    let source = "export type infer<pattern> = InvertPattern<NoInfer<pattern>, unknown>;";
    for parse in [parse_source_file, parse_jsx_source_file] {
        let result = parse(source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1);
        let alias = type_alias(&result, statements[0]);
        assert_eq!(identifier_text(&result, alias.name), "infer");
        let name = result.arena.get(alias.name).unwrap();
        assert_eq!(name.parent, Some(statements[0]));
        assert_eq!((name.range.start.get(), name.range.end.get()), (12, 17));
        assert!(alias.modifiers.is_some());
        let parameters = alias.type_parameters.as_ref().unwrap();
        assert_eq!(parameters.nodes.len(), 1);
        let NodeData::TypeParameterDeclaration(parameter) =
            &result.arena.get(parameters.nodes[0]).unwrap().data
        else {
            panic!("expected type parameter");
        };
        assert_eq!(identifier_text(&result, parameter.name), "pattern");
        let NodeData::TypeReferenceNode(body) = &result.arena.get(alias.type_).unwrap().data else {
            panic!("expected type reference");
        };
        assert_eq!(identifier_text(&result, body.type_name), "InvertPattern");
        assert_eq!(body.type_arguments.as_ref().unwrap().nodes.len(), 2);
        assert!(
            result
                .arena
                .iter()
                .all(|(_, node)| node.kind != SyntaxKind::InferType)
        );
    }
}

#[test]
fn accepts_contextual_type_alias_names() {
    for name in [
        "infer",
        "keyof",
        "readonly",
        "type",
        "as",
        "satisfies",
        "asserts",
        "unknown",
        "implements",
        "interface",
        "require",
    ] {
        let source = format!("type {name}<T> = T;");
        let result = parse_source_file(&source);
        assert!(
            result.diagnostics.is_empty(),
            "{source}: {:?}",
            result.diagnostics
        );
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1, "{source}");
        assert_eq!(
            identifier_text(&result, type_alias(&result, statements[0]).name),
            name
        );
    }
}

#[test]
fn decodes_escaped_contextual_type_alias_names() {
    for (spelling, expected) in [
        (r"\u0069nfer", "infer"),
        (r"\u{69}nfer", "infer"),
        (r"in\u0066er", "infer"),
        (r"key\u006ff", "keyof"),
        (r"Al\u0069as", "Alias"),
    ] {
        let source = format!("type {spelling} = string;");
        let result = parse_source_file(&source);
        assert!(
            result.diagnostics.is_empty(),
            "{source}: {:?}",
            result.diagnostics
        );
        let statements = source_statements(&result);
        assert_eq!(statements.len(), 1, "{source}");
        let alias = type_alias(&result, statements[0]);
        assert_eq!(identifier_text(&result, alias.name), expected);
        let range = result.arena.get(alias.name).unwrap().range;
        assert_eq!(
            &source[range.start.get() as usize..range.end.get() as usize],
            spelling
        );
    }
}

#[test]
fn keeps_infer_type_nodes_in_type_alias_bodies() {
    let result = parse_source_file(concat!(
        "export type infer<T> = T extends infer U ? U : never;",
        "type Result<T> = T extends infer U ? U : never;",
    ));
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    let statements = source_statements(&result);
    assert_eq!(statements.len(), 2);
    for &statement in statements {
        let alias = type_alias(&result, statement);
        let NodeData::ConditionalTypeNode(body) = &result.arena.get(alias.type_).unwrap().data
        else {
            panic!("expected conditional type");
        };
        let NodeData::InferTypeNode(infer) = &result.arena.get(body.extends_type).unwrap().data
        else {
            panic!("expected infer type");
        };
        let NodeData::TypeParameterDeclaration(parameter) =
            &result.arena.get(infer.type_parameter).unwrap().data
        else {
            panic!("expected inferred type parameter");
        };
        assert_eq!(identifier_text(&result, parameter.name), "U");
    }
}

#[test]
fn rejects_invalid_type_alias_names_and_recovers() {
    for spelling in ["if", "class", "return", "false", "this", r"\u0069f"] {
        let source = format!("type {spelling} = number; type After = string;");
        let result = parse_source_file(&source);
        let diagnostic = result
            .diagnostics
            .first()
            .expect("expected name diagnostic");
        assert_eq!(
            diagnostic.message, "Expected a type alias name.",
            "{source}"
        );
        let start = diagnostic.range.start.get() as usize;
        let end = diagnostic.range.end.get() as usize;
        assert_eq!(&source[start..end], spelling);
        let statements = source_statements(&result);
        let first = type_alias(&result, statements[0]);
        assert_eq!(identifier_text(&result, first.name), "", "{source}");
        let missing = result.arena.get(first.name).unwrap();
        assert_eq!(missing.range.start, missing.range.end, "{source}");
        assert_eq!(missing.range.start, diagnostic.range.start, "{source}");
        let last = type_alias(&result, *statements.last().unwrap());
        assert_eq!(identifier_text(&result, last.name), "After", "{source}");
    }
}

#[test]
fn recovers_missing_body_after_infer_alias_name() {
    let source = "export type infer<T> = ; type After = string;";
    let result = parse_source_file(source);
    assert_eq!(result.diagnostics.len(), 1, "{:?}", result.diagnostics);
    let diagnostic = &result.diagnostics[0];
    assert_eq!(diagnostic.code, Some(1110));
    assert_eq!(
        diagnostic.range.start.get() as usize,
        source.find(';').unwrap()
    );
    let statements = source_statements(&result);
    assert_eq!(statements.len(), 2);
    let alias = type_alias(&result, statements[0]);
    assert_eq!(identifier_text(&result, alias.name), "infer");
    let NodeData::TypeReferenceNode(body) = &result.arena.get(alias.type_).unwrap().data else {
        panic!("expected missing type reference");
    };
    let missing = result.arena.get(body.type_name).unwrap();
    assert_eq!(identifier_text(&result, body.type_name), "");
    assert_eq!(missing.range.start, missing.range.end);
    assert_eq!(
        identifier_text(&result, type_alias(&result, statements[1]).name),
        "After"
    );
}

#[test]
fn requires_infer_type_parameter_name() {
    let source = "type Result<T> = T extends infer ? T : never; type After = string;";
    let result = parse_source_file(source);
    assert_eq!(result.diagnostics.len(), 1, "{:?}", result.diagnostics);
    let diagnostic = &result.diagnostics[0];
    assert_eq!(diagnostic.code, Some(1003));
    assert_eq!(
        diagnostic.range.start.get() as usize,
        source.find('?').unwrap()
    );
    let statements = source_statements(&result);
    assert_eq!(statements.len(), 2);
    let alias = type_alias(&result, statements[0]);
    let NodeData::ConditionalTypeNode(body) = &result.arena.get(alias.type_).unwrap().data else {
        panic!("expected conditional type");
    };
    let NodeData::InferTypeNode(infer) = &result.arena.get(body.extends_type).unwrap().data else {
        panic!("expected infer type");
    };
    let NodeData::TypeParameterDeclaration(parameter) =
        &result.arena.get(infer.type_parameter).unwrap().data
    else {
        panic!("expected inferred type parameter");
    };
    assert_eq!(identifier_text(&result, parameter.name), "");
    assert_eq!(
        identifier_text(&result, type_alias(&result, statements[1]).name),
        "After"
    );
}

#[test]
fn respects_await_and_yield_context_for_type_alias_names() {
    for source in [
        "function plain() { type await = string; type yield = number; }",
        "async function asynchronous() { type yield = string; type infer = number; }",
        "function* generator() { type await = string; type infer = number; }",
    ] {
        let result = parse_source_file(source);
        assert!(
            result.diagnostics.is_empty(),
            "{source}: {:?}",
            result.diagnostics
        );
    }
    for (source, keyword) in [
        (
            "async function asynchronous() { type await = string; }",
            "await",
        ),
        ("function* generator() { type yield = string; }", "yield"),
    ] {
        let result = parse_source_file(source);
        let diagnostic = result
            .diagnostics
            .first()
            .expect("expected name diagnostic");
        assert_eq!(
            diagnostic.message, "Expected a type alias name.",
            "{source}"
        );
        let start = diagnostic.range.start.get() as usize;
        let end = diagnostic.range.end.get() as usize;
        assert_eq!(&source[start..end], keyword, "{source}");
    }
}

fn source_statements(result: &ParseResult) -> &[NodeId] {
    let NodeData::SourceFile(source) = &result.arena.get(result.source_file).unwrap().data else {
        panic!("expected source file");
    };
    &source.statements.nodes
}

fn type_alias(result: &ParseResult, statement: NodeId) -> &TypeAliasDeclarationData {
    let NodeData::TypeAliasDeclaration(alias) = &result.arena.get(statement).unwrap().data else {
        panic!("expected type alias");
    };
    alias
}

fn identifier_text(result: &ParseResult, identifier: NodeId) -> &str {
    let NodeData::Identifier(identifier) = &result.arena.get(identifier).unwrap().data else {
        panic!("expected identifier");
    };
    &identifier.text
}
