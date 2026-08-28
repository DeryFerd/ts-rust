use ts_ast::{Node, NodeData, SyntaxKind};
use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};

#[test]
fn malformed_generic_return_types_keep_the_pinned_ts_and_tsx_decisions() {
    // Expected kinds and end positions come from wave140's saved pinned Go controls.
    let mut mismatches = Vec::new();
    for (name, declaration, ts_kind, ts_end, tsx_end, after_end) in [
        (
            "missing-outer-arrow",
            "const fn = <T,>(value: T): (<U>() => void);",
            SyntaxKind::TypeAssertionExpression,
            13,
            42,
            59,
        ),
        (
            "missing-return-type",
            "const fn = <T,>(value: T): (<U>() => ) => () => {};",
            SyntaxKind::TypeAssertionExpression,
            13,
            50,
            67,
        ),
        (
            "missing-type-parameter",
            "const fn = <T,>(value: T): (<,>() => void) => () => {};",
            SyntaxKind::ArrowFunction,
            54,
            54,
            71,
        ),
        (
            "missing-close-angle",
            "const fn = <T,>(value: T): (<U() => void) => () => {};",
            SyntaxKind::ArrowFunction,
            53,
            53,
            70,
        ),
    ] {
        let source = format!("{declaration}\nconst after = 1;\n");
        for (mode, parsed, expected_kind, expected_end) in [
            ("TS", parse_source_file(&source), ts_kind, ts_end),
            (
                "TSX",
                parse_jsx_source_file(&source),
                SyntaxKind::ArrowFunction,
                tsx_end,
            ),
        ] {
            let function = initializer(&parsed, "fn");
            let after = initializer(&parsed, "after");
            let kind = function.map(|node| node.kind);
            let end = function.map(|node| node.range.end.get());
            let following_kind = after.map(|node| node.kind);
            let following_end = after.map(|node| node.range.end.get());
            eprintln!(
                "{name}.{mode}: kind={kind:?} end={end:?} expected_kind={expected_kind:?} expected_end={expected_end} after_kind={following_kind:?} after_end={following_end:?} diagnostics={}",
                parsed.diagnostics.len(),
            );
            if (kind, end) != (Some(expected_kind), Some(expected_end)) {
                mismatches.push(format!(
                    "{name}.{mode}: {kind:?}/{end:?} != {expected_kind:?}/{expected_end}",
                ));
            }
            if (following_kind, following_end)
                != (Some(SyntaxKind::NumericLiteral), Some(after_end))
            {
                mismatches.push(format!("{name}.{mode}: following declaration differs"));
            }
            let following_start = source.find("const after").unwrap();
            if parsed.diagnostics.is_empty()
                || !parsed
                    .diagnostics
                    .iter()
                    .all(|diagnostic| diagnostic.range.end.get() as usize <= following_start)
            {
                mismatches.push(format!("{name}.{mode}: invalid-source diagnostics differ"));
            }
        }
    }
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}

fn initializer<'a>(parsed: &'a ParseResult, expected: &str) -> Option<&'a Node> {
    let NodeData::SourceFile(source) = &parsed.arena.get(parsed.source_file).unwrap().data else {
        panic!("expected a source file")
    };
    source.statements.nodes.iter().find_map(|statement| {
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
                let NodeData::VariableDeclaration(variable) = &parsed.arena.get(*declaration)?.data
                else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                    return None;
                };
                (name.text == expected)
                    .then(|| parsed.arena.get(variable.initializer?))
                    .flatten()
            })
    })
}

#[test]
fn missing_inner_close_angle_keeps_exact_recovery_in_both_modes() {
    let source = concat!(
        "const fn = <T,>(value: T): (<U() => void) => () => {};\n",
        "const after = 1;\n",
    );
    for (mode, parsed) in [
        ("TS", parse_source_file(source)),
        ("TSX", parse_jsx_source_file(source)),
    ] {
        let diagnostics = parsed
            .diagnostics
            .iter()
            .map(|diagnostic| {
                (
                    diagnostic.code.expect("expected a catalog diagnostic"),
                    diagnostic.range.start.get(),
                    diagnostic.range.end.get(),
                )
            })
            .collect::<Vec<_>>();
        eprintln!("missing-close-angle.{mode}: diagnostics={diagnostics:?}");
        assert_eq!(diagnostics, [(1005, 30, 31)], "{mode}");
        let function = initializer(&parsed, "fn").expect("expected outer initializer");
        assert_eq!(function.kind, SyntaxKind::ArrowFunction, "{mode}");
        assert_eq!(function.range.end.get(), 53, "{mode}");
        let NodeData::ArrowFunction(arrow) = &function.data else {
            panic!("expected outer arrow");
        };
        let NodeData::ParenthesizedTypeNode(parenthesized) =
            &parsed.arena.get(arrow.type_.unwrap()).unwrap().data
        else {
            panic!("expected parenthesized return type");
        };
        let NodeData::FunctionTypeNode(inner) =
            &parsed.arena.get(parenthesized.type_).unwrap().data
        else {
            panic!("expected recovered generic function type");
        };
        assert_eq!(inner.type_parameters.as_ref().unwrap().nodes.len(), 1);
        assert_eq!(
            parsed.arena.get(inner.type_.unwrap()).unwrap().kind,
            SyntaxKind::VoidKeyword,
        );
        assert_eq!(
            parsed.arena.get(arrow.body).unwrap().kind,
            SyntaxKind::ArrowFunction
        );
        let after = initializer(&parsed, "after").expect("expected following declaration");
        assert_eq!(after.kind, SyntaxKind::NumericLiteral, "{mode}");
        assert_eq!(after.range.end.get(), 70, "{mode}");
    }
}
