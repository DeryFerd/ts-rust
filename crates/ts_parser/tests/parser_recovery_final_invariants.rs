use std::collections::HashSet;

use ts_ast::{Node, NodeData, SyntaxKind};
use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};

fn initializer<'a>(parsed: &'a ParseResult, name: &str) -> &'a Node {
    parsed
        .arena
        .iter()
        .find_map(|(_, node)| {
            let NodeData::VariableDeclaration(declaration) = &node.data else {
                return None;
            };
            let NodeData::Identifier(identifier) = &parsed.arena.get(declaration.name)?.data else {
                return None;
            };
            (identifier.text == name)
                .then(|| parsed.arena.get(declaration.initializer?))
                .flatten()
        })
        .expect("expected variable initializer")
}

fn tree_errors(parsed: &ParseResult, source: &str) -> Vec<String> {
    let mut pending = vec![parsed.source_file];
    let mut visited = HashSet::new();
    let mut errors = Vec::new();
    while let Some(id) = pending.pop() {
        if !visited.insert(id) {
            errors.push(format!("repeated child {id:?}"));
            continue;
        }
        let node = parsed.arena.get(id).expect("expected allocated node");
        let start = usize::try_from(node.range.start.get()).unwrap();
        let end = usize::try_from(node.range.end.get()).unwrap();
        if start > end
            || end > source.len()
            || !source.is_char_boundary(start)
            || !source.is_char_boundary(end)
        {
            errors.push(format!(
                "invalid UTF-8 range {:?}: {:?}",
                node.kind, node.range
            ));
        }
        node.for_each_child(|child_id| {
            let child = parsed
                .arena
                .get(child_id)
                .expect("expected allocated child");
            if child.parent != Some(id) {
                errors.push(format!("wrong parent for {:?}", child.kind));
            }
            if child.range.start < node.range.start || child.range.end > node.range.end {
                errors.push(format!(
                    "{:?} {:?} does not contain {:?} {:?}",
                    node.kind, node.range, child.kind, child.range,
                ));
            }
            pending.push(child_id);
        });
    }
    for diagnostic in &parsed.diagnostics {
        let start = usize::try_from(diagnostic.range.start.get()).unwrap();
        let end = usize::try_from(diagnostic.range.end.get()).unwrap();
        if start > end
            || end > source.len()
            || !source.is_char_boundary(start)
            || !source.is_char_boundary(end)
        {
            errors.push(format!("invalid diagnostic range {:?}", diagnostic.range));
        }
    }
    errors
}

#[test]
fn missing_inner_angle_preserves_utf8_ranges_and_parent_links() {
    let source = concat!(
        "/* \u{e9}\u{1f642} */\n",
        "const fn = <T,>(value: T): (<U() => void) => () => {};\n",
        "const after = 1;\n",
    );
    let error_start = u32::try_from(source.find("<U(").unwrap() + 2).unwrap();
    let arrow_end = u32::try_from(source.find(";\nconst after").unwrap()).unwrap();
    for parse in [parse_source_file, parse_jsx_source_file] {
        let parsed = parse(source);
        let diagnostics = parsed
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
        assert_eq!(diagnostics, [(Some(1005), error_start, error_start + 1)]);
        let function = initializer(&parsed, "fn");
        assert_eq!(function.kind, SyntaxKind::ArrowFunction);
        assert_eq!(function.range.end.get(), arrow_end);
        assert_eq!(
            initializer(&parsed, "after").kind,
            SyntaxKind::NumericLiteral
        );
        let errors = tree_errors(&parsed, source);
        assert!(errors.is_empty(), "{}", errors.join("\n"));
    }
}

#[test]
fn missing_body_before_utf8_comment_keeps_the_following_statement() {
    let source = concat!(
        "async function outer() {\n",
        "  const fn = (value: unknown): number /* \u{e9}\u{1f642}\n",
        "  */ await action();\n",
        "}\n",
        "const after = 1;\n",
    );
    let end = u32::try_from(source.find(" /*").unwrap()).unwrap();
    let error_start = u32::try_from(source.find("await action").unwrap()).unwrap();
    for parse in [parse_source_file, parse_jsx_source_file] {
        let parsed = parse(source);
        assert_eq!(parsed.diagnostics.len(), 1);
        let diagnostic = &parsed.diagnostics[0];
        assert_eq!(diagnostic.code, Some(1005));
        assert_eq!(diagnostic.range.start.get(), error_start);
        assert_eq!(diagnostic.range.end.get(), error_start + 5);
        let function = initializer(&parsed, "fn");
        let NodeData::ArrowFunction(arrow) = &function.data else {
            panic!("expected recovered arrow");
        };
        assert_eq!(function.range.end.get(), end);
        for id in [arrow.body, arrow.equals_greater_than_token] {
            let node = parsed.arena.get(id).unwrap();
            assert_eq!((node.range.start.get(), node.range.end.get()), (end, end));
        }
        assert_eq!(
            initializer(&parsed, "after").kind,
            SyntaxKind::NumericLiteral
        );
        let errors = tree_errors(&parsed, source);
        assert!(errors.is_empty(), "{}", errors.join("\n"));
    }
}

#[test]
fn missing_return_type_and_body_stay_inside_recovered_arrow() {
    let mut failures = Vec::new();
    for (name, signature) in [
        ("parenthesized", "(value: unknown):"),
        ("generic", "<T,>(value: T):"),
        ("async-generic", "async <T,>(value: T):"),
    ] {
        let source = format!("const fn = {signature} /* comment */;\nconst after = 1;\n");
        for (mode, parsed) in [
            ("TS", parse_source_file(&source)),
            ("TSX", parse_jsx_source_file(&source)),
        ] {
            // TS requires a complete generic prefix and a body candidate.
            if mode == "TS" && name != "parenthesized" {
                continue;
            }
            let function = initializer(&parsed, "fn");
            assert_eq!(function.kind, SyntaxKind::ArrowFunction, "{name}.{mode}");
            assert!(!parsed.diagnostics.is_empty(), "{name}.{mode}");
            assert_eq!(
                initializer(&parsed, "after").kind,
                SyntaxKind::NumericLiteral
            );
            let errors = tree_errors(&parsed, &source);
            for error in errors {
                failures.push(format!("{name}.{mode}: {error}"));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
