use ts_ast::{Node, NodeData, SyntaxKind};
use ts_parser::{ParseResult, parse_jsx_source_file, parse_source_file};

const SIGNATURES: [&str; 3] = [
    "(value: unknown):",
    "<T,>(value: T):",
    "async <T,>(value: T):",
];

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
            if identifier.text == name {
                parsed.arena.get(declaration.initializer?)
            } else {
                None
            }
        })
        .expect("expected variable initializer")
}

fn assert_empty_range(node: &Node, position: usize) {
    assert_eq!(node.range.start.get() as usize, position);
    assert_eq!(node.range.end.get() as usize, position);
}

fn assert_missing_return_type(parsed: &ParseResult, end: usize) {
    let function = initializer(parsed, "fn");
    let NodeData::ArrowFunction(arrow) = &function.data else {
        panic!("expected recovered arrow");
    };
    assert_eq!(function.range.start.get(), 11);
    assert_eq!(function.range.end.get() as usize, end);
    for id in [arrow.body, arrow.equals_greater_than_token] {
        assert_empty_range(parsed.arena.get(id).unwrap(), end);
    }
    let return_type = parsed.arena.get(arrow.type_.unwrap()).unwrap();
    assert_eq!(return_type.range.end.get() as usize, end);
    let reference = if let NodeData::UnionTypeNode(union) = &return_type.data {
        parsed
            .arena
            .get(*union.types.nodes.last().unwrap())
            .unwrap()
    } else {
        return_type
    };
    let NodeData::TypeReferenceNode(reference_data) = &reference.data else {
        panic!("expected missing type reference");
    };
    assert!(reference_data.type_arguments.is_none());
    let name = parsed.arena.get(reference_data.type_name).unwrap();
    let missing_name = if let NodeData::QualifiedName(qualified) = &name.data {
        parsed.arena.get(qualified.right).unwrap()
    } else {
        assert_empty_range(reference, end);
        name
    };
    assert_empty_range(missing_name, end);
    let NodeData::Identifier(identifier) = &missing_name.data else {
        panic!("expected missing type name");
    };
    assert!(identifier.text.is_empty());
}

#[test]
fn missing_return_names_keep_arrow_ends_before_comments() {
    for signature in SIGNATURES {
        for (type_tail, code) in [("", 1110), (" Result.", 1003), (" Result |", 1110)] {
            for trivia in [" /* comment */", " /* \u{e9}\u{1f642}\n */"] {
                let prefix = format!("const fn = {signature}{type_tail}");
                let source = format!("{prefix}{trivia};\nconst after = 1;\n");
                let error_start = u32::try_from(prefix.len() + trivia.len()).unwrap();
                for (mode, parsed) in [
                    ("TS", parse_source_file(&source)),
                    ("TSX", parse_jsx_source_file(&source)),
                ] {
                    // In TS, incomplete generic signatures are not selected as arrows.
                    if mode == "TS" && signature != SIGNATURES[0] {
                        continue;
                    }
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
                    assert_eq!(
                        diagnostics,
                        [(Some(code), error_start, error_start + 1)],
                        "{mode}: {source}",
                    );
                    assert_missing_return_type(&parsed, prefix.len());
                    let after = initializer(&parsed, "after");
                    assert_eq!(after.kind, SyntaxKind::NumericLiteral);
                    assert_eq!(after.range.start.get() as usize, source.rfind('1').unwrap());
                    assert_eq!(
                        after.range.end.get() as usize,
                        source.rfind('1').unwrap() + 1
                    );
                }
            }
        }
    }
}

#[test]
fn missing_return_type_at_eof_keeps_the_existing_diagnostic_location() {
    for signature in SIGNATURES {
        let prefix = format!("const fn = {signature}");
        let source = format!("{prefix} /* comment */\n");
        for (mode, parsed) in [
            ("TS", parse_source_file(&source)),
            ("TSX", parse_jsx_source_file(&source)),
        ] {
            if mode == "TS" && signature != SIGNATURES[0] {
                continue;
            }
            assert_eq!(parsed.diagnostics.len(), 1, "{mode}: {source}");
            let diagnostic = &parsed.diagnostics[0];
            assert_eq!(diagnostic.code, Some(1110));
            assert_eq!(diagnostic.range.start.get() as usize, source.len());
            assert_eq!(diagnostic.range.end.get() as usize, source.len());
            assert_missing_return_type(&parsed, prefix.len());
        }
    }
}

#[test]
fn existing_return_type_names_keep_their_token_ranges() {
    for signature in SIGNATURES {
        for type_text in ["Result", "Namespace.Result"] {
            let source = format!(
                "const fn = {signature} /* type */ {type_text} => value;\nconst after = 1;\n"
            );
            for parse in [parse_source_file, parse_jsx_source_file] {
                let parsed = parse(&source);
                assert!(
                    parsed.diagnostics.is_empty(),
                    "{source}: {:?}",
                    parsed.diagnostics
                );
                let function = initializer(&parsed, "fn");
                let NodeData::ArrowFunction(arrow) = &function.data else {
                    panic!("expected valid arrow");
                };
                let type_node = parsed.arena.get(arrow.type_.unwrap()).unwrap();
                let NodeData::TypeReferenceNode(reference) = &type_node.data else {
                    panic!("expected type reference");
                };
                let start = source.find(type_text).unwrap();
                for node in [type_node, parsed.arena.get(reference.type_name).unwrap()] {
                    assert_eq!(node.range.start.get() as usize, start);
                    assert_eq!(node.range.end.get() as usize, start + type_text.len());
                }
                let body = parsed.arena.get(arrow.body).unwrap();
                let NodeData::Identifier(identifier) = &body.data else {
                    panic!("expected identifier body");
                };
                assert_eq!(identifier.text, "value");
                assert_eq!(
                    function.range.end.get() as usize,
                    source.find(";\n").unwrap()
                );
                assert_eq!(
                    initializer(&parsed, "after").kind,
                    SyntaxKind::NumericLiteral
                );
            }
        }
    }
}

#[test]
fn arrow_return_recovery_does_not_change_following_type_names() {
    for signature in SIGNATURES {
        for following in ["type Alias< /* comment */}", "const value: /* comment */;"] {
            let source = format!("const fn = {signature} /* comment */;\n{following}");
            let expected = source.len() - 1;
            for (mode, parsed) in [
                ("TS", parse_source_file(&source)),
                ("TSX", parse_jsx_source_file(&source)),
            ] {
                if mode == "TS" && signature != SIGNATURES[0] {
                    continue;
                }
                let reference = parsed
                    .arena
                    .iter()
                    .filter_map(|(_, node)| {
                        let NodeData::TypeReferenceNode(reference) = &node.data else {
                            return None;
                        };
                        let name = parsed.arena.get(reference.type_name).unwrap();
                        let NodeData::Identifier(identifier) = &name.data else {
                            return None;
                        };
                        identifier.text.is_empty().then_some((node, name))
                    })
                    .last()
                    .expect("expected following missing type");
                assert_empty_range(reference.0, expected);
                assert_empty_range(reference.1, expected);
                let parent = parsed.arena.get(reference.0.parent.unwrap()).unwrap();
                parent.for_each_child(|id| {
                    let child = parsed.arena.get(id).unwrap();
                    assert!(parent.range.start <= child.range.start);
                    assert!(child.range.end <= parent.range.end);
                });
            }
        }
    }
}
