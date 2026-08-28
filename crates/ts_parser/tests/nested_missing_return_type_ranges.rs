include!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../docs/review-probes/parser-missing-return-final-review.rs"
));

#[test]
fn nested_signatures_keep_missing_returns_after_their_headers() {
    for signature in REVIEW_SIGNATURES {
        for head in [
            "<",
            "new <",
            "abstract new <",
            "<const",
            "new <const",
            "abstract new <const",
        ] {
            for trivia in [" /* comment */", " /* \u{e9}\u{1f642}\n */"] {
                let prefix = format!("const fn = {signature} ({head}");
                let source = format!("{prefix}{trivia});\nconst after = 1;\n");
                let end = u32::try_from(prefix.len()).unwrap();
                let closing = u32::try_from(source.find(");").unwrap()).unwrap();
                for (mode, parsed) in [
                    ("TS", parse_source_file(&source)),
                    ("TSX", parse_jsx_source_file(&source)),
                ] {
                    if mode == "TS" && signature != REVIEW_SIGNATURES[0] {
                        continue;
                    }
                    let function = initializer(&parsed, "fn");
                    let NodeData::ArrowFunction(arrow) = &function.data else {
                        panic!("expected recovered arrow");
                    };
                    assert_eq!(function.range.end.get(), closing + 1);
                    let NodeData::ParenthesizedTypeNode(wrapper) =
                        &parsed.arena.get(arrow.type_.unwrap()).unwrap().data
                    else {
                        panic!("expected parenthesized signature");
                    };
                    let nested = parsed.arena.get(wrapper.type_).unwrap();
                    let (types, parameters, return_type) = match &nested.data {
                        NodeData::FunctionTypeNode(function) => (
                            function.type_parameters.as_ref().unwrap(),
                            &function.parameters,
                            function.type_.unwrap(),
                        ),
                        NodeData::ConstructorTypeNode(constructor) => (
                            constructor.type_parameters.as_ref().unwrap(),
                            &constructor.parameters,
                            constructor.type_.unwrap(),
                        ),
                        _ => panic!("expected a function or constructor type"),
                    };
                    assert_eq!(nested.range.end.get(), end);
                    assert_eq!(types.nodes.len(), 1);
                    assert_eq!(types.range.end.get(), end);
                    assert!(parameters.nodes.is_empty());
                    assert_eq!(parameters.range.start.get(), end);
                    assert_eq!(parameters.range.end.get(), end);
                    let parameter = parsed.arena.get(types.nodes[0]).unwrap();
                    let NodeData::TypeParameterDeclaration(parameter_data) = &parameter.data else {
                        panic!("expected missing type parameter");
                    };
                    assert_eq!(parameter.range.end.get(), end);
                    if let Some(modifiers) = &parameter_data.modifiers {
                        assert_eq!(parameter.range.start, modifiers.list.range.start);
                        assert_eq!(modifiers.list.range.end.get(), end);
                    } else {
                        assert_eq!(parameter.range.start.get(), end);
                    }
                    let returned = parsed.arena.get(return_type).unwrap();
                    let NodeData::TypeReferenceNode(reference) = &returned.data else {
                        panic!("expected missing return type");
                    };
                    for node in [
                        parsed.arena.get(parameter_data.name).unwrap(),
                        returned,
                        parsed.arena.get(reference.type_name).unwrap(),
                    ] {
                        assert_eq!((node.range.start.get(), node.range.end.get()), (end, end));
                    }
                    let diagnostics = parsed
                        .diagnostics
                        .iter()
                        .map(|item| (item.code, item.range.start.get(), item.range.end.get()))
                        .collect::<Vec<_>>();
                    assert_eq!(
                        diagnostics,
                        [
                            (Some(1003), closing, closing + 1),
                            (Some(1005), closing + 1, closing + 2),
                        ],
                        "{mode}: {source}",
                    );
                    let errors = tree_errors(&parsed, &source);
                    assert!(errors.is_empty(), "{}", errors.join("\n"));
                    assert_eq!(
                        initializer(&parsed, "after").range.end.get() as usize,
                        source.rfind('1').unwrap() + 1,
                    );
                }
            }
        }
    }
}

#[test]
fn nested_signature_returns_restore_the_enclosing_arrow_context() {
    for signature in REVIEW_SIGNATURES {
        for head in ["<T>()", "new <T>()", "abstract new <T>()"] {
            let source = format!(
                "const fn = {signature} (({head} => Result) | /* comment */);\nconst after = 1;\n"
            );
            let end = u32::try_from(source.find("| /*").unwrap() + 1).unwrap();
            for (mode, parsed) in [
                ("TS", parse_source_file(&source)),
                ("TSX", parse_jsx_source_file(&source)),
            ] {
                if mode == "TS" && signature != REVIEW_SIGNATURES[0] {
                    continue;
                }
                let missing = parsed
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
                    .collect::<Vec<_>>();
                assert_eq!(missing.len(), 1, "{mode}: {source}");
                for node in [missing[0].0, missing[0].1] {
                    assert_eq!((node.range.start.get(), node.range.end.get()), (end, end));
                }
                assert_eq!(
                    initializer(&parsed, "fn").range.end.get() as usize,
                    source.find(";\n").unwrap(),
                );
                let errors = tree_errors(&parsed, &source);
                assert!(errors.is_empty(), "{mode}: {source}: {}", errors.join("\n"));
                assert_eq!(
                    initializer(&parsed, "after").kind,
                    SyntaxKind::NumericLiteral
                );
            }
        }
    }
}

#[test]
fn unparenthesized_missing_signature_returns_stay_inside_the_arrow() {
    for signature in REVIEW_SIGNATURES {
        for head in [
            "<",
            "new <",
            "abstract new <",
            "<T>() =>",
            "new <T>() =>",
            "abstract new <T>() =>",
        ] {
            let prefix = format!("const fn = {signature} {head}");
            let source = format!("{prefix} /* comment */;\nconst after = 1;\n");
            for (mode, parsed) in [
                ("TS", parse_source_file(&source)),
                ("TSX", parse_jsx_source_file(&source)),
            ] {
                if mode == "TS" && signature != REVIEW_SIGNATURES[0] {
                    continue;
                }
                let function = initializer(&parsed, "fn");
                assert_eq!(function.kind, SyntaxKind::ArrowFunction, "{mode}: {source}");
                assert_eq!(
                    function.range.end.get() as usize,
                    prefix.len(),
                    "{mode}: {source}"
                );
                let errors = tree_errors(&parsed, &source);
                assert!(errors.is_empty(), "{mode}: {source}: {}", errors.join("\n"));
                assert_eq!(
                    initializer(&parsed, "after").kind,
                    SyntaxKind::NumericLiteral
                );
                assert_eq!(
                    initializer(&parsed, "after").range.end.get() as usize,
                    source.rfind('1').unwrap() + 1,
                );
            }
        }
    }
}
