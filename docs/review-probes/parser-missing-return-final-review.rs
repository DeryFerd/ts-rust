include!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../docs/review-probes/parser-recovery-final-invariants.rs"
));

const REVIEW_SIGNATURES: [&str; 3] = [
    "(value: unknown):",
    "<T,>(value: T):",
    "async <T,>(value: T):",
];

#[test]
fn nested_missing_type_wrappers_keep_ranges_and_ownership() {
    for signature in REVIEW_SIGNATURES {
        for type_text in [
            "(Result | /* \u{e9}\u{1f642} */)",
            "(Result & /* \u{e9}\u{1f642} */)",
            "(keyof /* \u{e9}\u{1f642} */)",
            "[item: /* \u{e9}\u{1f642} */]",
            "[... /* \u{e9}\u{1f642} */]",
            "Box< /* \u{e9}\u{1f642} */, Result>",
            "Result[Type | /* \u{e9}\u{1f642} */]",
            "(`prefix${ /* \u{e9}\u{1f642} */}suffix`)",
        ] {
            let source = format!("const fn = {signature} {type_text};\nconst after = 1;\n");
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
                    source.find(";\n").unwrap(),
                    "{mode}: {source}",
                );
                assert!(
                    parsed
                        .diagnostics
                        .iter()
                        .any(|item| item.code == Some(1110)),
                    "{mode}: {source}: {:?}",
                    parsed.diagnostics,
                );
                assert_eq!(
                    initializer(&parsed, "after").kind,
                    SyntaxKind::NumericLiteral
                );
                let errors = tree_errors(&parsed, &source);
                assert!(errors.is_empty(), "{mode}: {source}: {}", errors.join("\n"));
            }
        }
    }
}

#[test]
fn arrow_bodies_do_not_keep_the_return_type_context() {
    let source = concat!(
        "const fn = (value: unknown): Result => {\n",
        "  const inside: /* comment */;\n",
        "  const inner = (): Result => { const nested: /* comment */; };\n",
        "};\n",
        "const outside: /* comment */;\n",
        "const after = 1;\n",
    );
    for parse in [parse_source_file, parse_jsx_source_file] {
        let parsed = parse(source);
        for name in ["inside", "nested", "outside"] {
            let marker = format!("const {name}: /* comment */");
            let expected = source.find(&marker).unwrap() + marker.len();
            let type_node = parsed
                .arena
                .iter()
                .find_map(|(_, node)| {
                    let NodeData::VariableDeclaration(declaration) = &node.data else {
                        return None;
                    };
                    let NodeData::Identifier(identifier) =
                        &parsed.arena.get(declaration.name)?.data
                    else {
                        return None;
                    };
                    (identifier.text == name)
                        .then(|| parsed.arena.get(declaration.type_?))
                        .flatten()
                })
                .expect("expected missing variable type");
            assert_eq!(type_node.range.start.get() as usize, expected, "{name}");
            assert_eq!(type_node.range.end.get() as usize, expected, "{name}");
        }
        let errors = tree_errors(&parsed, source);
        assert!(errors.is_empty(), "{}", errors.join("\n"));
        assert_eq!(
            initializer(&parsed, "after").kind,
            SyntaxKind::NumericLiteral
        );
    }
}

#[test]
fn nested_missing_generic_names_stay_inside_their_function_types() {
    let mut failures = Vec::new();
    for signature in REVIEW_SIGNATURES {
        for type_text in [
            "(< /* comment */)",
            "(new < /* comment */)",
            "(abstract new < /* comment */)",
        ] {
            let source = format!("const fn = {signature} {type_text};\nconst after = 1;\n");
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
                    source.find(";\n").unwrap(),
                    "{mode}: {source}",
                );
                let after = initializer(&parsed, "after");
                assert_eq!(after.kind, SyntaxKind::NumericLiteral);
                assert_eq!(
                    after.range.end.get() as usize,
                    source.rfind('1').unwrap() + 1
                );
                let diagnostics = parsed
                    .diagnostics
                    .iter()
                    .map(|item| (item.code, item.range.start.get(), item.range.end.get()))
                    .collect::<Vec<_>>();
                eprintln!(
                    "{mode}: {signature} {type_text}: arrow end {}, after end {}, diagnostics {diagnostics:?}",
                    function.range.end.get(),
                    after.range.end.get(),
                );
                let errors = tree_errors(&parsed, &source);
                if !errors.is_empty() {
                    failures.push(format!("{mode}: {source}: {}", errors.join("\n")));
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
