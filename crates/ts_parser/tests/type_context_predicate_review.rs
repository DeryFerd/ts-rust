use ts_ast::{NodeData, SyntaxKind};
use ts_parser::{parse_jsx_source_file, parse_source_file};

const VALID_PREDICATES: &str = concat!(
    "async function outer() {\n",
    "  const functionPredicate = (value: unknown): value is <await>() => void => true;\n",
    "  await action();\n",
    "  const constructorPredicate = (value: unknown): value is new <await>() => object => true;\n",
    "  await action();\n",
    "  const assertion = (value: unknown): asserts await => {};\n",
    "  await action();\n",
    "  const thisPredicate = (value: unknown): this is string => true;\n",
    "  await action();\n",
    "  const innerAfter = 1;\n",
    "}\n",
    "function* generator() {\n",
    "  const functionPredicate = (value: unknown): value is <yield>() => void => true;\n",
    "  yield 1;\n",
    "  const constructorPredicate = (value: unknown): value is new <yield>() => object => true;\n",
    "  yield 1;\n",
    "  const assertion = (value: unknown): asserts yield => {};\n",
    "  yield 1;\n",
    "  const thisPredicate = (value: unknown): this is string => true;\n",
    "  yield 1;\n",
    "  const innerAfter = 1;\n",
    "}\n",
    "const after = 2;\n",
);

fn assert_reserved_predicate_is_rejected(source: &str) {
    let mut accepted_modes = Vec::new();
    for (mode, parsed) in [
        ("ts", parse_source_file(source)),
        ("tsx", parse_jsx_source_file(source)),
    ] {
        let codes = parsed
            .diagnostics
            .iter()
            .map(|diagnostic| diagnostic.code)
            .collect::<Vec<_>>();
        eprintln!("predicate context mode={mode} codes={codes:?}");
        if parsed.diagnostics.is_empty() {
            accepted_modes.push(mode);
        }
    }
    assert!(
        accepted_modes.is_empty(),
        "reserved predicate name accepted in {accepted_modes:?}: {source}",
    );
}

#[test]
fn value_arrow_predicate_keeps_the_outer_await_context() {
    assert_reserved_predicate_is_rejected(concat!(
        "async function outer() {\n",
        "  const predicate = (value: unknown): await is string => true;\n",
        "  await action();\n",
        "}\n",
        "const after = 1;\n",
    ));
}

#[test]
fn value_arrow_predicate_keeps_the_outer_yield_context() {
    assert_reserved_predicate_is_rejected(concat!(
        "function* outer() {\n",
        "  const predicate = (value: unknown): yield is string => true;\n",
        "  yield 1;\n",
        "}\n",
        "const after = 1;\n",
    ));
}

#[test]
fn predicate_targets_and_assertions_keep_type_and_value_contexts() {
    for parsed in [
        parse_source_file(VALID_PREDICATES),
        parse_jsx_source_file(VALID_PREDICATES),
    ] {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let predicates = parsed
            .arena
            .iter()
            .filter_map(|(_, node)| {
                let NodeData::TypePredicateNode(predicate) = &node.data else {
                    return None;
                };
                let name = match &parsed.arena.get(predicate.parameter_name).unwrap().data {
                    NodeData::Identifier(name) => name.text.as_str(),
                    NodeData::ThisTypeNode(_) => "this",
                    _ => panic!("expected a predicate name"),
                };
                Some((
                    name,
                    predicate.asserts_modifier.is_some(),
                    predicate
                        .type_
                        .map(|node| parsed.arena.get(node).unwrap().kind),
                ))
            })
            .collect::<Vec<_>>();
        assert_eq!(
            predicates,
            [
                ("value", false, Some(SyntaxKind::FunctionType)),
                ("value", false, Some(SyntaxKind::ConstructorType)),
                ("await", true, None),
                ("this", false, Some(SyntaxKind::StringKeyword)),
                ("value", false, Some(SyntaxKind::FunctionType)),
                ("value", false, Some(SyntaxKind::ConstructorType)),
                ("yield", true, None),
                ("this", false, Some(SyntaxKind::StringKeyword)),
            ],
        );
        let type_parameters = parsed
            .arena
            .iter()
            .filter_map(|(_, node)| {
                let NodeData::TypeParameterDeclaration(parameter) = &node.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(parameter.name).unwrap().data
                else {
                    panic!("expected a type parameter name");
                };
                Some(name.text.as_str())
            })
            .collect::<Vec<_>>();
        assert_eq!(type_parameters, ["await", "await", "yield", "yield"]);
        for kind in [SyntaxKind::AwaitExpression, SyntaxKind::YieldExpression] {
            assert_eq!(
                parsed
                    .arena
                    .iter()
                    .filter(|(_, node)| node.kind == kind)
                    .count(),
                4,
                "{kind:?}",
            );
        }
        let NodeData::SourceFile(root) = &parsed.arena.get(parsed.source_file).unwrap().data else {
            panic!("expected source file");
        };
        assert_eq!(root.statements.nodes.len(), 3);
        assert_eq!(
            parsed.arena.get(root.statements.nodes[2]).unwrap().kind,
            SyntaxKind::VariableStatement,
        );
    }
}
