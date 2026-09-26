use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

struct ExpectedAssignment<'a> {
    expression: &'a str,
    start: usize,
    target_type: &'a str,
    rhs_type: &'a str,
    arguments: [&'a str; 2],
}

fn strict_context(parsed: &ParseResult, file: FileId) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            file,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/nullish-assignment-diagnostics.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            )
            .with_always_strict(true),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, file)
        .unwrap();
    CanonicalCheckerContext::new(
        binder.finish(),
        [(file, &parsed.arena)].into_iter().collect(),
        CanonicalCheckerOptions {
            intrinsic: IntrinsicBootstrapOptions {
                strict_null_checks: true,
                ..IntrinsicBootstrapOptions::default()
            },
            no_implicit_any: true,
            strict_function_types: true,
            ..CanonicalCheckerOptions::default()
        },
    )
    .unwrap()
}

fn node_text<'source>(source: &'source str, parsed: &ParseResult, node: NodeRef) -> &'source str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn assignment_nodes(
    source: &str,
    parsed: &ParseResult,
    file: FileId,
    expected: &[ExpectedAssignment<'_>],
) -> Vec<[NodeRef; 3]> {
    expected
        .iter()
        .map(|expected| {
            parsed
                .arena
                .iter()
                .find_map(|(id, record)| {
                    let NodeData::BinaryExpression(binary) = &record.data else {
                        return None;
                    };
                    let expression = NodeRef::new(parsed.arena.id(), file, id);
                    if node_text(source, parsed, expression) != expected.expression {
                        return None;
                    }
                    assert_eq!(
                        parsed.arena.get(binary.operator_token).unwrap().kind,
                        SyntaxKind::QuestionQuestionEqualsToken,
                    );
                    Some([
                        expression,
                        NodeRef::new(parsed.arena.id(), file, binary.left),
                        NodeRef::new(parsed.arena.id(), file, binary.right),
                    ])
                })
                .unwrap_or_else(|| panic!("missing assignment {}", expected.expression))
        })
        .collect()
}

fn resolved_type(context: &CanonicalCheckerContext<'_>, node: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(node)
        .and_then(|links| links.resolved_type)
        .unwrap_or_else(|| panic!("missing published type for {node:?}"))
}

fn published_types(
    context: &CanonicalCheckerContext<'_>,
    nodes: &[[NodeRef; 3]],
    expected: &[ExpectedAssignment<'_>],
) -> Vec<[TypeId; 3]> {
    nodes
        .iter()
        .zip(expected)
        .map(|(nodes, expected)| {
            let types = nodes.map(|node| resolved_type(context, node));
            assert_eq!(
                context.type_to_string(types[1]).unwrap(),
                expected.target_type
            );
            assert_eq!(context.type_to_string(types[2]).unwrap(), expected.rhs_type);
            types
        })
        .collect()
}

fn assert_diagnostics(
    context: &CanonicalCheckerContext<'_>,
    source: &str,
    parsed: &ParseResult,
    nodes: &[[NodeRef; 3]],
    expected: &[ExpectedAssignment<'_>],
) {
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), expected.len());
    for ((diagnostic, nodes), expected) in diagnostics.iter().zip(nodes).zip(expected) {
        assert_eq!(diagnostic.node, Some(nodes[1]));
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic
                .diagnostic
                .arguments
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            expected.arguments,
        );
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
        assert!(diagnostic.diagnostic.details.is_empty());
        let target_text = expected.expression.split_once(" ??= ").unwrap().0;
        assert_eq!(node_text(source, parsed, nodes[1]), target_text);
        let range = parsed.arena.get(nodes[1].node).unwrap().range;
        assert_eq!(usize::try_from(range.start.get()).unwrap(), expected.start);
        assert_eq!(
            usize::try_from(range.end.get()).unwrap(),
            expected.start + target_text.len(),
        );
    }
}

// Check source-first and each cold assignment query, then preserve all three
// published type identities and the whole diagnostic list through both rechecks.
fn check_case(source: &str, expected: &[ExpectedAssignment<'_>]) {
    let parsed = parse_source_file(source);
    let file = FileId::new(202_972);
    let nodes = assignment_nodes(source, &parsed, file, expected);
    for first in std::iter::once(None).chain(nodes.iter().map(|nodes| Some(nodes[0]))) {
        let mut context = strict_context(&parsed, file);
        let first_type = first.map(|node| (node, context.get_type_at_location(node).unwrap()));
        context.check_source_file(file).unwrap();
        assert_diagnostics(&context, source, &parsed, &nodes, expected);
        let types = published_types(&context, &nodes, expected);
        let diagnostics = context.diagnostics().clone();
        if let Some((node, type_)) = first_type {
            assert_eq!(context.get_type_at_location(node), Ok(type_));
        }
        for forced in [false, true] {
            if forced {
                context.recheck_source_file(file).unwrap();
            } else {
                context.check_source_file(file).unwrap();
            }
            assert_diagnostics(&context, source, &parsed, &nodes, expected);
            assert_eq!(published_types(&context, &nodes, expected), types);
            assert_eq!(context.diagnostics(), &diagnostics);
            for (nodes, types) in nodes.iter().zip(&types) {
                for (&node, &type_) in nodes.iter().zip(types) {
                    assert_eq!(context.get_type_at_location(node), Ok(type_));
                }
            }
        }
    }
}

#[test]
fn nullable_assignment_display_keeps_both_rhs_errors_and_semantic_types() {
    let source = concat!(
        "let value: string | undefined;\n",
        "value ??= 1;\n",
        "let present: string = 'ready';\n",
        "present ??= 2;\n",
    );
    check_case(
        source,
        &[
            ExpectedAssignment {
                expression: "value ??= 1",
                start: 31,
                target_type: "string | undefined",
                rhs_type: "1",
                arguments: ["number", "string"],
            },
            ExpectedAssignment {
                expression: "present ??= 2",
                start: 75,
                target_type: "string",
                rhs_type: "2",
                arguments: ["number", "string"],
            },
        ],
    );
}

#[test]
fn nullable_assignment_display_keeps_the_target_alias() {
    let source = concat!(
        "type MaybeText = string | undefined;\n",
        "let value: MaybeText;\n",
        "value ??= 1;\n",
    );
    check_case(
        source,
        &[ExpectedAssignment {
            expression: "value ??= 1",
            start: 59,
            target_type: "MaybeText",
            rhs_type: "1",
            arguments: ["1", "MaybeText"],
        }],
    );
}

#[test]
fn nullable_assignment_display_keeps_literals_for_a_literal_target() {
    let source = concat!("let value: \"ready\" | undefined;\n", "value ??= 1;\n",);
    check_case(
        source,
        &[ExpectedAssignment {
            expression: "value ??= 1",
            start: 32,
            target_type: "\"ready\" | undefined",
            rhs_type: "1",
            arguments: ["1", "\"ready\""],
        }],
    );
}
