use ts_ast::{FileId, FlowFlags, FlowNodePayload, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions, TypeId,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_1102);

fn checked_context(
    parsed: &ParseResult,
    first_query: Option<NodeRef>,
) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/optional-top-level-read.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                CanonicalModuleState::Script,
            )
            .with_always_strict(true),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    let mut context = CanonicalCheckerContext::new(
        binder.finish(),
        [(FILE, &parsed.arena)].into_iter().collect(),
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
    .unwrap();
    let first = first_query.map(|node| (node, context.get_type_at_location(node).unwrap()));
    context.check_source_file(FILE).unwrap();
    if let Some((node, type_)) = first {
        assert_eq!(context.get_type_at_location(node), Ok(type_));
    }
    context
}

fn node_text<'a>(source: &'a str, parsed: &ParseResult, node: NodeRef) -> &'a str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

// Return the actual declaration, name, annotation and optional initializer.
fn variable(
    parsed: &ParseResult,
    expected: &str,
    ordinal: usize,
) -> (NodeRef, NodeRef, NodeRef, Option<NodeRef>) {
    parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                (
                    NodeRef::new(parsed.arena.id(), FILE, id),
                    NodeRef::new(parsed.arena.id(), FILE, variable.name),
                    NodeRef::new(parsed.arena.id(), FILE, variable.type_.unwrap()),
                    variable
                        .initializer
                        .map(|node| NodeRef::new(parsed.arena.id(), FILE, node)),
                )
            })
        })
        .nth(ordinal)
        .unwrap_or_else(|| panic!("missing declaration {expected}[{ordinal}]"))
}

fn optional_nodes(source: &str, parsed: &ParseResult) -> (NodeRef, NodeRef, NodeRef) {
    let assignment = parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let node = NodeRef::new(parsed.arena.id(), FILE, id);
            (record.kind == SyntaxKind::BinaryExpression
                && node_text(source, parsed, node) == "value ??= 'fallback'")
                .then_some(node)
        })
        .unwrap();
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(assignment.node).unwrap().data
    else {
        panic!("expected the actual nullish assignment");
    };
    (
        assignment,
        NodeRef::new(parsed.arena.id(), FILE, binary.left),
        variable(parsed, "good", 0).3.unwrap(),
    )
}

fn resolved_annotation(context: &CanonicalCheckerContext<'_>, annotation: NodeRef) -> TypeId {
    context
        .store()
        .type_node_links(annotation)
        .and_then(|links| links.resolved_type)
        .expect("the source check must resolve the real declaration annotation")
}

fn string_annotation_type(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    declaration: NodeRef,
    annotation: NodeRef,
) -> TypeId {
    let node = parsed.arena.get(annotation.node).unwrap();
    assert_eq!(node.kind, SyntaxKind::StringKeyword);
    assert_eq!(node.parent, Some(declaration.node));
    context.store().intrinsic_bootstrap().unwrap().string_type
}

fn assert_optional_root(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    assignment: NodeRef,
    left: NodeRef,
    read: NodeRef,
) -> [(NodeRef, TypeId); 5] {
    let (declaration, name, annotation, _) = variable(parsed, "value", 0);
    let (good, _, string_annotation, _) = variable(parsed, "good", 0);
    let declared = resolved_annotation(context, annotation);
    let string = string_annotation_type(context, parsed, good, string_annotation);
    assert_ne!(declared, string);
    assert_eq!(
        context.type_to_string(declared).unwrap(),
        "string | undefined"
    );
    assert_eq!(context.type_to_string(string).unwrap(), "string");
    let types = [
        (annotation, declared),
        (string_annotation, string),
        (assignment, string),
        (left, declared),
        (read, string),
    ];
    for (node, type_) in types {
        assert_eq!(context.get_type_at_location(node), Ok(type_));
    }
    let symbol = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
    for node in [name, left, read] {
        assert_eq!(context.get_symbol_at_location(node), Ok(Some(symbol)));
    }
    let graph = context.file(FILE).unwrap().1.flow_graph();
    assert!(graph.is_complete(), "{:?}", graph.unsupported());
    assert_eq!(
        graph
            .nodes()
            .iter()
            .filter(|flow| {
                flow.flags.contains(FlowFlags::ASSIGNMENT)
                    && flow.payload == Some(FlowNodePayload::Ast(left))
            })
            .count(),
        1,
    );
    types
}

fn assert_uninitialized(context: &CanonicalCheckerContext<'_>, read: NodeRef) {
    let diagnostics = context.diagnostics().as_slice();
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    let diagnostic = &diagnostics[0];
    assert_eq!(diagnostic.diagnostic.code(), 2454);
    assert_eq!(diagnostic.diagnostic.arguments, ["value"]);
    assert_eq!(diagnostic.node, Some(read));
    assert!(diagnostic.range_override.is_none());
    assert!(diagnostic.related_information.is_empty());
}

// Keep canonical types, published links, flow and diagnostics stable across replay.
fn semantic_state(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
) -> impl PartialEq + std::fmt::Debug + use<> {
    let store = context.store();
    (
        parsed
            .arena
            .iter()
            .map(|(id, _)| {
                let node = NodeRef::new(parsed.arena.id(), FILE, id);
                (
                    node,
                    store.node_links(node).cloned(),
                    store.type_node_links(node).cloned(),
                    store.symbol_node_links(node).cloned(),
                    store.signature_links(node).cloned(),
                )
            })
            .collect::<Vec<_>>(),
        store
            .symbol_store()
            .symbols()
            .map(|(symbol, _)| (symbol, store.value_symbol_links(symbol).cloned()))
            .collect::<Vec<_>>(),
        store
            .source_file_links(context.source_file(FILE).unwrap())
            .cloned(),
        context.file(FILE).unwrap().1.flow_graph().clone(),
        context.diagnostics().clone(),
    )
}

fn assert_replay(
    context: &mut CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    types: &[(NodeRef, TypeId)],
    identifiers: &[NodeRef],
) {
    let symbols = identifiers
        .iter()
        .map(|&node| (node, context.get_symbol_at_location(node).unwrap()))
        .collect::<Vec<_>>();
    let before = semantic_state(context, parsed);
    context.check_source_file(FILE).unwrap();
    assert_eq!(semantic_state(context, parsed), before);
    context.recheck_source_file(FILE).unwrap();
    for &(node, type_) in types {
        assert_eq!(context.get_type_at_location(node), Ok(type_));
    }
    for (node, symbol) in symbols {
        assert_eq!(context.get_symbol_at_location(node), Ok(symbol));
    }
    assert_eq!(semantic_state(context, parsed), before);
}

#[test]
fn optional_top_level_declaration_keeps_its_narrowed_read() {
    // Keep the original failure-74 TypeScript unchanged.
    let source = concat!(
        "let value: string | undefined;\n",
        "value ??= 'fallback';\n",
        "const good: string = value;\n",
    );
    let parsed = parse_source_file(source);
    let (assignment, left, read) = optional_nodes(source, &parsed);
    for first in [None, Some(assignment), Some(read)] {
        let mut context = checked_context(&parsed, first);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let types = assert_optional_root(&mut context, &parsed, assignment, left, read);
        assert_replay(&mut context, &parsed, &types, &[left, read]);
    }
}

#[test]
fn nonoptional_top_level_declaration_still_reports_an_uninitialized_read() {
    let source = concat!("let value: string;\n", "const bad: string = value;\n");
    let parsed = parse_source_file(source);
    let (declaration, name, annotation, _) = variable(&parsed, "value", 0);
    let read = variable(&parsed, "bad", 0).3.unwrap();
    for first in [None, Some(read)] {
        let mut context = checked_context(&parsed, first);
        assert_uninitialized(&context, read);
        let string = string_annotation_type(&context, &parsed, declaration, annotation);
        assert_eq!(context.type_to_string(string).unwrap(), "string");
        assert_eq!(context.get_type_at_location(read), Ok(string));
        let symbol = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
        for node in [name, read] {
            assert_eq!(context.get_symbol_at_location(node), Ok(Some(symbol)));
        }
        assert_replay(
            &mut context,
            &parsed,
            &[(annotation, string), (read, string)],
            &[name, read],
        );
    }
}

#[test]
fn optional_top_level_allowance_does_not_apply_to_a_shadowed_local() {
    let source = concat!(
        "let value: string | undefined;\n",
        "value ??= 'fallback';\n",
        "const good: string = value;\n",
        "function scoped(): string {\n",
        "  let value: string;\n",
        "  return value;\n",
        "}\n",
    );
    let parsed = parse_source_file(source);
    let (assignment, left, read) = optional_nodes(source, &parsed);
    let (local, local_name, local_annotation, _) = variable(&parsed, "value", 1);
    let local_read = parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::ReturnStatement(return_) = &record.data else {
                return None;
            };
            return_
                .expression
                .map(|node| NodeRef::new(parsed.arena.id(), FILE, node))
        })
        .unwrap();
    for first in [None, Some(assignment), Some(local_read)] {
        let mut context = checked_context(&parsed, first);
        assert_uninitialized(&context, local_read);
        let mut types =
            assert_optional_root(&mut context, &parsed, assignment, left, read).to_vec();
        let string = string_annotation_type(&context, &parsed, local, local_annotation);
        assert_eq!(context.get_type_at_location(local_read), Ok(string));
        assert_eq!(context.type_to_string(string).unwrap(), "string");
        let bound = context.file(FILE).unwrap().1;
        let outer_symbol = bound.symbol(variable(&parsed, "value", 0).0).unwrap();
        let local_symbol = bound.symbol(local).unwrap();
        assert_ne!(outer_symbol, local_symbol);
        for node in [local_name, local_read] {
            assert_eq!(context.get_symbol_at_location(node), Ok(Some(local_symbol)));
        }
        types.extend([(local_annotation, string), (local_read, string)]);
        assert_replay(
            &mut context,
            &parsed,
            &types,
            &[left, read, local_name, local_read],
        );
    }
}

#[test]
fn parenthesized_top_level_annotations_preserve_read_checks() {
    let inner_annotation = |parsed: &ParseResult, declaration: NodeRef, annotation: NodeRef| {
        let node = parsed.arena.get(annotation.node).unwrap();
        assert_eq!(node.kind, SyntaxKind::ParenthesizedType);
        assert_eq!(node.parent, Some(declaration.node));
        let NodeData::ParenthesizedTypeNode(parenthesized) = &node.data else {
            panic!("expected the actual parenthesized annotation");
        };
        let inner = NodeRef::new(parsed.arena.id(), FILE, parenthesized.type_);
        assert_eq!(
            parsed.arena.get(inner.node).unwrap().parent,
            Some(annotation.node),
        );
        inner
    };

    let source = concat!(
        "let value: (string | undefined);\n",
        "value ??= 'fallback';\n",
        "const good: string = value;\n",
    );
    let parsed = parse_source_file(source);
    let (declaration, name, annotation, _) = variable(&parsed, "value", 0);
    let (good, _, string_annotation, _) = variable(&parsed, "good", 0);
    let inner = inner_annotation(&parsed, declaration, annotation);
    assert_eq!(
        parsed.arena.get(inner.node).unwrap().kind,
        SyntaxKind::UnionType
    );
    let (assignment, left, read) = optional_nodes(source, &parsed);
    for first in [None, Some(assignment), Some(read)] {
        let mut context = checked_context(&parsed, first);
        assert!(
            context.diagnostics().is_empty(),
            "{:?}",
            context.diagnostics()
        );
        let declared = resolved_annotation(&context, inner);
        let string = string_annotation_type(&context, &parsed, good, string_annotation);
        assert_ne!(declared, string);
        assert_eq!(
            context.type_to_string(declared).unwrap(),
            "string | undefined"
        );
        let types = [
            (annotation, declared),
            (inner, declared),
            (string_annotation, string),
            (assignment, string),
            (left, declared),
            (read, string),
        ];
        for (node, type_) in types {
            assert_eq!(context.get_type_at_location(node), Ok(type_));
        }
        let symbol = context.file(FILE).unwrap().1.symbol(declaration).unwrap();
        for node in [name, left, read] {
            assert_eq!(context.get_symbol_at_location(node), Ok(Some(symbol)));
        }
        let graph = context.file(FILE).unwrap().1.flow_graph();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());
        assert_eq!(
            graph
                .nodes()
                .iter()
                .filter(|flow| {
                    flow.flags.contains(FlowFlags::ASSIGNMENT)
                        && flow.payload == Some(FlowNodePayload::Ast(left))
                })
                .count(),
            1,
        );
        assert_replay(&mut context, &parsed, &types, &[name, left, read]);
    }

    let source = concat!(
        "let value: (null);\n",
        "const bad: null = value;\n",
        "let assigned: (null) = null;\n",
        "const good: null = assigned;\n",
    );
    let parsed = parse_source_file(source);
    let (declaration, name, annotation, _) = variable(&parsed, "value", 0);
    let (assigned, assigned_name, assigned_annotation, _) = variable(&parsed, "assigned", 0);
    let read = variable(&parsed, "bad", 0).3.unwrap();
    let assigned_read = variable(&parsed, "good", 0).3.unwrap();
    for (declaration, annotation) in [(declaration, annotation), (assigned, assigned_annotation)] {
        let inner = inner_annotation(&parsed, declaration, annotation);
        let node = parsed.arena.get(inner.node).unwrap();
        assert_eq!(node.kind, SyntaxKind::LiteralType);
        let NodeData::LiteralTypeNode(literal) = &node.data else {
            panic!("expected the actual null annotation");
        };
        let literal = parsed.arena.get(literal.literal).unwrap();
        assert_eq!(literal.kind, SyntaxKind::NullKeyword);
        assert_eq!(literal.parent, Some(inner.node));
        assert_eq!(literal.range, node.range);
        assert!(matches!(literal.data, NodeData::KeywordExpression(_)));
    }
    for first in [None, Some(read), Some(assigned_read)] {
        let mut context = checked_context(&parsed, first);
        assert_uninitialized(&context, read);
        let null = context.store().intrinsic_bootstrap().unwrap().null_type;
        let types = [
            (annotation, null),
            (assigned_annotation, null),
            (read, null),
            (assigned_read, null),
        ];
        for (node, type_) in types {
            assert_eq!(context.get_type_at_location(node), Ok(type_));
        }
        let bound = context.file(FILE).unwrap().1;
        let symbol = bound.symbol(declaration).unwrap();
        let assigned_symbol = bound.symbol(assigned).unwrap();
        assert_ne!(symbol, assigned_symbol);
        for (node, expected) in [
            (name, symbol),
            (read, symbol),
            (assigned_name, assigned_symbol),
            (assigned_read, assigned_symbol),
        ] {
            assert_eq!(context.get_symbol_at_location(node), Ok(Some(expected)));
        }
        let graph = context.file(FILE).unwrap().1.flow_graph();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());
        assert_replay(
            &mut context,
            &parsed,
            &types,
            &[name, read, assigned_name, assigned_read],
        );
    }
}
