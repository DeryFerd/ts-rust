use ts_ast::{FileId, FlowFlags, FlowNodePayload, NodeData, NodeRef, SyntaxKind};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_checker::semantic::{
    CanonicalCheckerContext, CanonicalCheckerOptions, IntrinsicBootstrapOptions,
};
use ts_parser::{ParseResult, parse_source_file};

const FILE: FileId = FileId::new(202_1101);

fn context(parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new(
                EscapedName::source("\"/project/nested-logical-assignment.ts\""),
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
    CanonicalCheckerContext::new(
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
    .unwrap()
}

fn node_text<'a>(source: &'a str, parsed: &ParseResult, node: NodeRef) -> &'a str {
    let range = parsed.arena.get(node.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn expression(source: &str, parsed: &ParseResult, text: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let node = NodeRef::new(parsed.arena.id(), FILE, id);
            (record.kind == SyntaxKind::BinaryExpression && node_text(source, parsed, node) == text)
                .then_some(node)
        })
        .unwrap_or_else(|| panic!("missing expression {text:?}"))
}

fn initializer(parsed: &ParseResult, expected: &str) -> NodeRef {
    parsed
        .arena
        .iter()
        .find_map(|(_, record)| {
            let NodeData::VariableDeclaration(variable) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(variable.name)?.data else {
                return None;
            };
            (name.text == expected)
                .then_some(variable.initializer)
                .flatten()
                .map(|id| NodeRef::new(parsed.arena.id(), FILE, id))
        })
        .unwrap_or_else(|| panic!("missing initializer {expected}"))
}

fn parameter(parsed: &ParseResult, expected: &str) -> (NodeRef, NodeRef, NodeRef) {
    parsed
        .arena
        .iter()
        .find_map(|(id, record)| {
            let NodeData::ParameterDeclaration(parameter) = &record.data else {
                return None;
            };
            let NodeData::Identifier(name) = &parsed.arena.get(parameter.name)?.data else {
                return None;
            };
            (name.text == expected).then(|| {
                (
                    NodeRef::new(parsed.arena.id(), FILE, id),
                    NodeRef::new(parsed.arena.id(), FILE, parameter.name),
                    NodeRef::new(parsed.arena.id(), FILE, parameter.type_.unwrap()),
                )
            })
        })
        .unwrap_or_else(|| panic!("missing parameter {expected}"))
}

fn left(parsed: &ParseResult, expression: NodeRef) -> NodeRef {
    let NodeData::BinaryExpression(binary) = &parsed.arena.get(expression.node).unwrap().data
    else {
        panic!("expected a binary expression");
    };
    NodeRef::new(parsed.arena.id(), FILE, binary.left)
}

// Inspect the real binder edges, including the edge that must precede the outer write.
fn assert_assignment_join(
    context: &CanonicalCheckerContext<'_>,
    parsed: &ParseResult,
    outer: NodeRef,
    inner: NodeRef,
    rhs_entry_flag: FlowFlags,
) {
    let graph = context.file(FILE).unwrap().1.flow_graph();
    assert!(graph.is_complete(), "{:?}", graph.unsupported());
    let outer_left = left(parsed, outer);
    let inner_left = left(parsed, inner);
    let entry = graph
        .nodes()
        .get(graph.flow_at(inner_left).unwrap())
        .unwrap();
    assert!(entry.flags.contains(rhs_entry_flag));
    assert_eq!(entry.payload, Some(FlowNodePayload::Ast(outer_left)));

    let writes = [outer_left, inner_left].map(|target| {
        let writes = graph
            .nodes()
            .iter()
            .filter(|flow| {
                flow.flags.contains(FlowFlags::ASSIGNMENT)
                    && flow.payload == Some(FlowNodePayload::Ast(target))
            })
            .collect::<Vec<_>>();
        assert_eq!(writes.len(), 1, "one real write per target");
        writes[0]
    });
    let join = graph.nodes().get(writes[0].antecedent.unwrap()).unwrap();
    assert!(join.flags.contains(FlowFlags::BRANCH_LABEL));
    assert!(join.antecedents.iter().any(|&edge| {
        let flow = graph.nodes().get(edge).unwrap();
        flow.flags.contains(FlowFlags::TRUE_CONDITION)
            && flow.payload == Some(FlowNodePayload::Ast(inner_left))
    }));
    assert!(join.antecedents.iter().any(|&edge| {
        let flow = graph.nodes().get(edge).unwrap();
        flow.payload == Some(FlowNodePayload::Ast(inner))
            && flow.antecedent.and_then(|entry| graph.nodes().get(entry)) == Some(writes[1])
    }));
}

// Compare owned semantic state, not lazy relation-cache allocation counts.
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

fn assert_source_orders(source: &str, outer_text: &str, outer_writes: bool) {
    let parsed = parse_source_file(source);
    let outer = expression(source, &parsed, outer_text);
    let inner = expression(source, &parsed, "side ??= 1");
    let good = initializer(&parsed, "good");
    let optional = initializer(&parsed, "stillOptional");
    let bad = initializer(&parsed, "bad");
    let (value_decl, value_name, optional_annotation) = parameter(&parsed, "value");
    let (side_decl, side_name, _) = parameter(&parsed, "side");
    let number_annotation = parsed
        .arena
        .iter()
        .find_map(|(id, node)| {
            (node.kind == SyntaxKind::NumberKeyword).then_some(NodeRef::new(
                parsed.arena.id(),
                FILE,
                id,
            ))
        })
        .unwrap();

    for first in [None, Some(inner), Some(bad)] {
        let mut context = context(&parsed);
        let first_type = first.map(|node| (node, context.get_type_at_location(node).unwrap()));
        context.check_source_file(FILE).unwrap();
        if let Some((node, type_)) = first_type {
            assert_eq!(context.get_type_at_location(node), Ok(type_));
        }
        let diagnostics = context.diagnostics().as_slice();
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        let diagnostic = &diagnostics[0];
        assert_eq!(diagnostic.diagnostic.code(), 2322);
        assert_eq!(
            diagnostic.diagnostic.arguments,
            ["number | undefined", "number"]
        );
        assert!(diagnostic.range_override.is_none());
        assert!(diagnostic.related_information.is_empty());
        let diagnostic_node = diagnostic.node.unwrap();
        assert_eq!(node_text(source, &parsed, diagnostic_node), "bad");
        let range = parsed.arena.get(diagnostic_node.node).unwrap().range;
        assert_eq!(
            usize::try_from(range.start.get()).unwrap(),
            source.rfind("bad").unwrap()
        );
        assert_eq!(range.end.get() - range.start.get(), 3);

        let number = context.get_type_at_location(number_annotation).unwrap();
        let optional_type = context.get_type_at_location(optional_annotation).unwrap();
        assert_eq!(context.type_to_string(number).unwrap(), "number");
        assert_eq!(
            context.type_to_string(optional_type).unwrap(),
            "number | undefined"
        );
        let expected = [
            (outer, number),
            (inner, number),
            (good, if outer_writes { number } else { optional_type }),
            (optional, optional_type),
            (bad, optional_type),
        ];
        for (node, type_) in expected {
            assert_eq!(context.get_type_at_location(node), Ok(type_));
        }

        let bound = context.file(FILE).unwrap().1;
        let value_symbol = bound.symbol(value_decl).unwrap();
        let side_symbol = bound.symbol(side_decl).unwrap();
        assert_ne!(value_symbol, side_symbol);
        let symbols = [
            (value_name, value_symbol),
            (left(&parsed, outer), value_symbol),
            (good, value_symbol),
            (side_name, side_symbol),
            (left(&parsed, inner), side_symbol),
            (optional, side_symbol),
            (bad, side_symbol),
        ];
        for (node, symbol) in symbols {
            assert_eq!(context.get_symbol_at_location(node), Ok(Some(symbol)));
        }

        let graph = context.file(FILE).unwrap().1.flow_graph();
        assert!(graph.is_complete(), "{:?}", graph.unsupported());
        if outer_writes {
            assert_assignment_join(&context, &parsed, outer, inner, FlowFlags::FALSE_CONDITION);
        } else {
            let outer_left = left(&parsed, outer);
            assert!(!graph.nodes().iter().any(|flow| {
                flow.flags.contains(FlowFlags::ASSIGNMENT)
                    && flow.payload == Some(FlowNodePayload::Ast(outer_left))
            }));
            let entry = graph
                .nodes()
                .get(graph.flow_at(left(&parsed, inner)).unwrap())
                .unwrap();
            assert!(entry.flags.contains(FlowFlags::FALSE_CONDITION));
            assert_eq!(entry.payload, Some(FlowNodePayload::Ast(outer_left)));
        }

        let before = semantic_state(&context, &parsed);
        context.check_source_file(FILE).unwrap();
        assert_eq!(semantic_state(&context, &parsed), before);
        context.recheck_source_file(FILE).unwrap();
        for (node, type_) in expected {
            assert_eq!(context.get_type_at_location(node), Ok(type_));
        }
        for (node, symbol) in symbols {
            assert_eq!(context.get_symbol_at_location(node), Ok(Some(symbol)));
        }
        assert_eq!(semantic_state(&context, &parsed), before);
    }
}

#[test]
fn logical_assignment_parents_join_the_nested_rhs_before_writing() {
    for (operator, entry_flag) in [
        ("??=", FlowFlags::FALSE_CONDITION),
        ("||=", FlowFlags::FALSE_CONDITION),
        ("&&=", FlowFlags::TRUE_CONDITION),
    ] {
        let source = format!(
            "function nested(value: number | undefined, side: number | undefined): void {{\n  value {operator} ((side ??= 1));\n}}\n"
        );
        let parsed = parse_source_file(&source);
        let outer = expression(
            &source,
            &parsed,
            &format!("value {operator} ((side ??= 1))"),
        );
        let inner = expression(&source, &parsed, "side ??= 1");
        // This control checks all three binder operators, not checker support for ||= or &&=.
        let context = context(&parsed);
        assert_assignment_join(&context, &parsed, outer, inner, entry_flag);
    }
}

#[test]
fn nested_nullish_assignment_keeps_outer_write_and_optional_rhs() {
    // Keep the original failure-71 TypeScript unchanged in this focused control.
    let source = concat!(
        "function conditional(value: number | undefined, side: number | undefined): void {\n",
        "  value ??= (side ??= 1);\n",
        "  const good: number = value;\n",
        "  const stillOptional: number | undefined = side;\n",
        "  const bad: number = side;\n",
        "}\n",
    );
    assert_source_orders(source, "value ??= (side ??= 1)", true);
}

#[test]
fn nonassignment_coalescing_parent_keeps_both_later_reads_optional() {
    let source = concat!(
        "function conditional(value: number | undefined, side: number | undefined): void {\n",
        "  value ?? ((side ??= 1));\n",
        "  const good: number | undefined = value;\n",
        "  const stillOptional: number | undefined = side;\n",
        "  const bad: number = side;\n",
        "}\n",
    );
    assert_source_orders(source, "value ?? ((side ??= 1))", false);
}
