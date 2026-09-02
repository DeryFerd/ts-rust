use std::collections::HashSet;

use ts_ast::{
    FileId, FlowFlags, FlowNode, FlowNodeArena, FlowNodePayload, FlowRef, NodeData, NodeId,
    NodeRef, SyntaxKind,
};
use ts_binder::{
    CanonicalBinder, CanonicalModuleState, CanonicalSourceFileFacts, CanonicalSourceLanguage,
    EscapedName,
};
use ts_parser::{ParseResult, parse_source_file};

use super::{
    FLOW_DEPTH_LIMIT, SourceFlowActivePath, SourceFlowAssignment, SourceFlowCondition,
    SourceFlowCoverage, SourceFlowEffects, SourceFlowError, SourceFlowInvariant, SourceFlowPlan,
    label_antecedents, validate_direct_call,
};

const FILE: FileId = FileId::new(205_710);

fn node(parsed: &ParseResult, id: NodeId) -> NodeRef {
    NodeRef::new(parsed.arena.id(), FILE, id)
}

fn text<'a>(parsed: &ParseResult, source: &'a str, location: NodeRef) -> &'a str {
    assert_eq!(location.arena, parsed.arena.id());
    assert_eq!(location.file, FILE);
    let range = parsed.arena.get(location.node).unwrap().range;
    &source[usize::try_from(range.start.get()).unwrap()..usize::try_from(range.end.get()).unwrap()]
}

fn expression(parsed: &ParseResult, source: &str, kind: SyntaxKind, expected: &str) -> NodeRef {
    let matches = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            let location = node(parsed, id);
            (record.kind == kind && text(parsed, source, location) == expected).then_some(location)
        })
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1, "expected one {expected:?}");
    matches[0]
}

fn check_legal_preflight(source: &str, loop_names: &[&str], call_text: &str) {
    let parsed = parse_source_file(source);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut binder = CanonicalBinder::new();
    binder
        .bind_source_file_with_facts(
            &parsed.arena,
            parsed.source_file,
            FILE,
            CanonicalSourceFileFacts::new_with_default_library(
                EscapedName::source("\"/project/counted-flow-preflight.ts\""),
                CanonicalSourceLanguage::TypeScript,
                false,
                false,
                CanonicalModuleState::External,
            )
            .with_always_strict(true),
        )
        .unwrap();
    binder
        .bind_typescript_declaration_slice(&parsed.arena, FILE)
        .unwrap();
    let bindings = binder.finish();
    let bound = bindings.file(FILE).unwrap();
    let graph = bound.flow_graph();
    let before = graph.clone();
    assert_eq!(bound.node_arena_id(), parsed.arena.id());
    assert_eq!(bound.node_arena_revision(), parsed.arena.revision());
    assert_eq!(bound.file_id(), FILE);

    let functions = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| match &record.data {
            NodeData::FunctionDeclaration(function) if function.body.is_some() => {
                Some(node(&parsed, id))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let [container] = functions.as_slice() else {
        panic!("expected one function body");
    };
    let call = expression(&parsed, source, SyntaxKind::CallExpression, call_text);
    let mut effects = SourceFlowEffects::default();
    effects.calls.insert(
        call,
        validate_direct_call(&parsed.arena, bound, *container, call).unwrap(),
    );

    let declarations = loop_names
        .iter()
        .map(|&name| {
            let matches = parsed
                .arena
                .iter()
                .filter_map(|(id, record)| {
                    let NodeData::VariableDeclaration(declaration) = &record.data else {
                        return None;
                    };
                    (text(&parsed, source, node(&parsed, declaration.name)) == name)
                        .then_some(node(&parsed, id))
                })
                .collect::<Vec<_>>();
            assert_eq!(matches.len(), 1, "expected one declaration of {name}");
            let declaration = matches[0];
            assert_eq!(bound.container(declaration), Some(*container));
            (name, declaration, bound.symbol(declaration).unwrap())
        })
        .collect::<Vec<_>>();

    // Register the actual binder assignment payloads and their real declaration owners.
    let assignments = graph
        .nodes()
        .iter()
        .filter(|flow| flow.flags.contains(FlowFlags::ASSIGNMENT))
        .map(|flow| {
            let Some(FlowNodePayload::Ast(target)) = &flow.payload else {
                panic!("expected an AST assignment payload");
            };
            let target = *target;
            let (_, declaration, symbol) = declarations
                .iter()
                .find(|(name, declaration, _)| {
                    *declaration == target || *name == text(&parsed, source, target)
                })
                .expect("expected a counted-loop assignment");
            assert_eq!(bound.container(target), Some(*container));
            assert_eq!(
                effects.assignment_declarations.insert(target, *declaration),
                None
            );
            SourceFlowAssignment {
                declaration: target,
                symbol: *symbol,
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(assignments.len(), loop_names.len() * 2);

    let mut points = Vec::new();
    let mut conditions = Vec::new();
    let mut entries = Vec::new();
    for &name in loop_names {
        let condition = expression(
            &parsed,
            source,
            SyntaxKind::BinaryExpression,
            &format!("{name} < limit"),
        );
        conditions.push(SourceFlowCondition::Unchanged(condition));
        let header = bound.flow_at(condition).unwrap();
        let header_node = graph.nodes().get(header).unwrap();
        assert!(header_node.flags.contains(FlowFlags::LOOP_LABEL));
        entries.push(header);

        let update = expression(
            &parsed,
            source,
            SyntaxKind::PostfixUnaryExpression,
            &format!("{name}++"),
        );
        let NodeData::PostfixUnaryExpression(unary) = &parsed.arena.get(update.node).unwrap().data
        else {
            panic!("expected the parsed incrementor");
        };
        let target = node(&parsed, unary.operand);
        points.push(target);
        let update_flows = header_node
            .antecedents
            .iter()
            .copied()
            .filter(|&flow| {
                graph.nodes().get(flow).unwrap().payload == Some(FlowNodePayload::Ast(target))
            })
            .collect::<Vec<_>>();
        let [update_flow] = update_flows.as_slice() else {
            panic!("expected one actual incrementor backedge");
        };
        assert!(
            graph
                .nodes()
                .get(*update_flow)
                .unwrap()
                .flags
                .contains(FlowFlags::ASSIGNMENT)
        );
        entries.push(*update_flow);
    }
    let call_entry = bound.flow_at(*points.last().unwrap()).unwrap();
    let call_node = graph.nodes().get(call_entry).unwrap();
    assert!(call_node.flags.contains(FlowFlags::CALL));
    assert_eq!(call_node.payload, Some(FlowNodePayload::Ast(call)));
    entries.push(call_entry);

    let returns = parsed
        .arena
        .iter()
        .filter_map(|(id, record)| {
            (record.kind == SyntaxKind::Identifier
                && record.parent.is_some_and(|parent| {
                    parsed.arena.get(parent).unwrap().kind == SyntaxKind::ReturnStatement
                }))
            .then_some(node(&parsed, id))
        })
        .collect::<Vec<_>>();
    let [returned] = returns.as_slice() else {
        panic!("expected one returned identifier");
    };
    assert_eq!(text(&parsed, source, *returned), "limit");
    points.push(*returned);

    // This is the full production structural preflight, including plan coverage checks.
    let plan = SourceFlowPlan::preflight_with_effects(
        bound,
        *container,
        None,
        points,
        conditions,
        assignments,
        effects,
    )
    .unwrap();
    for entry in entries {
        assert!(entry.is_for(parsed.arena.id(), FILE));
        let mut validated = HashSet::new();
        let mut active = SourceFlowActivePath::default();
        let mut coverage = SourceFlowCoverage::default();
        plan.validate_flow(bound, entry, 0, &mut validated, &mut active, &mut coverage)
            .unwrap();
        assert!(validated.contains(&entry));
        assert!(coverage.calls.contains(&call));
        assert!(active.members.is_empty());
        assert!(active.nodes.is_empty());
    }
    plan.validate_flow_paths(bound).unwrap();
    let depth_error = plan.validate_flow(
        bound,
        call_entry,
        FLOW_DEPTH_LIMIT + 1,
        &mut HashSet::new(),
        &mut SourceFlowActivePath::default(),
        &mut SourceFlowCoverage::default(),
    );
    assert!(
        matches!(depth_error, Err(SourceFlowError::Invariant(SourceFlowInvariant::DepthLimit(flow))) if flow == call_entry)
    );
    assert_eq!(bound.flow_graph(), &before);
}

#[test]
fn counted_loop_preflight_accepts_call_update_and_header_entries() {
    let source = r#"declare function visit(index: number): void;
export function count(limit: number): number {
  for (let i = 0; i < limit; i++) {
    visit(i);
  }
  return limit;
}
"#;
    check_legal_preflight(source, &["i"], "visit(i)");
}

#[test]
fn nested_counted_loop_preflight_keeps_outer_and_inner_headers() {
    let source = r#"declare function visit(outer: number, inner: number): void;
export function count(limit: number): number {
  for (let i = 0; i < limit; i++) {
    for (let j = 0; j < limit; j++) {
      visit(i, j);
    }
  }
  return limit;
}
"#;
    check_legal_preflight(source, &["i", "j"], "visit(i, j)");
}

fn arena_with_start() -> (ParseResult, FlowNodeArena, FlowRef) {
    let parsed = parse_source_file("function build(): void {}\n");
    assert!(parsed.diagnostics.is_empty());
    let mut nodes = FlowNodeArena::new(parsed.arena.id(), FILE);
    let start = nodes.alloc(FlowNode::new(FlowFlags::START)).unwrap();
    (parsed, nodes, start)
}

fn active_segment(
    nodes: &FlowNodeArena,
    path: &[FlowRef],
    repeated: FlowRef,
) -> SourceFlowActivePath {
    let members = path.iter().copied().collect::<HashSet<_>>();
    assert_eq!(members.len(), path.len());
    for (&flow, next) in path
        .iter()
        .zip(path.iter().copied().skip(1).chain([repeated]))
    {
        assert!(flow.is_for(nodes.node_arena(), nodes.file()));
        let node = nodes.get(flow).unwrap();
        assert!(label_antecedents(flow, node).unwrap().contains(&next));
    }
    SourceFlowActivePath {
        members,
        nodes: path.to_vec(),
    }
}

fn assert_cycle(nodes: &FlowNodeArena, path: &[FlowRef], repeated: FlowRef) {
    let active = active_segment(nodes, path, repeated);
    let result = active.validate_cycle(nodes, repeated);
    assert!(
        matches!(&result, Err(SourceFlowError::Invariant(SourceFlowInvariant::Cycle(flow))) if *flow == repeated),
        "{result:?}"
    );
}

#[test]
fn cycle_classifier_rejects_self_cycle_without_loop_label() {
    let (_parsed, mut nodes, start) = arena_with_start();
    let branch = nodes.alloc(FlowNode::new(FlowFlags::BRANCH_LABEL)).unwrap();
    nodes
        .replace_antecedents(branch, vec![start, branch])
        .unwrap();
    assert_cycle(&nodes, &[branch], branch);
}

#[test]
fn cycle_classifier_rejects_two_node_cycle_without_loop_label() {
    let (_parsed, mut nodes, start) = arena_with_start();
    let first = nodes.alloc(FlowNode::new(FlowFlags::BRANCH_LABEL)).unwrap();
    let second = nodes.alloc(FlowNode::new(FlowFlags::BRANCH_LABEL)).unwrap();
    nodes
        .replace_antecedents(first, vec![start, second])
        .unwrap();
    nodes
        .replace_antecedents(second, vec![start, first])
        .unwrap();
    assert_cycle(&nodes, &[first, second], first);
}

#[test]
fn cycle_classifier_rejects_inner_cycle_under_unrelated_loop() {
    let (_parsed, mut nodes, start) = arena_with_start();
    let outer = nodes.alloc(FlowNode::new(FlowFlags::LOOP_LABEL)).unwrap();
    let outer_backedge = nodes.alloc(FlowNode::new(FlowFlags::BRANCH_LABEL)).unwrap();
    let first = nodes.alloc(FlowNode::new(FlowFlags::BRANCH_LABEL)).unwrap();
    let second = nodes.alloc(FlowNode::new(FlowFlags::BRANCH_LABEL)).unwrap();
    nodes
        .replace_antecedents(outer, vec![start, first, outer_backedge])
        .unwrap();
    nodes
        .replace_antecedents(outer_backedge, vec![start, outer])
        .unwrap();
    nodes
        .replace_antecedents(first, vec![start, second])
        .unwrap();
    nodes
        .replace_antecedents(second, vec![start, first])
        .unwrap();
    assert_cycle(&nodes, &[outer, first, second], first);
}

#[test]
fn cycle_classifier_preserves_node_and_label_errors() {
    let (_parsed, mut nodes, start) = arena_with_start();
    let label = nodes.alloc(FlowNode::new(FlowFlags::LOOP_LABEL)).unwrap();
    let active = SourceFlowActivePath {
        members: HashSet::from([label]),
        nodes: vec![label],
    };
    assert!(
        matches!(active.validate_cycle(&nodes, label), Err(SourceFlowError::Invariant(SourceFlowInvariant::InvalidAntecedents(flow))) if flow == label)
    );
    nodes
        .replace_antecedents(label, vec![start, start])
        .unwrap();
    assert!(
        matches!(active.validate_cycle(&nodes, label), Err(SourceFlowError::Invariant(SourceFlowInvariant::InvalidAntecedents(flow))) if flow == label)
    );
    nodes.get_mut(label).unwrap().flags = FlowFlags::LOOP_LABEL | FlowFlags::CALL;
    assert!(
        matches!(active.validate_cycle(&nodes, label), Err(SourceFlowError::Invariant(SourceFlowInvariant::InvalidFlowFlags { flow, .. })) if flow == label)
    );

    let earlier = nodes.clone();
    let absent = nodes.alloc(FlowNode::new(FlowFlags::BRANCH_LABEL)).unwrap();
    let active = SourceFlowActivePath {
        members: HashSet::from([absent]),
        nodes: vec![absent],
    };
    assert!(earlier.get(absent).is_none());
    assert!(
        matches!(active.validate_cycle(&earlier, absent), Err(SourceFlowError::Invariant(SourceFlowInvariant::MissingFlowNode(flow))) if flow == absent)
    );

    let foreign_parsed = parse_source_file("function other(): void {}\n");
    assert_ne!(foreign_parsed.arena.id(), nodes.node_arena());
    let mut foreign_nodes = FlowNodeArena::new(foreign_parsed.arena.id(), FILE);
    let foreign = foreign_nodes
        .alloc(FlowNode::new(FlowFlags::BRANCH_LABEL))
        .unwrap();
    let active = SourceFlowActivePath {
        members: HashSet::from([foreign]),
        nodes: vec![foreign],
    };
    assert!(
        matches!(active.validate_cycle(&nodes, foreign), Err(SourceFlowError::Invariant(SourceFlowInvariant::ForeignFlow(flow))) if flow == foreign)
    );
    let mut other_file_nodes = FlowNodeArena::new(nodes.node_arena(), FileId::new(205_711));
    let other_file = other_file_nodes
        .alloc(FlowNode::new(FlowFlags::BRANCH_LABEL))
        .unwrap();
    let active = SourceFlowActivePath {
        members: HashSet::from([other_file]),
        nodes: vec![other_file],
    };
    assert!(
        matches!(active.validate_cycle(&nodes, other_file), Err(SourceFlowError::Invariant(SourceFlowInvariant::ForeignFlow(flow))) if flow == other_file)
    );
}
