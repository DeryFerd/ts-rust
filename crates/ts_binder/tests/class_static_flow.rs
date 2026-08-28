use ts_ast::{
    FileId, FlowFlags, FlowNodeId, FlowNodePayload, FlowRef, NodeData, NodeRef, SyntaxKind,
};
use ts_binder::{BoundFile, CanonicalBinder, UnsupportedFlowKind, bind_source_file_in_file};
use ts_parser::{ParseResult, parse_source_file};

struct Fixture {
    parsed: ParseResult,
    binder: CanonicalBinder,
    file: FileId,
}

impl Fixture {
    fn new(source: &str) -> Self {
        let parsed = parse_source_file(source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(1);
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        Self {
            parsed,
            binder,
            file,
        }
    }

    fn bound(&self) -> &BoundFile {
        self.binder.file(self.file).unwrap()
    }

    fn nodes(&self, kind: SyntaxKind) -> Vec<NodeRef> {
        self.parsed
            .arena
            .iter()
            .filter_map(|(id, node)| {
                (node.kind == kind).then_some(NodeRef::new(self.parsed.arena.id(), self.file, id))
            })
            .collect()
    }

    fn node(&self, kind: SyntaxKind, source: &str) -> NodeRef {
        let text = self.parsed.arena.source_text().unwrap();
        self.nodes(kind)
            .into_iter()
            .find(|id| {
                let node = self.parsed.arena.get(id.node).unwrap();
                &text[node.range.start.get() as usize..node.range.end.get() as usize] == source
            })
            .unwrap_or_else(|| panic!("missing {kind:?}: {source}"))
    }

    fn mutation(&self, flags: FlowFlags, target: NodeRef) -> FlowRef {
        let graph = self.bound().flow_graph();
        let index = graph
            .nodes()
            .iter()
            .position(|node| {
                node.flags.contains(flags) && node.payload == Some(FlowNodePayload::Ast(target))
            })
            .unwrap_or_else(|| panic!("missing {flags:?} flow for {target:?}"));
        graph
            .nodes()
            .flow_ref(FlowNodeId(u32::try_from(index).unwrap()))
            .unwrap()
    }
}

#[test]
fn static_blocks_keep_outer_assignment_and_receiver_reference_identity() {
    let fixture = Fixture::new(concat!(
        "class C {} C.second = 456; ",
        "class D extends C { ",
        "static { observe(super.second); this.first = 1; } ",
        "static { this.first; this.second = 2; } ",
        "} after;",
    ));
    let bound = fixture.bound();
    let graph = bound.flow_graph();
    assert!(graph.is_complete(), "{:?}", graph.unsupported());
    let blocks = fixture.nodes(SyntaxKind::ClassStaticBlockDeclaration);
    let external = fixture.node(SyntaxKind::PropertyAccessExpression, "C.second");
    let inherited_read = fixture.node(SyntaxKind::PropertyAccessExpression, "super.second");
    let first_write = fixture.node(SyntaxKind::PropertyAccessExpression, "this.first");
    let second_write = fixture.node(SyntaxKind::PropertyAccessExpression, "this.second");
    let call = fixture.node(SyntaxKind::CallExpression, "observe(super.second)");
    let after = fixture.node(SyntaxKind::ExpressionStatement, "after;");
    let external_flow = fixture.mutation(FlowFlags::ASSIGNMENT, external);
    let call_flow = fixture.mutation(FlowFlags::CALL, call);
    let first_flow = fixture.mutation(FlowFlags::ASSIGNMENT, first_write);
    let second_flow = fixture.mutation(FlowFlags::ASSIGNMENT, second_write);

    assert_eq!(graph.container_start(blocks[0]), Some(external_flow));
    assert_eq!(bound.flow_container(external), Some(bound.source_file()));
    assert_eq!(bound.flow_container(inherited_read), Some(blocks[0]));
    assert_eq!(bound.flow_at(inherited_read), Some(external_flow));
    let NodeData::PropertyAccessExpression(read) =
        &fixture.parsed.arena.get(inherited_read.node).unwrap().data
    else {
        panic!("expected property access");
    };
    let receiver = NodeRef::new(fixture.parsed.arena.id(), fixture.file, read.expression);
    assert_eq!(
        fixture.parsed.arena.get(receiver.node).unwrap().kind,
        SyntaxKind::SuperKeyword
    );
    assert_eq!(bound.flow_at(receiver), Some(external_flow));
    assert_eq!(bound.flow_container(receiver), Some(blocks[0]));
    assert_eq!(
        graph.nodes().get(call_flow).unwrap().antecedent,
        Some(external_flow)
    );
    assert_eq!(
        graph.nodes().get(first_flow).unwrap().antecedent,
        Some(call_flow)
    );
    assert_eq!(graph.container_end(blocks[0]), Some(first_flow));
    assert_eq!(graph.container_return(blocks[0]), Some(first_flow));
    assert_eq!(graph.container_start(blocks[1]), Some(first_flow));
    assert_eq!(
        graph.nodes().get(second_flow).unwrap().antecedent,
        Some(first_flow)
    );
    assert_eq!(graph.container_end(blocks[1]), Some(second_flow));
    assert_eq!(graph.container_return(blocks[1]), Some(second_flow));
    assert_eq!(bound.flow_at(after), Some(second_flow));
    assert_eq!(graph.container_end(bound.source_file()), Some(second_flow));
    assert_eq!(
        graph
            .nodes()
            .iter()
            .filter(|node| node.flags.contains(FlowFlags::START))
            .count(),
        1
    );
    assert!(!graph.nodes().iter().any(|node| {
        node.flags.contains(FlowFlags::ASSIGNMENT)
            && node.payload == Some(FlowNodePayload::Ast(inherited_read))
    }));
}

#[test]
fn constructors_and_methods_keep_separate_flow_from_static_blocks() {
    let fixture = Fixture::new(concat!(
        "class Base {} class Derived extends Base { ",
        "static { this.count = 1; } ",
        "constructor() { super(); this.value = 2; return; } ",
        "method() { this.other = 3; } ",
        "} after;",
    ));
    let bound = fixture.bound();
    let graph = bound.flow_graph();
    assert!(graph.is_complete(), "{:?}", graph.unsupported());
    let block = fixture.nodes(SyntaxKind::ClassStaticBlockDeclaration)[0];
    let constructor = fixture.nodes(SyntaxKind::Constructor)[0];
    let method = fixture.nodes(SyntaxKind::MethodDeclaration)[0];
    let static_assignment = fixture.mutation(
        FlowFlags::ASSIGNMENT,
        fixture.node(SyntaxKind::PropertyAccessExpression, "this.count"),
    );
    let instance_assignment = fixture.mutation(
        FlowFlags::ASSIGNMENT,
        fixture.node(SyntaxKind::PropertyAccessExpression, "this.value"),
    );
    let method_assignment = fixture.mutation(
        FlowFlags::ASSIGNMENT,
        fixture.node(SyntaxKind::PropertyAccessExpression, "this.other"),
    );
    let super_call = fixture.mutation(
        FlowFlags::CALL,
        fixture.node(SyntaxKind::CallExpression, "super()"),
    );
    let constructor_start = graph.container_start(constructor).unwrap();
    let method_start = graph.container_start(method).unwrap();
    assert!(
        graph
            .nodes()
            .get(constructor_start)
            .unwrap()
            .flags
            .contains(FlowFlags::START)
    );
    assert!(
        graph
            .nodes()
            .get(method_start)
            .unwrap()
            .flags
            .contains(FlowFlags::START)
    );
    assert_ne!(constructor_start, method_start);
    assert_ne!(graph.container_start(block), Some(constructor_start));
    assert_eq!(
        graph.nodes().get(super_call).unwrap().antecedent,
        Some(constructor_start)
    );
    assert_eq!(
        graph.nodes().get(instance_assignment).unwrap().antecedent,
        Some(super_call)
    );
    assert_eq!(
        graph.container_return(constructor),
        Some(instance_assignment)
    );
    assert_eq!(graph.container_end(constructor), None);
    assert_eq!(
        graph.nodes().get(method_assignment).unwrap().antecedent,
        Some(method_start)
    );
    assert_eq!(graph.container_end(method), Some(method_assignment));
    assert_eq!(graph.container_return(method), None);
    assert_eq!(graph.container_return(block), Some(static_assignment));
    assert_eq!(
        graph.container_end(bound.source_file()),
        Some(static_assignment)
    );
}

#[test]
fn conditional_static_blocks_keep_both_assignment_branches() {
    let fixture = Fixture::new(concat!(
        "flag ? class { static { left = 1; } } ",
        ": class { static { right = 2; } }; after;",
    ));
    let bound = fixture.bound();
    let graph = bound.flow_graph();
    assert!(graph.is_complete(), "{:?}", graph.unsupported());
    let left = fixture.mutation(
        FlowFlags::ASSIGNMENT,
        fixture.node(SyntaxKind::Identifier, "left"),
    );
    let right = fixture.mutation(
        FlowFlags::ASSIGNMENT,
        fixture.node(SyntaxKind::Identifier, "right"),
    );
    let blocks = fixture.nodes(SyntaxKind::ClassStaticBlockDeclaration);
    for (block, flag, assignment) in [
        (blocks[0], FlowFlags::TRUE_CONDITION, left),
        (blocks[1], FlowFlags::FALSE_CONDITION, right),
    ] {
        let start = graph.container_start(block).unwrap();
        assert!(graph.nodes().get(start).unwrap().flags.contains(flag));
        assert_eq!(
            graph.nodes().get(assignment).unwrap().antecedent,
            Some(start)
        );
        assert_eq!(graph.container_return(block), Some(assignment));
    }
    let after = fixture.node(SyntaxKind::ExpressionStatement, "after;");
    let joined = graph.nodes().get(bound.flow_at(after).unwrap()).unwrap();
    assert!(joined.flags.contains(FlowFlags::BRANCH_LABEL));
    assert_eq!(joined.antecedents, [left, right]);
}

#[test]
fn throwing_static_blocks_make_the_outer_flow_unreachable() {
    let fixture = Fixture::new(concat!(
        "class C { static { throw error; } ",
        "static { skipped(); } method() { inside; } } after;",
    ));
    let bound = fixture.bound();
    let graph = bound.flow_graph();
    assert!(graph.is_complete(), "{:?}", graph.unsupported());
    let blocks = fixture.nodes(SyntaxKind::ClassStaticBlockDeclaration);
    let unreachable = graph.nodes().unreachable();
    for block in &blocks {
        assert_eq!(graph.container_is_complete(*block), Some(true));
        assert_eq!(graph.container_end(*block), None);
        assert_eq!(graph.container_return(*block), Some(unreachable));
    }
    assert_eq!(graph.container_start(blocks[1]), Some(unreachable));
    assert_eq!(graph.container_end(bound.source_file()), Some(unreachable));
    for source in ["skipped();", "after;"] {
        let statement = fixture.node(SyntaxKind::ExpressionStatement, source);
        assert_eq!(graph.is_unreachable(statement), Some(true));
        assert_eq!(bound.flow_at(statement), None);
    }
    let method = fixture.nodes(SyntaxKind::MethodDeclaration)[0];
    let inside = fixture.node(SyntaxKind::ExpressionStatement, "inside;");
    assert_eq!(graph.container_is_complete(method), Some(true));
    assert_eq!(bound.flow_at(inside), graph.container_start(method));
}

#[test]
fn unreachable_static_blocks_do_not_start_independent_flow() {
    let fixture = Fixture::new(concat!(
        "function stop() { return; ",
        "class C { static { skipped = 1; } } } after;",
    ));
    let bound = fixture.bound();
    let graph = bound.flow_graph();
    assert!(graph.is_complete(), "{:?}", graph.unsupported());
    let block = fixture.nodes(SyntaxKind::ClassStaticBlockDeclaration)[0];
    let unreachable = graph.nodes().unreachable();
    assert_eq!(graph.container_start(block), Some(unreachable));
    assert_eq!(graph.container_return(block), Some(unreachable));
    assert_eq!(graph.container_end(block), None);
    assert!(
        !graph
            .nodes()
            .iter()
            .any(|node| node.flags.contains(FlowFlags::ASSIGNMENT))
    );
    let after = fixture.node(SyntaxKind::ExpressionStatement, "after;");
    assert_eq!(
        bound.flow_at(after),
        graph.container_start(bound.source_file())
    );
}

#[test]
fn unsupported_static_flow_invalidates_the_executing_outer_container() {
    let fixture = Fixture::new(concat!(
        "function run() { class C { ",
        "static { try { value = 1; } finally {} } ",
        "method() { inside; } } after; } outside;",
    ));
    let bound = fixture.bound();
    let graph = bound.flow_graph();
    let function = fixture.nodes(SyntaxKind::FunctionDeclaration)[0];
    let block = fixture.nodes(SyntaxKind::ClassStaticBlockDeclaration)[0];
    let method = fixture.nodes(SyntaxKind::MethodDeclaration)[0];
    assert_eq!(graph.container_is_complete(block), Some(false));
    assert_eq!(graph.container_is_complete(function), Some(false));
    assert_eq!(graph.container_is_complete(method), Some(true));
    assert_eq!(graph.container_is_complete(bound.source_file()), Some(true));
    assert_eq!(graph.container_start(block), None);
    assert_eq!(graph.container_end(block), None);
    assert_eq!(graph.container_return(block), None);
    assert_eq!(
        bound.flow_at(fixture.node(SyntaxKind::ExpressionStatement, "after;")),
        None
    );
    assert!(
        bound
            .flow_at(fixture.node(SyntaxKind::ExpressionStatement, "outside;"))
            .is_some()
    );
    assert!(graph.unsupported().iter().any(|boundary| {
        boundary.container == block && boundary.kind == UnsupportedFlowKind::TryStatement
    }));
    assert!(graph.unsupported().iter().any(|boundary| {
        boundary.container == function
            && boundary.kind == UnsupportedFlowKind::CrossContainerFlowEffects
    }));
}

#[test]
fn static_blocks_cannot_recover_an_incomplete_outer_flow() {
    let fixture = Fixture::new(concat!(
        "try {} finally {} ",
        "class C { static { value = 1; } method() { inside; } }",
    ));
    let bound = fixture.bound();
    let graph = bound.flow_graph();
    let block = fixture.nodes(SyntaxKind::ClassStaticBlockDeclaration)[0];
    let method = fixture.nodes(SyntaxKind::MethodDeclaration)[0];
    assert_eq!(
        graph.container_is_complete(bound.source_file()),
        Some(false)
    );
    assert_eq!(graph.container_is_complete(block), Some(false));
    assert_eq!(graph.container_start(block), None);
    assert_eq!(graph.container_end(block), None);
    assert_eq!(graph.container_return(block), None);
    assert_eq!(graph.container_is_complete(method), Some(true));
    assert!(
        bound
            .flow_at(fixture.node(SyntaxKind::ExpressionStatement, "inside;"))
            .is_some()
    );
}

#[test]
fn detached_functions_inside_static_blocks_keep_their_own_failure_boundary() {
    let fixture = Fixture::new(concat!(
        "class C { static { ",
        "function detached() { try {} finally {} } value = 1; ",
        "} } after;",
    ));
    let bound = fixture.bound();
    let graph = bound.flow_graph();
    let block = fixture.nodes(SyntaxKind::ClassStaticBlockDeclaration)[0];
    let function = fixture.nodes(SyntaxKind::FunctionDeclaration)[0];
    let assignment = fixture.mutation(
        FlowFlags::ASSIGNMENT,
        fixture.node(SyntaxKind::Identifier, "value"),
    );
    assert_eq!(graph.container_is_complete(function), Some(false));
    assert_eq!(graph.container_is_complete(block), Some(true));
    assert_eq!(graph.container_is_complete(bound.source_file()), Some(true));
    assert_eq!(graph.container_return(block), Some(assignment));
    assert_eq!(graph.container_end(bound.source_file()), Some(assignment));
    assert_eq!(graph.unsupported().len(), 1);
}

#[test]
fn static_blocks_restore_outer_loop_and_constructor_return_targets() {
    let fixture = Fixture::new(concat!(
        "class C { constructor() { ",
        "outer: while (flag) { ",
        "class D { static { inner: while (ready) { value = 1; break inner; } } } ",
        "continue outer; } this.value = 2; return; } }",
    ));
    let bound = fixture.bound();
    let graph = bound.flow_graph();
    assert!(graph.is_complete(), "{:?}", graph.unsupported());
    let block = fixture.nodes(SyntaxKind::ClassStaticBlockDeclaration)[0];
    let constructor = fixture.nodes(SyntaxKind::Constructor)[0];
    let jump = fixture.node(SyntaxKind::ContinueStatement, "continue outer;");
    assert_eq!(bound.flow_container(jump), Some(constructor));
    assert_eq!(bound.flow_at(jump), graph.container_return(block));
    let outer_condition = fixture.node(SyntaxKind::Identifier, "flag");
    let outer_loop = graph
        .nodes()
        .get(bound.flow_at(outer_condition).unwrap())
        .unwrap();
    assert!(outer_loop.flags.contains(FlowFlags::LOOP_LABEL));
    assert!(
        outer_loop
            .antecedents
            .contains(&bound.flow_at(jump).unwrap())
    );
    let assignment = fixture.mutation(
        FlowFlags::ASSIGNMENT,
        fixture.node(SyntaxKind::PropertyAccessExpression, "this.value"),
    );
    assert_eq!(graph.container_return(constructor), Some(assignment));
    assert_eq!(graph.container_end(constructor), None);
    assert_ne!(graph.container_return(block), Some(assignment));
}

#[test]
fn later_outer_failure_invalidates_shared_static_flow() {
    let fixture = Fixture::new(concat!(
        "function run() { value = 0; while (flag) { ",
        "class C { static { value; } } ",
        "try { value = 1; } finally {} } }",
    ));
    let legacy = bind_source_file_in_file(
        &fixture.parsed.arena,
        fixture.parsed.source_file,
        fixture.file,
    );
    let bound = fixture.bound();
    let function = fixture.nodes(SyntaxKind::FunctionDeclaration)[0];
    let block = fixture.nodes(SyntaxKind::ClassStaticBlockDeclaration)[0];
    let read = fixture.node(SyntaxKind::ExpressionStatement, "value;");
    for graph in [
        bound.flow_graph(),
        legacy
            .flow_graph(&fixture.parsed.arena, fixture.parsed.source_file)
            .unwrap(),
    ] {
        assert_eq!(graph.container_is_complete(bound.source_file()), Some(true));
        assert_eq!(graph.container_is_complete(function), Some(false));
        assert_eq!(graph.flow_container(read), Some(block));
        assert_eq!(
            (
                graph.container_is_complete(block),
                graph.container_start(block),
                graph.container_end(block),
                graph.container_return(block),
                graph.flow_at(read),
            ),
            (Some(false), None, None, None, None),
            "the static block depends on the incomplete outer loop",
        );
    }
}

#[test]
fn complete_outer_loop_keeps_nested_static_flow_and_its_backedge() {
    let fixture = Fixture::new(concat!(
        "function run() { entered = 0; while (flag) { ",
        "class Outer { static { outer_read; ",
        "class Inner { static { inner_read; } } } } ",
        "advanced = 1; } } after;",
    ));
    let bound = fixture.bound();
    let graph = bound.flow_graph();
    assert!(graph.is_complete(), "{:?}", graph.unsupported());
    let loop_head = bound
        .flow_at(fixture.node(SyntaxKind::Identifier, "flag"))
        .unwrap();
    let entered = fixture.mutation(
        FlowFlags::ASSIGNMENT,
        fixture.node(SyntaxKind::Identifier, "entered"),
    );
    let advanced = fixture.mutation(
        FlowFlags::ASSIGNMENT,
        fixture.node(SyntaxKind::Identifier, "advanced"),
    );
    let loop_node = graph.nodes().get(loop_head).unwrap();
    assert!(loop_node.flags.contains(FlowFlags::LOOP_LABEL));
    assert_eq!(loop_node.antecedents, [entered, advanced]);
    let incoming = graph.nodes().get(advanced).unwrap().antecedent.unwrap();
    let incoming_node = graph.nodes().get(incoming).unwrap();
    assert!(incoming_node.flags.contains(FlowFlags::TRUE_CONDITION));
    assert_eq!(incoming_node.antecedent, Some(loop_head));
    for text in ["outer_read;", "inner_read;"] {
        let read = fixture.node(SyntaxKind::ExpressionStatement, text);
        let block = bound.flow_container(read).unwrap();
        assert_eq!(graph.container_is_complete(block), Some(true));
        assert_eq!(graph.container_start(block), Some(incoming));
        assert_eq!(graph.container_end(block), Some(incoming));
        assert_eq!(graph.container_return(block), Some(incoming));
        assert_eq!(bound.flow_at(read), Some(incoming));
    }
}

#[test]
fn late_outer_failure_invalidates_nested_blocks_but_not_independent_bodies() {
    let fixture = Fixture::new(concat!(
        "function run() { while (flag) { class Outer { ",
        "static { outer_read; class Inner { static { inner_read; } } ",
        "function detached() { class Local { static { function_read; } } } } ",
        "constructor() { constructor_read; } ",
        "method() { class Local { static { method_read; } } } ",
        "} try { value = 1; } finally {} } } after;",
    ));
    let bound = fixture.bound();
    let graph = bound.flow_graph();
    assert_eq!(graph.container_is_complete(bound.source_file()), Some(true));
    for text in ["outer_read;", "inner_read;"] {
        let read = fixture.node(SyntaxKind::ExpressionStatement, text);
        let block = bound.flow_container(read).unwrap();
        assert_eq!(graph.container_is_complete(block), Some(false));
        assert_eq!(graph.container_start(block), None);
        assert_eq!(graph.container_end(block), None);
        assert_eq!(graph.container_return(block), None);
        assert_eq!(bound.flow_at(read), None);
        assert!(graph.unsupported().iter().any(|boundary| {
            boundary.node == block
                && boundary.container == block
                && boundary.kind == UnsupportedFlowKind::CrossContainerFlowEffects
        }));
    }
    let detached = fixture.node(
        SyntaxKind::FunctionDeclaration,
        "function detached() { class Local { static { function_read; } } }",
    );
    let method = fixture.nodes(SyntaxKind::MethodDeclaration)[0];
    let constructor = fixture.nodes(SyntaxKind::Constructor)[0];
    for (body, text) in [
        (detached, "function_read;"),
        (method, "method_read;"),
        (constructor, "constructor_read;"),
    ] {
        let read = fixture.node(SyntaxKind::ExpressionStatement, text);
        let container = bound.flow_container(read).unwrap();
        let start = graph.container_start(body).unwrap();
        assert!(
            graph
                .nodes()
                .get(start)
                .unwrap()
                .flags
                .contains(FlowFlags::START)
        );
        assert_eq!(graph.container_is_complete(body), Some(true));
        assert_eq!(graph.container_is_complete(container), Some(true));
        assert_eq!(graph.container_start(container), Some(start));
        assert_eq!(bound.flow_at(read), Some(start));
    }
    assert!(
        bound
            .flow_at(fixture.node(SyntaxKind::ExpressionStatement, "after;"))
            .is_some()
    );
}
