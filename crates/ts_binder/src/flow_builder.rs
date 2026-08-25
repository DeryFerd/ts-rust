use std::collections::{BTreeSet, HashMap};

use ts_ast::{
    FileId, FlowFlags, FlowNode, FlowNodePayload, FlowRef, NodeArena, NodeData, NodeFlags, NodeId,
    NodeRef, SyntaxKind,
};

use crate::{BoundFlowGraph, UnsupportedFlow, UnsupportedFlowKind};

pub(super) trait FlowTraversalHooks {
    fn enter_node(&mut self, node: NodeId);

    fn exit_node(&mut self, node: NodeId);
}

struct NoopTraversalHooks;

impl FlowTraversalHooks for NoopTraversalHooks {
    fn enter_node(&mut self, _node: NodeId) {}

    fn exit_node(&mut self, _node: NodeId) {}
}

pub(super) fn build_flow_graph(
    arena: &NodeArena,
    children: &HashMap<NodeId, Vec<NodeId>>,
    source_file: NodeId,
    file: FileId,
) -> BoundFlowGraph {
    build_flow_graph_with_hooks(arena, children, source_file, file, &mut NoopTraversalHooks)
}

pub(super) fn build_flow_graph_with_hooks(
    arena: &NodeArena,
    children: &HashMap<NodeId, Vec<NodeId>>,
    source_file: NodeId,
    file: FileId,
    hooks: &mut dyn FlowTraversalHooks,
) -> BoundFlowGraph {
    FlowBuilder::new(arena, children, file, hooks).build(source_file)
}

struct SavedFlow {
    current: Option<FlowRef>,
    container: NodeId,
    return_target: Option<FlowRef>,
    break_target: Option<FlowRef>,
    continue_target: Option<FlowRef>,
    active_labels: Vec<ActiveLabel>,
    pre_switch_case_flow: Option<FlowRef>,
}

#[derive(Clone, Copy)]
struct FunctionContainer {
    body: Option<NodeId>,
    return_target: bool,
    start_payload: bool,
}

struct ActiveLabel {
    name: String,
    break_target: FlowRef,
    continue_target: Option<FlowRef>,
    referenced: bool,
}

#[derive(Clone, Copy)]
enum JumpKind {
    Break,
    Continue,
}

struct FlowBuilder<'a, 'hooks> {
    ast: &'a NodeArena,
    children: &'a HashMap<NodeId, Vec<NodeId>>,
    hooks: &'hooks mut dyn FlowTraversalHooks,
    graph: BoundFlowGraph,
    current: Option<FlowRef>,
    container: NodeId,
    return_target: Option<FlowRef>,
    break_target: Option<FlowRef>,
    continue_target: Option<FlowRef>,
    true_target: Option<FlowRef>,
    false_target: Option<FlowRef>,
    active_labels: Vec<ActiveLabel>,
    pre_switch_case_flow: Option<FlowRef>,
    has_flow_effects: bool,
    in_assignment_pattern: bool,
    effect_dependency_containers: Vec<NodeId>,
    built_containers: BTreeSet<NodeId>,
    visited: Vec<bool>,
}

impl<'a, 'hooks> FlowBuilder<'a, 'hooks> {
    fn new(
        ast: &'a NodeArena,
        children: &'a HashMap<NodeId, Vec<NodeId>>,
        file: FileId,
        hooks: &'hooks mut dyn FlowTraversalHooks,
    ) -> Self {
        Self {
            ast,
            children,
            hooks,
            graph: BoundFlowGraph::new(ast.id(), file),
            current: None,
            container: NodeId::new(0),
            return_target: None,
            break_target: None,
            continue_target: None,
            true_target: None,
            false_target: None,
            active_labels: Vec::new(),
            pre_switch_case_flow: None,
            has_flow_effects: false,
            in_assignment_pattern: false,
            effect_dependency_containers: Vec::new(),
            built_containers: BTreeSet::new(),
            visited: vec![false; ast.len()],
        }
    }

    fn build(mut self, source_file: NodeId) -> BoundFlowGraph {
        self.container = source_file;
        self.built_containers.insert(source_file);
        let start = self.alloc_start(None);
        self.graph.container_starts.insert(source_file, start);
        self.current = Some(start);

        self.bind_node(source_file);
        self.finish_container(source_file, true);
        self.graph
    }

    fn bind_node(&mut self, node_id: NodeId) {
        if std::mem::replace(&mut self.visited[node_id.index()], true) {
            return;
        }
        self.hooks.enter_node(node_id);
        let saved_in_assignment_pattern = self.in_assignment_pattern;
        self.in_assignment_pattern = saved_in_assignment_pattern
            && !self.current_is_unreachable()
            && (self.is_destructuring_assignment(node_id)
                || matches!(
                    self.node_kind(node_id),
                    Some(
                        SyntaxKind::ObjectLiteralExpression
                            | SyntaxKind::ArrayLiteralExpression
                            | SyntaxKind::PropertyAssignment
                            | SyntaxKind::SpreadElement
                    )
                ));
        self.bind_node_worker(node_id);
        for child in self.children_in_pinned_order(node_id) {
            if !self.visited[child.index()] {
                self.bind_node(child);
            }
        }
        self.in_assignment_pattern = saved_in_assignment_pattern;
        self.hooks.exit_node(node_id);
    }

    fn bind_node_worker(&mut self, node_id: NodeId) {
        let Some(node) = self.ast.get(node_id) else {
            self.mark_unsupported(node_id, UnsupportedFlowKind::DestructuringAssignment);
            return;
        };
        let kind = node.kind;

        if kind == SyntaxKind::ClassStaticBlockDeclaration {
            self.mark_unsupported(node_id, UnsupportedFlowKind::ClassStaticBlock);
            self.bind_children_without_flow(node_id);
            return;
        }

        if let Some(function) = self.function_container(node_id) {
            if let Some(kind) = self.unsupported_direct_function_call_kind(node_id) {
                self.mark_unsupported(node_id, kind);
                self.bind_children_without_flow(node_id);
                return;
            }
            if function.start_payload {
                self.record_node_flow_including_unreachable(node_id);
            }
            self.bind_function_container(node_id, function);
            return;
        }

        if kind == SyntaxKind::ModuleBlock {
            self.bind_module_block(node_id);
            return;
        }

        if kind == SyntaxKind::PropertyDeclaration
            && matches!(
                self.ast.get(node_id).map(|node| &node.data),
                Some(NodeData::PropertyDeclaration(data)) if data.initializer.is_some()
            )
        {
            self.bind_property_initializer_container(node_id);
            return;
        }

        if self.current.is_none() {
            self.bind_children_without_flow(node_id);
            return;
        }

        if self.current_is_unreachable() {
            if self.is_potentially_executable_node(node_id) {
                self.graph.unreachable_nodes.insert(node_id);
                self.graph.node_containers.insert(node_id, self.container);
            }
            self.bind_children(node_id);
            return;
        }

        if is_flow_statement(kind) {
            self.record_node_flow(node_id);
        }

        if self.is_optional_chain_node(node_id) {
            if matches!(
                kind,
                SyntaxKind::PropertyAccessExpression | SyntaxKind::ElementAccessExpression
            ) && self.is_narrowable_reference(node_id)
            {
                self.record_node_flow(node_id);
            }
            self.bind_optional_chain_flow(node_id);
            if kind == SyntaxKind::CallExpression {
                self.bind_array_mutation_call(node_id);
            }
            return;
        }

        self.bind_node_by_kind(node_id, kind);
    }

    fn bind_node_by_kind(&mut self, node_id: NodeId, kind: SyntaxKind) {
        match kind {
            SyntaxKind::WhileStatement => self.bind_while_statement(node_id),
            SyntaxKind::DoStatement => self.bind_do_statement(node_id),
            SyntaxKind::ForStatement => self.bind_for_statement(node_id),
            SyntaxKind::ForInStatement | SyntaxKind::ForOfStatement => {
                self.bind_for_in_or_of_statement(node_id);
            }
            SyntaxKind::SwitchStatement => self.bind_switch_statement(node_id),
            SyntaxKind::CaseBlock => self.bind_case_block(node_id),
            SyntaxKind::CaseClause | SyntaxKind::DefaultClause => {
                self.bind_case_or_default_clause(node_id);
            }
            SyntaxKind::TryStatement | SyntaxKind::CatchClause => {
                self.mark_unsupported(node_id, UnsupportedFlowKind::TryStatement);
                self.bind_children_without_flow(node_id);
            }
            SyntaxKind::BreakStatement => {
                self.bind_break_or_continue_statement(node_id, JumpKind::Break);
            }
            SyntaxKind::ContinueStatement => {
                self.bind_break_or_continue_statement(node_id, JumpKind::Continue);
            }
            SyntaxKind::LabeledStatement => self.bind_labeled_statement(node_id),
            SyntaxKind::WithStatement => {
                self.mark_unsupported(node_id, UnsupportedFlowKind::WithStatement);
                self.bind_children_without_flow(node_id);
            }
            SyntaxKind::SourceFile => self.bind_source_file(node_id),
            SyntaxKind::Block => self.bind_block(node_id),
            SyntaxKind::IfStatement => self.bind_if_statement(node_id),
            SyntaxKind::ReturnStatement => self.bind_return_statement(node_id),
            SyntaxKind::ThrowStatement => self.bind_throw_statement(node_id),
            SyntaxKind::ExpressionStatement => self.bind_expression_statement(node_id),
            SyntaxKind::ConditionalExpression => self.bind_conditional_expression(node_id),
            SyntaxKind::BinaryExpression => self.bind_binary_expression(node_id),
            SyntaxKind::VariableDeclaration => self.bind_variable_declaration(node_id),
            SyntaxKind::Parameter => self.bind_parameter(node_id),
            SyntaxKind::BindingElement => self.bind_binding_element(node_id),
            SyntaxKind::PrefixUnaryExpression => self.bind_prefix_unary_expression(node_id),
            SyntaxKind::PostfixUnaryExpression => self.bind_postfix_unary_expression(node_id),
            SyntaxKind::DeleteExpression => self.bind_delete_expression(node_id),
            SyntaxKind::CallExpression => self.bind_call_expression(node_id),
            SyntaxKind::QualifiedName => {
                if self.is_part_of_type_query(node_id) {
                    self.record_node_flow(node_id);
                }
                self.bind_children(node_id);
            }
            SyntaxKind::Identifier
            | SyntaxKind::ThisKeyword
            | SyntaxKind::SuperKeyword
            | SyntaxKind::MetaProperty => {
                self.record_node_flow(node_id);
                self.bind_children(node_id);
            }
            SyntaxKind::PropertyAccessExpression | SyntaxKind::ElementAccessExpression => {
                if self.is_narrowable_reference(node_id) {
                    self.record_node_flow(node_id);
                }
                self.bind_children(node_id);
            }
            _ => self.bind_children(node_id),
        }
    }

    fn bind_block(&mut self, block: NodeId) {
        let statements = match self.ast.get(block).map(|node| &node.data) {
            Some(NodeData::Block(data)) => data.statements.nodes.clone(),
            _ => return,
        };
        self.bind_statement_list(&statements);
    }

    fn bind_source_file(&mut self, source_file: NodeId) {
        let (statements, end_of_file) = match self.ast.get(source_file).map(|node| &node.data) {
            Some(NodeData::SourceFile(data)) => {
                (data.statements.nodes.clone(), data.end_of_file_token)
            }
            _ => return,
        };
        self.bind_statement_list(&statements);
        self.bind_node(end_of_file);
    }

    fn bind_statement_list(&mut self, statements: &[NodeId]) {
        for statement in statements {
            if self.node_kind(*statement) == Some(SyntaxKind::FunctionDeclaration) {
                self.bind_node(*statement);
            }
        }
        for statement in statements {
            if self.node_kind(*statement) != Some(SyntaxKind::FunctionDeclaration) {
                self.bind_node(*statement);
            }
        }
    }

    fn set_continue_target(&mut self, mut node_id: NodeId, target: FlowRef) -> FlowRef {
        let mut label_index = self.active_labels.len();
        while let Some(parent) = self.ast.get(node_id).and_then(|node| node.parent) {
            if self.node_kind(parent) != Some(SyntaxKind::LabeledStatement) || label_index == 0 {
                break;
            }
            label_index -= 1;
            self.active_labels[label_index].continue_target = Some(target);
            node_id = parent;
        }
        target
    }

    fn bind_iterative_statement(
        &mut self,
        statement: NodeId,
        break_target: FlowRef,
        continue_target: FlowRef,
    ) {
        let saved_break_target = self.break_target.replace(break_target);
        let saved_continue_target = self.continue_target.replace(continue_target);
        self.bind_node(statement);
        self.break_target = saved_break_target;
        self.continue_target = saved_continue_target;
    }

    fn bind_while_statement(&mut self, node_id: NodeId) {
        let (expression, statement) = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::WhileStatement(data)) => (data.expression, data.statement),
            _ => return,
        };
        let pre_while_label = self.alloc_loop_label();
        let pre_while_label = self.set_continue_target(node_id, pre_while_label);
        let pre_body_label = self.alloc_label();
        let post_while_label = self.alloc_label();
        self.add_current_antecedent(pre_while_label);
        self.current = Some(pre_while_label);
        self.bind_condition(expression, pre_body_label, post_while_label);
        if self.current.is_none() {
            return;
        }
        self.current = self.finish_label(pre_body_label);
        self.bind_iterative_statement(statement, post_while_label, pre_while_label);
        if self.current.is_none() {
            return;
        }
        self.add_current_antecedent(pre_while_label);
        self.current = self.finish_label(post_while_label);
    }

    fn bind_do_statement(&mut self, node_id: NodeId) {
        let (expression, statement) = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::DoStatement(data)) => (data.expression, data.statement),
            _ => return,
        };
        let pre_do_label = self.alloc_loop_label();
        let pre_condition_label = self.alloc_label();
        let pre_condition_label = self.set_continue_target(node_id, pre_condition_label);
        let post_do_label = self.alloc_label();
        self.add_current_antecedent(pre_do_label);
        self.current = Some(pre_do_label);
        self.bind_iterative_statement(statement, post_do_label, pre_condition_label);
        if self.current.is_none() {
            return;
        }
        self.add_current_antecedent(pre_condition_label);
        self.current = self.finish_label(pre_condition_label);
        self.bind_condition(expression, pre_do_label, post_do_label);
        if self.current.is_none() {
            return;
        }
        self.current = self.finish_label(post_do_label);
    }

    fn bind_for_statement(&mut self, node_id: NodeId) {
        let (initializer, condition, incrementor, statement) =
            match self.ast.get(node_id).map(|node| &node.data) {
                Some(NodeData::ForStatement(data)) => (
                    data.initializer,
                    data.condition,
                    data.incrementor,
                    data.statement,
                ),
                _ => return,
            };
        let pre_loop_label = self.alloc_loop_label();
        let pre_loop_label = self.set_continue_target(node_id, pre_loop_label);
        let pre_body_label = self.alloc_label();
        let pre_incrementor_label = self.alloc_label();
        let post_loop_label = self.alloc_label();
        if let Some(initializer) = initializer {
            self.bind_node(initializer);
        }
        if self.current.is_none() {
            return;
        }
        self.add_current_antecedent(pre_loop_label);
        self.current = Some(pre_loop_label);
        self.bind_optional_condition(condition, pre_body_label, post_loop_label);
        if self.current.is_none() {
            return;
        }
        self.current = self.finish_label(pre_body_label);
        self.bind_iterative_statement(statement, post_loop_label, pre_incrementor_label);
        if self.current.is_none() {
            return;
        }
        self.add_current_antecedent(pre_incrementor_label);
        self.current = self.finish_label(pre_incrementor_label);
        if let Some(incrementor) = incrementor {
            self.bind_node(incrementor);
        }
        if self.current.is_none() {
            return;
        }
        self.add_current_antecedent(pre_loop_label);
        self.current = self.finish_label(post_loop_label);
    }

    fn bind_for_in_or_of_statement(&mut self, node_id: NodeId) {
        let (await_modifier, expression, initializer, statement) =
            match self.ast.get(node_id).map(|node| &node.data) {
                Some(NodeData::ForInOrOfStatement(data)) => (
                    data.await_modifier,
                    data.expression,
                    data.initializer,
                    data.statement,
                ),
                _ => return,
            };
        let pre_loop_label = self.alloc_loop_label();
        let pre_loop_label = self.set_continue_target(node_id, pre_loop_label);
        let post_loop_label = self.alloc_label();
        self.bind_node(expression);
        if self.current.is_none() {
            return;
        }
        self.add_current_antecedent(pre_loop_label);
        self.current = Some(pre_loop_label);
        if self.node_kind(node_id) == Some(SyntaxKind::ForOfStatement)
            && let Some(await_modifier) = await_modifier
        {
            self.bind_node(await_modifier);
        }
        self.add_current_antecedent(post_loop_label);
        if self.node_kind(initializer) != Some(SyntaxKind::VariableDeclarationList)
            && matches!(
                self.node_kind(self.skip_parentheses(initializer)),
                Some(SyntaxKind::ArrayLiteralExpression | SyntaxKind::ObjectLiteralExpression)
            )
        {
            self.mark_unsupported(initializer, UnsupportedFlowKind::DestructuringAssignment);
            return;
        }
        self.bind_node(initializer);
        if self.current.is_none() {
            return;
        }
        if self.node_kind(initializer) != Some(SyntaxKind::VariableDeclarationList) {
            self.bind_assignment_target_flow(initializer);
        }
        self.bind_iterative_statement(statement, post_loop_label, pre_loop_label);
        if self.current.is_none() {
            return;
        }
        self.add_current_antecedent(pre_loop_label);
        self.current = self.finish_label(post_loop_label);
    }

    fn bind_switch_statement(&mut self, node_id: NodeId) {
        let (expression, case_block) = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::SwitchStatement(data)) => (data.expression, data.case_block),
            _ => return,
        };
        let post_switch_label = self.alloc_label();
        self.bind_node(expression);
        let Some(pre_switch_case_flow) = self.current else {
            return;
        };

        let saved_break_target = self.break_target.replace(post_switch_label);
        let saved_pre_switch_case_flow = self.pre_switch_case_flow.replace(pre_switch_case_flow);
        self.bind_node(case_block);

        if let Some(current) = self.current {
            self.add_antecedent(post_switch_label, current);
        }
        if !self.case_block_has_default(case_block) {
            let no_match = self.create_flow_switch_clause(pre_switch_case_flow, node_id, 0, 0);
            self.add_antecedent(post_switch_label, no_match);
        }
        let post_switch_flow = self.finish_label(post_switch_label);
        let switch_incomplete = self.graph.incomplete_containers.contains(&self.container);
        self.break_target = saved_break_target;
        self.pre_switch_case_flow = saved_pre_switch_case_flow;
        self.current = (!switch_incomplete).then_some(post_switch_flow).flatten();
    }

    fn bind_case_block(&mut self, node_id: NodeId) {
        let clauses = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::CaseBlock(data)) => data.clauses.nodes.clone(),
            _ => return,
        };
        let Some(switch_statement) = self.ast.get(node_id).and_then(|node| node.parent) else {
            self.bind_children(node_id);
            return;
        };
        let Some(NodeData::SwitchStatement(switch_data)) =
            self.ast.get(switch_statement).map(|node| &node.data)
        else {
            self.bind_children(node_id);
            return;
        };
        let switch_expression = switch_data.expression;
        let Some(pre_switch_case_flow) = self.pre_switch_case_flow else {
            self.bind_children(node_id);
            return;
        };
        let is_narrowing_switch = self.node_kind(switch_expression)
            == Some(SyntaxKind::TrueKeyword)
            || self.is_narrowing_expression(switch_expression);
        let mut fallthrough_flow = self.graph.nodes.unreachable();
        let mut index = 0;

        while index < clauses.len() {
            let clause_start = index;
            while self.case_clause_statements_are_empty(clauses[index]) && index + 1 < clauses.len()
            {
                if self.is_unreachable(fallthrough_flow) {
                    self.current = Some(pre_switch_case_flow);
                }
                self.bind_node(clauses[index]);
                if self.current.is_none() {
                    return;
                }
                index += 1;
            }

            let pre_case_label = self.alloc_label();
            let pre_case_flow = if is_narrowing_switch {
                self.create_flow_switch_clause(
                    pre_switch_case_flow,
                    switch_statement,
                    clause_start,
                    index + 1,
                )
            } else {
                pre_switch_case_flow
            };
            self.add_antecedent(pre_case_label, pre_case_flow);
            self.add_antecedent(pre_case_label, fallthrough_flow);
            self.current = self.finish_label(pre_case_label);

            let clause = clauses[index];
            self.bind_node(clause);
            let Some(current) = self.current else {
                return;
            };
            fallthrough_flow = current;
            if !self.is_unreachable(current) && index + 1 < clauses.len() {
                self.graph.fallthrough_flows.insert(clause, current);
                self.graph.node_containers.insert(clause, self.container);
            }
            index += 1;
        }
    }

    fn bind_case_or_default_clause(&mut self, node_id: NodeId) {
        let (expression, statements) = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::CaseOrDefaultClause(data)) => (
                (self.node_kind(node_id) == Some(SyntaxKind::CaseClause))
                    .then_some(data.expression),
                data.statements.nodes.clone(),
            ),
            _ => return,
        };
        if let Some(expression) = expression {
            let saved_current = self.current;
            let Some(pre_switch_case_flow) = self.pre_switch_case_flow else {
                self.bind_case_statements(&statements);
                return;
            };
            self.current = Some(pre_switch_case_flow);
            self.bind_node(expression);
            self.current = saved_current;
        }
        self.bind_case_statements(&statements);
    }

    fn bind_case_statements(&mut self, statements: &[NodeId]) {
        for statement in statements {
            self.bind_node(*statement);
        }
    }

    fn case_block_has_default(&self, case_block: NodeId) -> bool {
        matches!(
            self.ast.get(case_block).map(|node| &node.data),
            Some(NodeData::CaseBlock(data))
                if data.clauses.nodes.iter().any(|clause| {
                    self.node_kind(*clause) == Some(SyntaxKind::DefaultClause)
                })
        )
    }

    fn case_clause_statements_are_empty(&self, clause: NodeId) -> bool {
        matches!(
            self.ast.get(clause).map(|node| &node.data),
            Some(NodeData::CaseOrDefaultClause(data)) if data.statements.nodes.is_empty()
        )
    }

    fn bind_break_or_continue_statement(&mut self, node_id: NodeId, jump: JumpKind) {
        let label = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::BreakStatement(data)) => data.label,
            Some(NodeData::ContinueStatement(data)) => data.label,
            _ => return,
        };
        if let Some(label) = label {
            self.bind_node(label);
            let Some(name) = self.identifier_text(label).map(str::to_owned) else {
                return;
            };
            if let Some(index) = self.find_active_label(&name) {
                self.active_labels[index].referenced = true;
                let target = match jump {
                    JumpKind::Break => Some(self.active_labels[index].break_target),
                    JumpKind::Continue => self.active_labels[index].continue_target,
                };
                self.bind_break_or_continue_flow(target);
            }
        } else {
            let target = match jump {
                JumpKind::Break => self.break_target,
                JumpKind::Continue => self.continue_target,
            };
            self.bind_break_or_continue_flow(target);
        }
    }

    fn find_active_label(&self, name: &str) -> Option<usize> {
        self.active_labels
            .iter()
            .rposition(|label| label.name == name)
    }

    fn bind_break_or_continue_flow(&mut self, target: Option<FlowRef>) {
        let (Some(target), Some(current)) = (target, self.current) else {
            return;
        };
        self.add_antecedent(target, current);
        self.current = Some(self.graph.nodes.unreachable());
        self.has_flow_effects = true;
    }

    fn bind_labeled_statement(&mut self, node_id: NodeId) {
        let (label, statement) = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::LabeledStatement(data)) => (data.label, data.statement),
            _ => return,
        };
        let Some(name) = self.identifier_text(label).map(str::to_owned) else {
            self.mark_unsupported(node_id, UnsupportedFlowKind::DestructuringAssignment);
            return;
        };
        let post_statement_label = self.alloc_label();
        self.active_labels.push(ActiveLabel {
            name,
            break_target: post_statement_label,
            continue_target: None,
            referenced: false,
        });
        self.bind_node(label);
        self.bind_node(statement);
        let active_label = self
            .active_labels
            .pop()
            .expect("labeled statement keeps its active label until its body is bound");
        if !active_label.referenced {
            self.graph.unreachable_nodes.insert(label);
            self.graph.node_containers.insert(label, self.container);
        }
        if self.current.is_none() {
            return;
        }
        self.add_current_antecedent(post_statement_label);
        self.current = self.finish_label(post_statement_label);
    }

    fn bind_if_statement(&mut self, node_id: NodeId) {
        let (expression, then_statement, else_statement) =
            match self.ast.get(node_id).map(|node| &node.data) {
                Some(NodeData::IfStatement(data)) => {
                    (data.expression, data.then_statement, data.else_statement)
                }
                _ => return,
            };
        let then_label = self.alloc_label();
        let else_label = self.alloc_label();
        let post_if_label = self.alloc_label();
        self.bind_condition(expression, then_label, else_label);
        if self.current.is_none() {
            return;
        }
        let Some(then_flow) = self.finish_label(then_label) else {
            return;
        };
        self.current = Some(then_flow);
        self.bind_node(then_statement);
        if !self.add_current_antecedent(post_if_label) {
            return;
        }
        let Some(else_flow) = self.finish_label(else_label) else {
            return;
        };
        self.current = Some(else_flow);
        if let Some(else_statement) = else_statement {
            self.bind_node(else_statement);
        }
        if !self.add_current_antecedent(post_if_label) {
            return;
        }
        self.current = self.finish_label(post_if_label);
    }

    fn bind_condition(&mut self, expression: NodeId, true_target: FlowRef, false_target: FlowRef) {
        self.bind_optional_condition(Some(expression), true_target, false_target);
    }

    fn bind_optional_condition(
        &mut self,
        expression: Option<NodeId>,
        true_target: FlowRef,
        false_target: FlowRef,
    ) {
        if let Some(expression) = expression {
            self.bind_with_conditional_branches(expression, true_target, false_target);
            if self.current.is_none()
                || self.is_logical_condition(expression)
                || self.is_outermost_optional_chain(expression)
            {
                return;
            }
        }
        let Some(current) = self.current else {
            return;
        };
        let (true_flow, false_flow) = if let Some(expression) = expression {
            (
                self.create_flow_condition(FlowFlags::TRUE_CONDITION, current, expression),
                self.create_flow_condition(FlowFlags::FALSE_CONDITION, current, expression),
            )
        } else {
            (current, self.graph.nodes.unreachable())
        };
        self.add_antecedent(true_target, true_flow);
        self.add_antecedent(false_target, false_flow);
    }

    fn bind_with_conditional_branches(
        &mut self,
        expression: NodeId,
        true_target: FlowRef,
        false_target: FlowRef,
    ) {
        let saved_true_target = self.true_target.replace(true_target);
        let saved_false_target = self.false_target.replace(false_target);
        self.bind_node(expression);
        self.true_target = saved_true_target;
        self.false_target = saved_false_target;
    }

    fn bind_return_statement(&mut self, node_id: NodeId) {
        let expression = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::ReturnStatement(data)) => data.expression,
            _ => return,
        };
        if let Some(expression) = expression {
            self.bind_node(expression);
        }
        if let (Some(target), Some(current)) = (self.return_target, self.current) {
            self.add_antecedent(target, current);
        }
        if self.current.is_some() {
            self.current = Some(self.graph.nodes.unreachable());
            self.has_flow_effects = true;
        }
    }

    fn bind_throw_statement(&mut self, node_id: NodeId) {
        let expression = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::ThrowStatement(data)) => data.expression,
            _ => return,
        };
        self.bind_node(expression);
        if self.current.is_some() {
            self.current = Some(self.graph.nodes.unreachable());
            self.has_flow_effects = true;
        }
    }

    fn bind_expression_statement(&mut self, node_id: NodeId) {
        let expression = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::ExpressionStatement(data)) => data.expression,
            _ => return,
        };
        self.bind_node(expression);
        self.maybe_bind_expression_flow_if_call(expression);
    }

    fn bind_conditional_expression(&mut self, node_id: NodeId) {
        let dependency_container = self.container;
        self.effect_dependency_containers.push(dependency_container);
        self.bind_conditional_expression_worker(node_id);
        let popped = self.effect_dependency_containers.pop();
        debug_assert_eq!(popped, Some(dependency_container));
    }

    fn bind_conditional_expression_worker(&mut self, node_id: NodeId) {
        let (condition, question, when_true, colon, when_false) =
            match self.ast.get(node_id).map(|node| &node.data) {
                Some(NodeData::ConditionalExpression(data)) => (
                    data.condition,
                    data.question_token,
                    data.when_true,
                    data.colon_token,
                    data.when_false,
                ),
                _ => return,
            };
        let true_label = self.alloc_label();
        let false_label = self.alloc_label();
        let post_expression_label = self.alloc_label();
        let saved_current = self.current;
        let saved_effects = self.has_flow_effects;
        self.has_flow_effects = false;

        self.bind_condition(condition, true_label, false_label);
        if self.current.is_none() {
            self.has_flow_effects |= saved_effects;
            return;
        }
        let Some(true_flow) = self.finish_label(true_label) else {
            self.has_flow_effects |= saved_effects;
            return;
        };
        self.current = Some(true_flow);
        self.bind_node(question);
        self.bind_node(when_true);
        if !self.add_current_antecedent(post_expression_label) {
            self.has_flow_effects |= saved_effects;
            return;
        }
        let Some(false_flow) = self.finish_label(false_label) else {
            self.has_flow_effects |= saved_effects;
            return;
        };
        self.current = Some(false_flow);
        self.bind_node(colon);
        self.bind_node(when_false);
        if !self.add_current_antecedent(post_expression_label) {
            self.has_flow_effects |= saved_effects;
            return;
        }
        self.current = if self.has_flow_effects {
            self.finish_label(post_expression_label)
        } else {
            saved_current
        };
        self.has_flow_effects |= saved_effects;
    }

    fn bind_binary_expression(&mut self, node_id: NodeId) {
        if self.bind_literal_addition_chain(node_id) {
            return;
        }

        let (left, operator_token, right, type_) =
            match self.ast.get(node_id).map(|node| &node.data) {
                Some(NodeData::BinaryExpression(data)) => {
                    (data.left, data.operator_token, data.right, data.type_)
                }
                _ => return,
            };
        let Some(operator) = self.node_kind(operator_token) else {
            self.mark_unsupported(node_id, UnsupportedFlowKind::DestructuringAssignment);
            return;
        };
        if operator.is_assignment_operator()
            && matches!(
                self.node_kind(left),
                Some(SyntaxKind::ArrayLiteralExpression | SyntaxKind::ObjectLiteralExpression)
            )
        {
            if operator != SyntaxKind::EqualsToken {
                self.mark_unsupported(node_id, UnsupportedFlowKind::DestructuringAssignment);
                self.bind_children_without_flow(node_id);
                return;
            }

            let saved_in_assignment_pattern = self.in_assignment_pattern;
            self.bind_destructuring_assignment_children(node_id);
            debug_assert_eq!(self.in_assignment_pattern, saved_in_assignment_pattern);
            self.bind_assignment_target_flow(left);
            return;
        }
        if is_logical_operator(operator) {
            self.bind_logical_expression(node_id);
            return;
        }

        self.bind_node(left);
        if operator == SyntaxKind::CommaToken {
            self.maybe_bind_expression_flow_if_call(left);
        }
        if let Some(type_) = type_ {
            self.bind_node(type_);
        }
        self.bind_node(operator_token);
        self.bind_node(right);
        if operator == SyntaxKind::CommaToken {
            self.maybe_bind_expression_flow_if_call(right);
        }
        if operator.is_assignment_operator() && !self.is_assignment_target(node_id) {
            self.bind_assignment_target_flow(left);
            if operator == SyntaxKind::EqualsToken
                && self.node_kind(left) == Some(SyntaxKind::ElementAccessExpression)
            {
                let base = match self.ast.get(left).map(|node| &node.data) {
                    Some(NodeData::ElementAccessExpression(data)) => data.expression,
                    _ => return,
                };
                if self.is_narrowable_operand(base) {
                    self.create_flow_mutation(FlowFlags::ARRAY_MUTATION, node_id);
                }
            }
        }
    }

    /// Walks long literal additions without recursively entering their left spine.
    fn bind_literal_addition_chain(&mut self, root: NodeId) -> bool {
        let mut current = root;
        let mut chain = Vec::new();
        let mut expected_family = None;

        let first = loop {
            let Some(NodeData::BinaryExpression(binary)) =
                self.ast.get(current).map(|node| &node.data)
            else {
                return false;
            };
            if binary.type_.is_some()
                || self.node_kind(binary.operator_token) != Some(SyntaxKind::PlusToken)
            {
                return false;
            }

            let family = match self.node_kind(binary.right) {
                Some(SyntaxKind::NumericLiteral) => false,
                Some(SyntaxKind::StringLiteral | SyntaxKind::NoSubstitutionTemplateLiteral) => true,
                _ => return false,
            };
            if expected_family.is_some_and(|expected| expected != family) {
                return false;
            }
            expected_family = Some(family);
            chain.push((current, binary.operator_token, binary.right));

            if self.node_kind(binary.left) != Some(SyntaxKind::BinaryExpression) {
                let first_family = match self.node_kind(binary.left) {
                    Some(SyntaxKind::NumericLiteral) => false,
                    Some(SyntaxKind::StringLiteral | SyntaxKind::NoSubstitutionTemplateLiteral) => {
                        true
                    }
                    _ => return false,
                };
                if first_family != family || chain.len() < 32 {
                    return false;
                }
                break binary.left;
            }
            current = binary.left;
        };

        if chain
            .iter()
            .skip(1)
            .any(|(node, _, _)| self.visited[node.index()])
        {
            return false;
        }

        for (node, _, _) in chain.iter().skip(1) {
            self.visited[node.index()] = true;
            self.hooks.enter_node(*node);
        }

        self.bind_node(first);
        for (node, operator, right) in chain.into_iter().rev() {
            self.bind_node(operator);
            self.bind_node(right);
            if node != root {
                self.hooks.exit_node(node);
            }
        }
        true
    }

    fn bind_logical_expression(&mut self, node_id: NodeId) {
        let dependency_container = self.container;
        self.effect_dependency_containers.push(dependency_container);
        self.bind_logical_expression_worker(node_id);
        let popped = self.effect_dependency_containers.pop();
        debug_assert_eq!(popped, Some(dependency_container));
    }

    fn bind_logical_expression_worker(&mut self, node_id: NodeId) {
        if self.is_top_level_logical_expression(node_id) {
            let post_expression_label = self.alloc_label();
            let saved_current = self.current;
            let saved_effects = self.has_flow_effects;
            self.has_flow_effects = false;
            self.bind_logical_like_expression(
                node_id,
                post_expression_label,
                post_expression_label,
            );
            if self.current.is_some() {
                self.current = if self.has_flow_effects {
                    self.finish_label(post_expression_label)
                } else {
                    saved_current
                };
            }
            self.has_flow_effects |= saved_effects;
        } else if let (Some(true_target), Some(false_target)) =
            (self.true_target, self.false_target)
        {
            self.bind_logical_like_expression(node_id, true_target, false_target);
        } else {
            self.mark_unsupported(node_id, UnsupportedFlowKind::LogicalExpression);
        }
    }

    fn bind_logical_like_expression(
        &mut self,
        node_id: NodeId,
        true_target: FlowRef,
        false_target: FlowRef,
    ) {
        let (left, operator_token, right) = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::BinaryExpression(data)) => (data.left, data.operator_token, data.right),
            _ => return,
        };
        let Some(operator) = self.node_kind(operator_token) else {
            return;
        };
        let pre_right_label = self.alloc_label();
        if matches!(
            operator,
            SyntaxKind::AmpersandAmpersandToken | SyntaxKind::AmpersandAmpersandEqualsToken
        ) {
            self.bind_condition(left, pre_right_label, false_target);
        } else {
            self.bind_condition(left, true_target, pre_right_label);
        }
        if self.current.is_none() {
            return;
        }
        self.current = self.finish_label(pre_right_label);
        if self.current.is_none() {
            return;
        }
        self.bind_node(operator_token);
        if operator.is_logical_or_coalescing_assignment_operator() {
            self.bind_with_conditional_branches(right, true_target, false_target);
            if self.current.is_none() {
                return;
            }
            self.bind_assignment_target_flow(left);
            let Some(current) = self.current else {
                return;
            };
            let true_flow = self.create_flow_condition(FlowFlags::TRUE_CONDITION, current, node_id);
            let false_flow =
                self.create_flow_condition(FlowFlags::FALSE_CONDITION, current, node_id);
            self.add_antecedent(true_target, true_flow);
            self.add_antecedent(false_target, false_flow);
        } else {
            self.bind_condition(right, true_target, false_target);
        }
    }

    fn bind_optional_chain_flow(&mut self, node_id: NodeId) {
        let dependency_container = self.container;
        self.effect_dependency_containers.push(dependency_container);
        if self.is_top_level_logical_expression(node_id) {
            let post_expression_label = self.alloc_label();
            let saved_current = self.current;
            let saved_effects = self.has_flow_effects;
            self.bind_optional_chain(node_id, post_expression_label, post_expression_label);
            if self.current.is_some() {
                self.current = if self.has_flow_effects {
                    self.finish_label(post_expression_label)
                } else {
                    saved_current
                };
            }
            self.has_flow_effects |= saved_effects;
        } else if let (Some(true_target), Some(false_target)) =
            (self.true_target, self.false_target)
        {
            self.bind_optional_chain(node_id, true_target, false_target);
        } else {
            self.mark_unsupported(node_id, UnsupportedFlowKind::OptionalChain);
        }
        let popped = self.effect_dependency_containers.pop();
        debug_assert_eq!(popped, Some(dependency_container));
    }

    fn bind_optional_chain(
        &mut self,
        node_id: NodeId,
        true_target: FlowRef,
        false_target: FlowRef,
    ) {
        let Some(expression) = self.optional_chain_expression(node_id) else {
            return;
        };
        let pre_chain_label = self
            .is_optional_chain_root(node_id)
            .then(|| self.alloc_label());
        self.bind_optional_expression(
            expression,
            pre_chain_label.unwrap_or(true_target),
            false_target,
        );
        if self.current.is_none() {
            return;
        }
        if let Some(pre_chain_label) = pre_chain_label {
            self.current = self.finish_label(pre_chain_label);
        }
        if self.current.is_none() {
            return;
        }

        let saved_true_target = self.true_target.replace(true_target);
        let saved_false_target = self.false_target.replace(false_target);
        self.bind_optional_chain_rest(node_id);
        self.true_target = saved_true_target;
        self.false_target = saved_false_target;
        if self.current.is_none() || !self.is_outermost_optional_chain(node_id) {
            return;
        }
        let Some(current) = self.current else {
            return;
        };
        let true_flow = self.create_flow_condition(FlowFlags::TRUE_CONDITION, current, node_id);
        let false_flow = self.create_flow_condition(FlowFlags::FALSE_CONDITION, current, node_id);
        self.add_antecedent(true_target, true_flow);
        self.add_antecedent(false_target, false_flow);
    }

    fn bind_optional_expression(
        &mut self,
        expression: NodeId,
        true_target: FlowRef,
        false_target: FlowRef,
    ) {
        self.bind_with_conditional_branches(expression, true_target, false_target);
        let Some(current) = self.current else {
            return;
        };
        if !self.is_optional_chain_node(expression) || self.is_outermost_optional_chain(expression)
        {
            let true_flow =
                self.create_flow_condition(FlowFlags::TRUE_CONDITION, current, expression);
            let false_flow =
                self.create_flow_condition(FlowFlags::FALSE_CONDITION, current, expression);
            self.add_antecedent(true_target, true_flow);
            self.add_antecedent(false_target, false_flow);
        }
    }

    fn bind_optional_chain_rest(&mut self, node_id: NodeId) {
        match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::PropertyAccessExpression(data)) => {
                let question_dot = data.question_dot_token;
                let name = data.name;
                if let Some(question_dot) = question_dot {
                    self.bind_node(question_dot);
                }
                self.bind_node(name);
            }
            Some(NodeData::ElementAccessExpression(data)) => {
                let question_dot = data.question_dot_token;
                let argument = data.argument_expression;
                if let Some(question_dot) = question_dot {
                    self.bind_node(question_dot);
                }
                self.bind_node(argument);
            }
            Some(NodeData::CallExpression(data)) => {
                let question_dot = data.question_dot_token;
                let type_arguments = data
                    .type_arguments
                    .as_ref()
                    .map(|arguments| arguments.nodes.clone())
                    .unwrap_or_default();
                let arguments = data.arguments.nodes.clone();
                if let Some(question_dot) = question_dot {
                    self.bind_node(question_dot);
                }
                for argument in type_arguments.into_iter().chain(arguments) {
                    self.bind_node(argument);
                }
            }
            _ => {}
        }
    }

    fn bind_variable_declaration(&mut self, node_id: NodeId) {
        let (name, exclamation, type_, initializer) =
            match self.ast.get(node_id).map(|node| &node.data) {
                Some(NodeData::VariableDeclaration(data)) => (
                    data.name,
                    data.exclamation_token,
                    data.type_,
                    data.initializer,
                ),
                _ => return,
            };
        let initialized_by_iteration = self.is_for_in_or_of_initializer(node_id);
        self.bind_node(name);
        if let Some(exclamation) = exclamation {
            self.bind_node(exclamation);
        }
        if let Some(type_) = type_ {
            self.bind_node(type_);
        }
        if let Some(initializer) = initializer {
            self.bind_node(initializer);
        }
        if initializer.is_some() || initialized_by_iteration {
            self.bind_initialized_variable_flow(node_id);
        }
    }

    fn bind_initialized_variable_flow(&mut self, node_id: NodeId) {
        let name = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::VariableDeclaration(data)) => Some(data.name),
            Some(NodeData::BindingElement(data)) => data.name,
            _ => None,
        };
        if let Some(name) = name
            && let Some(NodeData::BindingPattern(pattern)) =
                self.ast.get(name).map(|node| &node.data)
        {
            let elements = pattern.elements.nodes.clone();
            for element in elements {
                self.bind_initialized_variable_flow(element);
            }
        } else {
            self.create_flow_mutation(FlowFlags::ASSIGNMENT, node_id);
        }
    }

    fn bind_parameter(&mut self, node_id: NodeId) {
        let (modifiers, dot_dot_dot, question, type_, initializer, name) =
            match self.ast.get(node_id).map(|node| &node.data) {
                Some(NodeData::ParameterDeclaration(data)) => (
                    data.modifiers
                        .as_ref()
                        .map(|modifiers| modifiers.list.nodes.clone())
                        .unwrap_or_default(),
                    data.dot_dot_dot_token,
                    data.question_token,
                    data.type_,
                    data.initializer,
                    data.name,
                ),
                _ => return,
            };
        for modifier in modifiers {
            self.bind_node(modifier);
        }
        if let Some(dot_dot_dot) = dot_dot_dot {
            self.bind_node(dot_dot_dot);
        }
        if let Some(question) = question {
            self.bind_node(question);
        }
        if let Some(type_) = type_ {
            self.bind_node(type_);
        }
        if let Some(initializer) = initializer {
            self.bind_initializer(initializer);
        }
        self.bind_node(name);
    }

    fn bind_binding_element(&mut self, node_id: NodeId) {
        self.record_node_flow(node_id);
        let (dot_dot_dot, property_name, initializer, name) =
            match self.ast.get(node_id).map(|node| &node.data) {
                Some(NodeData::BindingElement(data)) => (
                    data.dot_dot_dot_token,
                    data.property_name,
                    data.initializer,
                    data.name,
                ),
                _ => return,
            };
        if let Some(dot_dot_dot) = dot_dot_dot {
            self.bind_node(dot_dot_dot);
        }
        if let Some(property_name) = property_name {
            self.bind_node(property_name);
        }
        if let Some(initializer) = initializer {
            self.bind_initializer(initializer);
        }
        if let Some(name) = name {
            self.bind_node(name);
        }
    }

    fn bind_initializer(&mut self, initializer: NodeId) {
        let entry = self.current;
        self.bind_node(initializer);
        let (Some(entry), Some(exit)) = (entry, self.current) else {
            return;
        };
        if entry == exit || self.is_unreachable(entry) {
            return;
        }
        let exit_label = self.alloc_label();
        self.add_antecedent(exit_label, entry);
        self.add_antecedent(exit_label, exit);
        self.current = self.finish_label(exit_label);
    }

    fn bind_prefix_unary_expression(&mut self, node_id: NodeId) {
        let (operand, operator) = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::PrefixUnaryExpression(data)) => (data.operand, data.operator),
            _ => return,
        };
        if operator == SyntaxKind::ExclamationToken {
            std::mem::swap(&mut self.true_target, &mut self.false_target);
            self.bind_node(operand);
            std::mem::swap(&mut self.true_target, &mut self.false_target);
            return;
        }
        self.bind_node(operand);
        if matches!(
            operator,
            SyntaxKind::PlusPlusToken | SyntaxKind::MinusMinusToken
        ) {
            self.bind_assignment_target_flow(operand);
        }
    }

    fn bind_postfix_unary_expression(&mut self, node_id: NodeId) {
        let (operand, operator) = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::PostfixUnaryExpression(data)) => (data.operand, data.operator),
            _ => return,
        };
        self.bind_node(operand);
        if matches!(
            operator,
            SyntaxKind::PlusPlusToken | SyntaxKind::MinusMinusToken
        ) {
            self.bind_assignment_target_flow(operand);
        }
    }

    fn bind_delete_expression(&mut self, node_id: NodeId) {
        let expression = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::DeleteExpression(data)) => data.expression,
            _ => return,
        };
        self.bind_node(expression);
        if self.node_kind(expression) == Some(SyntaxKind::PropertyAccessExpression) {
            self.bind_assignment_target_flow(expression);
        }
    }

    fn bind_call_expression(&mut self, node_id: NodeId) {
        let (expression, question_dot, type_arguments, arguments) =
            match self.ast.get(node_id).map(|node| &node.data) {
                Some(NodeData::CallExpression(data)) => (
                    data.expression,
                    data.question_dot_token,
                    data.type_arguments
                        .as_ref()
                        .map(|arguments| arguments.nodes.clone())
                        .unwrap_or_default(),
                    data.arguments.nodes.clone(),
                ),
                _ => return,
            };
        if let Some(function) = self.directly_invoked_function_target(expression)
            && let Some(kind) = self.unsupported_direct_function_call_kind(function)
        {
            self.mark_unsupported(function, kind);
            return;
        }
        self.bind_node(expression);
        if let Some(question_dot) = question_dot {
            self.bind_node(question_dot);
        }
        for type_argument in type_arguments {
            self.bind_node(type_argument);
        }
        for argument in arguments {
            self.bind_node(argument);
        }
        if self.node_kind(expression) == Some(SyntaxKind::SuperKeyword) {
            self.create_flow_mutation(FlowFlags::CALL, node_id);
        }
        self.bind_array_mutation_call(node_id);
    }

    fn bind_array_mutation_call(&mut self, node_id: NodeId) {
        let expression = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::CallExpression(data)) => data.expression,
            _ => return,
        };
        if let Some((base, name)) = self.property_access_parts(expression)
            && self.is_narrowable_operand(base)
            && matches!(self.identifier_text(name), Some("push" | "unshift"))
        {
            self.create_flow_mutation(FlowFlags::ARRAY_MUTATION, node_id);
        }
    }

    fn bind_assignment_target_flow(&mut self, node_id: NodeId) {
        match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::ArrayLiteralExpression(data)) => {
                let elements = data.elements.nodes.clone();
                for element in elements {
                    if let Some(NodeData::SpreadElement(spread)) =
                        self.ast.get(element).map(|node| &node.data)
                    {
                        self.bind_assignment_target_flow(spread.expression);
                    } else {
                        self.bind_destructuring_target_flow(element);
                    }
                }
            }
            Some(NodeData::ObjectLiteralExpression(data)) => {
                let properties = data.properties.nodes.clone();
                for property in properties {
                    match self.ast.get(property).map(|node| &node.data) {
                        Some(NodeData::PropertyAssignment(data)) => {
                            self.bind_destructuring_target_flow(data.initializer);
                        }
                        Some(NodeData::ShorthandPropertyAssignment(data)) => {
                            self.bind_assignment_target_flow(data.name);
                        }
                        Some(NodeData::SpreadAssignment(data)) => {
                            self.bind_assignment_target_flow(data.expression);
                        }
                        _ => {}
                    }
                }
            }
            _ if self.is_narrowable_reference(node_id) => {
                self.create_flow_mutation(FlowFlags::ASSIGNMENT, node_id);
            }
            _ => {}
        }
    }

    fn bind_destructuring_target_flow(&mut self, node_id: NodeId) {
        let target = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::BinaryExpression(data))
                if self.node_kind(data.operator_token) == Some(SyntaxKind::EqualsToken) =>
            {
                data.left
            }
            _ => node_id,
        };
        self.bind_assignment_target_flow(target);
    }

    fn bind_function_container(&mut self, node_id: NodeId, function: FunctionContainer) {
        if !self.built_containers.insert(node_id) {
            return;
        }
        let saved = self.save_flow();
        self.container = node_id;
        let payload = function
            .start_payload
            .then(|| FlowNodePayload::Ast(self.node_ref(node_id)));
        let start = self.alloc_start(payload);
        self.graph.container_starts.insert(node_id, start);
        self.current = Some(start);
        self.return_target = function.return_target.then(|| self.alloc_label());

        self.bind_children(node_id);
        self.finish_container(node_id, function.body.is_some());
        if let Some(return_target) = self.return_target
            && !self.graph.incomplete_containers.contains(&node_id)
        {
            if let Some(current) = self.current {
                self.add_antecedent(return_target, current);
            }
            if let Some(return_flow) = self.finish_label(return_target) {
                self.graph.container_returns.insert(node_id, return_flow);
            }
        }
        self.restore_flow(saved);
    }

    fn bind_module_block(&mut self, node_id: NodeId) {
        if !self.built_containers.insert(node_id) {
            return;
        }
        let statements = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::ModuleBlock(data)) => data.statements.nodes.clone(),
            _ => return,
        };
        let saved = self.save_flow();
        self.container = node_id;
        let start = self.alloc_start(None);
        self.graph.container_starts.insert(node_id, start);
        self.current = Some(start);
        self.return_target = None;
        self.bind_statement_list(&statements);
        self.restore_flow(saved);
    }

    fn bind_property_initializer_container(&mut self, node_id: NodeId) {
        if !self.built_containers.insert(node_id) {
            return;
        }
        let saved = self.save_flow();
        self.container = node_id;
        let start = self.alloc_start(None);
        self.graph.container_starts.insert(node_id, start);
        self.current = Some(start);
        self.return_target = None;
        self.bind_children(node_id);
        self.restore_flow(saved);
    }

    fn finish_container(&mut self, container: NodeId, records_end: bool) {
        if !records_end || self.graph.incomplete_containers.contains(&container) {
            return;
        }
        if let Some(current) = self.current
            && !self.is_unreachable(current)
        {
            self.graph.container_ends.insert(container, current);
        } else if container == self.container
            && self.node_kind(container) == Some(SyntaxKind::SourceFile)
            && let Some(current) = self.current
        {
            // SourceFile.EndFlowNode is assigned even when the file ends on an
            // unreachable path; function EndFlowNode is not.
            self.graph.container_ends.insert(container, current);
        }
    }

    fn bind_children(&mut self, node_id: NodeId) {
        let children = self.children.get(&node_id).cloned().unwrap_or_default();
        for child in children {
            self.bind_node(child);
        }
    }

    /// Continues the one canonical walk after the current CFG container has
    /// failed closed. Flow recording stays disabled, but every ordinary child
    /// is still entered and exited in pinned binder order. Nested flow
    /// containers may independently build their own graphs and then restore the
    /// disabled outer state.
    fn bind_children_without_flow(&mut self, node_id: NodeId) {
        let saved_in_assignment_pattern = self.in_assignment_pattern;
        self.in_assignment_pattern = false;

        if self.is_destructuring_assignment(node_id) {
            self.in_assignment_pattern = saved_in_assignment_pattern;
            self.bind_destructuring_assignment_children(node_id);
            debug_assert_eq!(self.in_assignment_pattern, saved_in_assignment_pattern);
            return;
        }

        if matches!(
            self.node_kind(node_id),
            Some(
                SyntaxKind::ObjectLiteralExpression
                    | SyntaxKind::ArrayLiteralExpression
                    | SyntaxKind::PropertyAssignment
                    | SyntaxKind::SpreadElement
            )
        ) {
            self.in_assignment_pattern = saved_in_assignment_pattern;
        }
        for child in self.children_in_pinned_order(node_id) {
            self.bind_node(child);
        }
        self.in_assignment_pattern = saved_in_assignment_pattern;
    }

    fn bind_destructuring_assignment_children(&mut self, node_id: NodeId) {
        let (left, type_, operator, right) = match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::BinaryExpression(data)) => {
                (data.left, data.type_, data.operator_token, data.right)
            }
            _ => return,
        };
        if self.in_assignment_pattern {
            self.in_assignment_pattern = false;
            self.bind_node(operator);
            self.bind_node(right);
            self.in_assignment_pattern = true;
            self.bind_node(left);
            if let Some(type_) = type_ {
                self.bind_node(type_);
            }
        } else {
            self.in_assignment_pattern = true;
            self.bind_node(left);
            if let Some(type_) = type_ {
                self.bind_node(type_);
            }
            self.in_assignment_pattern = false;
            self.bind_node(operator);
            self.bind_node(right);
        }
    }

    fn children_in_pinned_order(&self, node_id: NodeId) -> Vec<NodeId> {
        let Some(node) = self.ast.get(node_id) else {
            return Vec::new();
        };
        match &node.data {
            NodeData::SourceFile(data) => {
                let mut children = statements_in_pinned_order(self.ast, &data.statements.nodes);
                children.push(data.end_of_file_token);
                children
            }
            NodeData::Block(data) => statements_in_pinned_order(self.ast, &data.statements.nodes),
            NodeData::ModuleBlock(data) => {
                statements_in_pinned_order(self.ast, &data.statements.nodes)
            }
            NodeData::ForStatement(data) => {
                let mut children = Vec::with_capacity(4);
                children.extend(data.initializer);
                children.extend(data.condition);
                children.push(data.statement);
                children.extend(data.incrementor);
                children
            }
            NodeData::ForInOrOfStatement(data) => {
                let mut children = Vec::with_capacity(4);
                children.push(data.expression);
                if node.kind == SyntaxKind::ForOfStatement
                    && let Some(await_modifier) = data.await_modifier
                {
                    children.push(await_modifier);
                }
                children.push(data.initializer);
                children.push(data.statement);
                children
            }
            NodeData::BinaryExpression(data) => {
                let mut children = Vec::with_capacity(4);
                children.push(data.left);
                children.extend(data.type_);
                children.push(data.operator_token);
                children.push(data.right);
                children
            }
            NodeData::CallExpression(data)
                if !self.is_optional_chain_node(node_id)
                    && self
                        .directly_invoked_function_target(data.expression)
                        .is_some() =>
            {
                let mut children = Vec::new();
                if let Some(type_arguments) = &data.type_arguments {
                    children.extend(type_arguments.nodes.iter().copied());
                }
                children.extend(data.arguments.nodes.iter().copied());
                children.push(data.expression);
                children
            }
            NodeData::ParameterDeclaration(data) => {
                let mut children = Vec::new();
                if let Some(modifiers) = &data.modifiers {
                    children.extend(modifiers.list.nodes.iter().copied());
                }
                children.extend(data.dot_dot_dot_token);
                children.extend(data.question_token);
                children.extend(data.type_);
                children.extend(data.initializer);
                children.push(data.name);
                children
            }
            NodeData::BindingElement(data) => {
                let mut children = Vec::with_capacity(4);
                children.extend(data.dot_dot_dot_token);
                children.extend(data.property_name);
                children.extend(data.initializer);
                children.extend(data.name);
                children
            }
            _ => self.children.get(&node_id).cloned().unwrap_or_default(),
        }
    }

    fn function_container(&self, node_id: NodeId) -> Option<FunctionContainer> {
        let node = self.ast.get(node_id)?;
        let body = match &node.data {
            NodeData::FunctionDeclaration(data) => data.body,
            NodeData::FunctionExpression(data) => Some(data.body),
            NodeData::ArrowFunction(data) => Some(data.body),
            NodeData::MethodDeclaration(data) => data.body,
            NodeData::GetAccessorDeclaration(data) => data.body,
            NodeData::SetAccessorDeclaration(data) => data.body,
            NodeData::ConstructorDeclaration(data) => data.body,
            NodeData::FunctionTypeNode(_)
            | NodeData::ConstructorTypeNode(_)
            | NodeData::CallSignatureDeclaration(_)
            | NodeData::ConstructSignatureDeclaration(_)
            | NodeData::MethodSignatureDeclaration(_) => None,
            _ => return None,
        };
        let return_target = matches!(&node.data, NodeData::ConstructorDeclaration(_));
        let start_payload = matches!(
            &node.data,
            NodeData::FunctionExpression(_) | NodeData::ArrowFunction(_)
        ) || matches!(
            &node.data,
            NodeData::MethodDeclaration(_)
                | NodeData::GetAccessorDeclaration(_)
                | NodeData::SetAccessorDeclaration(_)
        ) && node.parent.is_some_and(|parent| {
            matches!(
                self.ast.get(parent).map(|node| &node.data),
                Some(NodeData::ObjectLiteralExpression(_) | NodeData::ClassExpression(_))
            )
        });
        Some(FunctionContainer {
            body,
            return_target,
            start_payload,
        })
    }

    fn save_flow(&mut self) -> SavedFlow {
        SavedFlow {
            current: self.current,
            container: self.container,
            return_target: self.return_target.take(),
            break_target: self.break_target.take(),
            continue_target: self.continue_target.take(),
            active_labels: std::mem::take(&mut self.active_labels),
            pre_switch_case_flow: self.pre_switch_case_flow.take(),
        }
    }

    fn restore_flow(&mut self, saved: SavedFlow) {
        self.current = saved.current;
        self.container = saved.container;
        self.return_target = saved.return_target;
        self.break_target = saved.break_target;
        self.continue_target = saved.continue_target;
        self.active_labels = saved.active_labels;
        self.pre_switch_case_flow = saved.pre_switch_case_flow;
    }

    fn maybe_bind_expression_flow_if_call(&mut self, expression: NodeId) {
        if self.node_kind(expression) != Some(SyntaxKind::CallExpression) {
            return;
        }
        let call_target = match self.ast.get(expression).map(|node| &node.data) {
            Some(NodeData::CallExpression(data)) => data.expression,
            _ => return,
        };
        if self.node_kind(call_target) != Some(SyntaxKind::SuperKeyword)
            && self.is_dotted_name(call_target)
        {
            self.create_flow_mutation(FlowFlags::CALL, expression);
        }
    }

    fn record_node_flow(&mut self, node_id: NodeId) {
        let Some(current) = self.current else {
            return;
        };
        if self.is_unreachable(current) {
            return;
        }
        self.record_node_flow_including_unreachable(node_id);
    }

    fn record_node_flow_including_unreachable(&mut self, node_id: NodeId) {
        let Some(current) = self.current else {
            return;
        };
        self.graph.node_flows.insert(node_id, current);
        self.graph.node_containers.insert(node_id, self.container);
    }

    fn alloc_start(&mut self, payload: Option<FlowNodePayload>) -> FlowRef {
        let mut node = FlowNode::new(FlowFlags::START);
        node.payload = payload;
        self.graph
            .nodes
            .alloc(node)
            .expect("binder-created start payload belongs to its flow arena")
    }

    fn alloc_label(&mut self) -> FlowRef {
        self.graph
            .nodes
            .alloc(FlowNode::new(FlowFlags::BRANCH_LABEL))
            .expect("binder-created label belongs to its flow arena")
    }

    fn alloc_loop_label(&mut self) -> FlowRef {
        self.graph
            .nodes
            .alloc(FlowNode::new(FlowFlags::LOOP_LABEL))
            .expect("binder-created loop label belongs to its flow arena")
    }

    fn create_flow_condition(
        &mut self,
        flags: FlowFlags,
        antecedent: FlowRef,
        expression: NodeId,
    ) -> FlowRef {
        if self.is_unreachable(antecedent) {
            return antecedent;
        }
        match self.node_kind(expression) {
            Some(SyntaxKind::TrueKeyword) if flags == FlowFlags::FALSE_CONDITION => {
                return self.graph.nodes.unreachable();
            }
            Some(SyntaxKind::FalseKeyword) if flags == FlowFlags::TRUE_CONDITION => {
                return self.graph.nodes.unreachable();
            }
            _ => {}
        }
        if !self.is_narrowing_expression(expression) {
            return antecedent;
        }
        self.graph
            .nodes
            .mark_referenced(antecedent)
            .expect("binder flow antecedent belongs to its file arena");
        self.graph
            .nodes
            .alloc(FlowNode::with_antecedent(
                flags,
                FlowNodePayload::Ast(self.node_ref(expression)),
                antecedent,
            ))
            .expect("binder condition references belong to its flow arena")
    }

    fn create_flow_mutation(&mut self, flags: FlowFlags, node_id: NodeId) {
        let Some(antecedent) = self.current else {
            return;
        };
        if self.is_unreachable(antecedent) {
            return;
        }
        self.graph
            .nodes
            .mark_referenced(antecedent)
            .expect("binder flow antecedent belongs to its file arena");
        let flow = self
            .graph
            .nodes
            .alloc(FlowNode::with_antecedent(
                flags,
                FlowNodePayload::Ast(self.node_ref(node_id)),
                antecedent,
            ))
            .expect("binder mutation references belong to its flow arena");
        self.current = Some(flow);
        self.has_flow_effects = true;
    }

    fn create_flow_switch_clause(
        &mut self,
        antecedent: FlowRef,
        switch_statement: NodeId,
        clause_start: usize,
        clause_end: usize,
    ) -> FlowRef {
        self.graph
            .nodes
            .mark_referenced(antecedent)
            .expect("binder switch-clause antecedent belongs to its flow arena");
        let payload = FlowNodePayload::SwitchClause {
            switch_statement: self.node_ref(switch_statement),
            clause_start: i32::try_from(clause_start)
                .expect("switch clause start fits the upstream i32 payload"),
            clause_end: i32::try_from(clause_end)
                .expect("switch clause end fits the upstream i32 payload"),
        };
        self.graph
            .nodes
            .alloc(FlowNode::with_antecedent(
                FlowFlags::SWITCH_CLAUSE,
                payload,
                antecedent,
            ))
            .expect("binder switch-clause payload belongs to its flow arena")
    }

    fn add_current_antecedent(&mut self, label: FlowRef) -> bool {
        let Some(current) = self.current else {
            return false;
        };
        self.add_antecedent(label, current);
        true
    }

    fn add_antecedent(&mut self, label: FlowRef, antecedent: FlowRef) {
        self.graph
            .nodes
            .add_antecedent(label, antecedent)
            .expect("binder flow label and antecedent belong to its file arena");
    }

    fn finish_label(&self, label: FlowRef) -> Option<FlowRef> {
        self.graph.nodes.finish_label(label)
    }

    fn mark_unsupported(&mut self, node_id: NodeId, kind: UnsupportedFlowKind) {
        let container = self.container;
        self.record_unsupported(node_id, container, kind);
        let dependencies = self
            .effect_dependency_containers
            .iter()
            .copied()
            .filter(|dependency| *dependency != container)
            .collect::<BTreeSet<_>>();
        for dependency in dependencies {
            self.record_unsupported(
                node_id,
                dependency,
                UnsupportedFlowKind::CrossContainerFlowEffects,
            );
        }
        self.current = None;
    }

    fn record_unsupported(
        &mut self,
        node_id: NodeId,
        container: NodeId,
        kind: UnsupportedFlowKind,
    ) {
        let unsupported = UnsupportedFlow {
            node: self.node_ref(node_id),
            container: self.node_ref(container),
            kind,
        };
        if !self.graph.unsupported.contains(&unsupported) {
            self.graph.unsupported.push(unsupported);
        }
        self.graph.incomplete_containers.insert(container);
    }

    fn current_is_unreachable(&self) -> bool {
        self.current.is_some_and(|flow| self.is_unreachable(flow))
    }

    fn is_unreachable(&self, flow: FlowRef) -> bool {
        self.graph
            .nodes
            .get(flow)
            .is_some_and(|node| node.flags.intersects(FlowFlags::UNREACHABLE))
    }

    fn node_ref(&self, node: NodeId) -> NodeRef {
        NodeRef::new(self.graph.node_arena_id(), self.graph.file_id(), node)
    }

    fn node_kind(&self, node: NodeId) -> Option<SyntaxKind> {
        self.ast.get(node).map(|node| node.kind)
    }

    fn is_logical_condition(&self, node_id: NodeId) -> bool {
        let node_id = self.skip_parentheses(node_id);
        match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::BinaryExpression(data)) => self
                .node_kind(data.operator_token)
                .is_some_and(is_logical_operator),
            Some(NodeData::PrefixUnaryExpression(data))
                if data.operator == SyntaxKind::ExclamationToken =>
            {
                self.is_logical_condition(data.operand)
            }
            _ => false,
        }
    }

    fn is_top_level_logical_expression(&self, mut node_id: NodeId) -> bool {
        while let Some(parent) = self.ast.get(node_id).and_then(|node| node.parent) {
            match self.ast.get(parent).map(|node| &node.data) {
                Some(NodeData::ParenthesizedExpression(_)) => node_id = parent,
                Some(NodeData::PrefixUnaryExpression(data))
                    if data.operator == SyntaxKind::ExclamationToken =>
                {
                    node_id = parent;
                }
                _ => break,
            }
        }
        let Some(parent) = self.ast.get(node_id).and_then(|node| node.parent) else {
            return true;
        };
        if self.is_statement_condition(node_id, parent) || self.is_logical_condition(parent) {
            return false;
        }
        !self.is_optional_chain_node(parent)
            || self.optional_chain_expression(parent) != Some(node_id)
    }

    fn is_statement_condition(&self, expression: NodeId, parent: NodeId) -> bool {
        match self.ast.get(parent).map(|node| &node.data) {
            Some(NodeData::IfStatement(data)) => data.expression == expression,
            Some(NodeData::WhileStatement(data)) => data.expression == expression,
            Some(NodeData::DoStatement(data)) => data.expression == expression,
            Some(NodeData::ForStatement(data)) => data.condition == Some(expression),
            Some(NodeData::ConditionalExpression(data)) => data.condition == expression,
            _ => false,
        }
    }

    fn is_optional_chain_node(&self, mut node_id: NodeId) -> bool {
        loop {
            let Some(node) = self.ast.get(node_id) else {
                return false;
            };
            if is_optional_chain(node.kind, node.flags) {
                return true;
            }
            match &node.data {
                NodeData::PropertyAccessExpression(data) => {
                    if data.question_dot_token.is_some() {
                        return true;
                    }
                    node_id = data.expression;
                }
                NodeData::ElementAccessExpression(data) => {
                    if data.question_dot_token.is_some() {
                        return true;
                    }
                    node_id = data.expression;
                }
                NodeData::CallExpression(data) => {
                    if data.question_dot_token.is_some() {
                        return true;
                    }
                    node_id = data.expression;
                }
                NodeData::NonNullExpression(data) => node_id = data.expression,
                _ => return false,
            }
        }
    }

    fn is_optional_chain_root(&self, node_id: NodeId) -> bool {
        match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::PropertyAccessExpression(data)) => data.question_dot_token.is_some(),
            Some(NodeData::ElementAccessExpression(data)) => data.question_dot_token.is_some(),
            Some(NodeData::CallExpression(data)) => data.question_dot_token.is_some(),
            _ => false,
        }
    }

    fn is_outermost_optional_chain(&self, node_id: NodeId) -> bool {
        self.is_optional_chain_node(node_id)
            && self
                .ast
                .get(node_id)
                .and_then(|node| node.parent)
                .is_none_or(|parent| {
                    !self.is_optional_chain_node(parent)
                        || self.is_optional_chain_root(parent)
                        || self.optional_chain_expression(parent) != Some(node_id)
                })
    }

    fn optional_chain_expression(&self, node_id: NodeId) -> Option<NodeId> {
        match self.ast.get(node_id).map(|node| &node.data) {
            Some(NodeData::PropertyAccessExpression(data)) => Some(data.expression),
            Some(NodeData::ElementAccessExpression(data)) => Some(data.expression),
            Some(NodeData::CallExpression(data)) => Some(data.expression),
            Some(NodeData::NonNullExpression(data)) => Some(data.expression),
            _ => None,
        }
    }

    fn is_for_in_or_of_initializer(&self, declaration: NodeId) -> bool {
        let Some(declaration_list) = self.ast.get(declaration).and_then(|node| node.parent) else {
            return false;
        };
        if self.node_kind(declaration_list) != Some(SyntaxKind::VariableDeclarationList) {
            return false;
        }
        let Some(statement) = self.ast.get(declaration_list).and_then(|node| node.parent) else {
            return false;
        };
        matches!(
            self.ast.get(statement).map(|node| &node.data),
            Some(NodeData::ForInOrOfStatement(data)) if data.initializer == declaration_list
        )
    }

    fn is_potentially_executable_node(&self, node_id: NodeId) -> bool {
        let Some(kind) = self.node_kind(node_id) else {
            return false;
        };
        if is_flow_statement(kind) {
            if kind != SyntaxKind::VariableStatement {
                return true;
            }
            let Some(statement_node) = self.ast.get(node_id) else {
                return false;
            };
            let NodeData::VariableStatement(statement) = &statement_node.data else {
                return false;
            };
            let Some(declaration_list) = self.ast.get(statement.declaration_list) else {
                return false;
            };
            let combined_flags = declaration_list.flags.0 | statement_node.flags.0;
            if combined_flags & NODE_FLAGS_BLOCK_SCOPED != 0 {
                return true;
            }
            let NodeData::VariableDeclarationList(declaration_list) = &declaration_list.data else {
                return false;
            };
            return declaration_list
                .declarations
                .nodes
                .iter()
                .any(|declaration| {
                    matches!(
                        self.ast.get(*declaration).map(|node| &node.data),
                        Some(NodeData::VariableDeclaration(data)) if data.initializer.is_some()
                    )
                });
        }
        matches!(
            kind,
            SyntaxKind::ClassDeclaration
                | SyntaxKind::EnumDeclaration
                | SyntaxKind::ModuleDeclaration
        )
    }

    fn is_part_of_type_query(&self, mut node_id: NodeId) -> bool {
        while matches!(
            self.node_kind(node_id),
            Some(SyntaxKind::QualifiedName | SyntaxKind::Identifier)
        ) {
            let Some(parent) = self.ast.get(node_id).and_then(|node| node.parent) else {
                return false;
            };
            node_id = parent;
        }
        self.node_kind(node_id) == Some(SyntaxKind::TypeQuery)
    }

    fn identifier_text(&self, node: NodeId) -> Option<&str> {
        match &self.ast.get(node)?.data {
            NodeData::Identifier(data) => Some(&data.text),
            _ => None,
        }
    }

    fn property_access_parts(&self, node: NodeId) -> Option<(NodeId, NodeId)> {
        let NodeData::PropertyAccessExpression(data) = &self.ast.get(node)?.data else {
            return None;
        };
        Some((data.expression, data.name))
    }

    fn is_narrowing_expression(&self, expression: NodeId) -> bool {
        match self.node_kind(expression) {
            Some(SyntaxKind::Identifier | SyntaxKind::ThisKeyword) => true,
            Some(SyntaxKind::PropertyAccessExpression | SyntaxKind::ElementAccessExpression) => {
                self.contains_narrowable_reference(expression)
            }
            Some(SyntaxKind::CallExpression) => self.has_narrowable_argument(expression),
            Some(
                SyntaxKind::ParenthesizedExpression
                | SyntaxKind::NonNullExpression
                | SyntaxKind::TypeOfExpression,
            ) => self
                .expression_child(expression)
                .is_some_and(|child| self.is_narrowing_expression(child)),
            Some(SyntaxKind::BinaryExpression) => self.is_narrowing_binary_expression(expression),
            Some(SyntaxKind::PrefixUnaryExpression) => {
                match &self.ast.get(expression).expect("known AST node").data {
                    NodeData::PrefixUnaryExpression(data)
                        if data.operator == SyntaxKind::ExclamationToken =>
                    {
                        self.is_narrowing_expression(data.operand)
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn contains_narrowable_reference(&self, expression: NodeId) -> bool {
        self.is_narrowable_reference(expression)
    }

    fn is_narrowable_reference(&self, node_id: NodeId) -> bool {
        match self.node_kind(node_id) {
            Some(
                SyntaxKind::Identifier
                | SyntaxKind::ThisKeyword
                | SyntaxKind::SuperKeyword
                | SyntaxKind::MetaProperty,
            ) => true,
            Some(
                SyntaxKind::PropertyAccessExpression
                | SyntaxKind::ParenthesizedExpression
                | SyntaxKind::NonNullExpression,
            ) => self
                .expression_child(node_id)
                .is_some_and(|expression| self.is_narrowable_reference(expression)),
            Some(SyntaxKind::ElementAccessExpression) => {
                let NodeData::ElementAccessExpression(data) =
                    &self.ast.get(node_id).expect("known AST node").data
                else {
                    return false;
                };
                self.is_string_or_numeric_literal(data.argument_expression)
                    || self.is_entity_name_expression(data.argument_expression)
                        && self.is_narrowable_reference(data.expression)
            }
            Some(SyntaxKind::BinaryExpression) => {
                let NodeData::BinaryExpression(data) =
                    &self.ast.get(node_id).expect("known AST node").data
                else {
                    return false;
                };
                match self.node_kind(data.operator_token) {
                    Some(SyntaxKind::CommaToken) => self.is_narrowable_reference(data.right),
                    Some(operator) if operator.is_assignment_operator() => {
                        self.is_left_hand_side_expression(data.left)
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    fn is_left_hand_side_expression(&self, mut node_id: NodeId) -> bool {
        while let Some(NodeData::PartiallyEmittedExpression(data)) =
            self.ast.get(node_id).map(|node| &node.data)
        {
            node_id = data.expression;
        }
        matches!(
            self.node_kind(node_id),
            Some(
                SyntaxKind::PropertyAccessExpression
                    | SyntaxKind::ElementAccessExpression
                    | SyntaxKind::NewExpression
                    | SyntaxKind::CallExpression
                    | SyntaxKind::JsxElement
                    | SyntaxKind::JsxSelfClosingElement
                    | SyntaxKind::JsxFragment
                    | SyntaxKind::TaggedTemplateExpression
                    | SyntaxKind::ArrayLiteralExpression
                    | SyntaxKind::ParenthesizedExpression
                    | SyntaxKind::ObjectLiteralExpression
                    | SyntaxKind::ClassExpression
                    | SyntaxKind::FunctionExpression
                    | SyntaxKind::Identifier
                    | SyntaxKind::PrivateIdentifier
                    | SyntaxKind::RegularExpressionLiteral
                    | SyntaxKind::NumericLiteral
                    | SyntaxKind::BigIntLiteral
                    | SyntaxKind::StringLiteral
                    | SyntaxKind::NoSubstitutionTemplateLiteral
                    | SyntaxKind::TemplateExpression
                    | SyntaxKind::FalseKeyword
                    | SyntaxKind::NullKeyword
                    | SyntaxKind::ThisKeyword
                    | SyntaxKind::TrueKeyword
                    | SyntaxKind::SuperKeyword
                    | SyntaxKind::NonNullExpression
                    | SyntaxKind::ExpressionWithTypeArguments
                    | SyntaxKind::MetaProperty
                    | SyntaxKind::ImportKeyword
                    | SyntaxKind::MissingDeclaration
            )
        )
    }

    fn has_narrowable_argument(&self, call: NodeId) -> bool {
        let NodeData::CallExpression(data) = &self.ast.get(call).expect("known call node").data
        else {
            return false;
        };
        data.arguments
            .nodes
            .iter()
            .any(|argument| self.contains_narrowable_reference(*argument))
            || self
                .property_access_parts(data.expression)
                .is_some_and(|(base, _)| self.contains_narrowable_reference(base))
    }

    fn is_narrowing_binary_expression(&self, expression: NodeId) -> bool {
        let NodeData::BinaryExpression(data) =
            &self.ast.get(expression).expect("known binary node").data
        else {
            return false;
        };
        match self.node_kind(data.operator_token) {
            Some(
                SyntaxKind::EqualsToken
                | SyntaxKind::BarBarEqualsToken
                | SyntaxKind::AmpersandAmpersandEqualsToken
                | SyntaxKind::QuestionQuestionEqualsToken,
            ) => self.contains_narrowable_reference(data.left),
            Some(
                SyntaxKind::EqualsEqualsToken
                | SyntaxKind::ExclamationEqualsToken
                | SyntaxKind::EqualsEqualsEqualsToken
                | SyntaxKind::ExclamationEqualsEqualsToken,
            ) => {
                let left = self.skip_parentheses(data.left);
                let right = self.skip_parentheses(data.right);
                self.is_narrowable_operand(left)
                    || self.is_narrowable_operand(right)
                    || self.is_narrowing_typeof_operands(right, left)
                    || self.is_narrowing_typeof_operands(left, right)
                    || (self.is_boolean_literal(right) && self.is_narrowing_expression(left))
                    || (self.is_boolean_literal(left) && self.is_narrowing_expression(right))
            }
            Some(SyntaxKind::InstanceOfKeyword) => self.is_narrowable_operand(data.left),
            Some(SyntaxKind::InKeyword | SyntaxKind::CommaToken) => {
                self.is_narrowing_expression(data.right)
            }
            _ => false,
        }
    }

    fn is_narrowable_operand(&self, expression: NodeId) -> bool {
        match self.node_kind(expression) {
            Some(SyntaxKind::ParenthesizedExpression) => self
                .expression_child(expression)
                .is_some_and(|child| self.is_narrowable_operand(child)),
            Some(SyntaxKind::BinaryExpression) => {
                let NodeData::BinaryExpression(data) =
                    &self.ast.get(expression).expect("known binary node").data
                else {
                    return false;
                };
                match self.node_kind(data.operator_token) {
                    Some(SyntaxKind::EqualsToken) => self.is_narrowable_operand(data.left),
                    Some(SyntaxKind::CommaToken) => self.is_narrowable_operand(data.right),
                    _ => self.contains_narrowable_reference(expression),
                }
            }
            _ => self.contains_narrowable_reference(expression),
        }
    }

    fn is_narrowing_typeof_operands(&self, first: NodeId, second: NodeId) -> bool {
        self.node_kind(first) == Some(SyntaxKind::TypeOfExpression)
            && self
                .expression_child(first)
                .is_some_and(|operand| self.is_narrowable_operand(operand))
            && matches!(
                self.node_kind(second),
                Some(SyntaxKind::StringLiteral | SyntaxKind::NoSubstitutionTemplateLiteral)
            )
    }

    fn expression_child(&self, node_id: NodeId) -> Option<NodeId> {
        match &self.ast.get(node_id)?.data {
            NodeData::ParenthesizedExpression(data) => Some(data.expression),
            NodeData::NonNullExpression(data) => Some(data.expression),
            NodeData::TypeOfExpression(data) => Some(data.expression),
            NodeData::PropertyAccessExpression(data) => Some(data.expression),
            _ => None,
        }
    }

    fn is_string_or_numeric_literal(&self, node: NodeId) -> bool {
        matches!(
            self.node_kind(node),
            Some(
                SyntaxKind::StringLiteral
                    | SyntaxKind::NoSubstitutionTemplateLiteral
                    | SyntaxKind::NumericLiteral
            )
        )
    }

    fn is_entity_name_expression(&self, node: NodeId) -> bool {
        match self.node_kind(node) {
            Some(SyntaxKind::Identifier) => true,
            Some(SyntaxKind::PropertyAccessExpression) => {
                let Some((base, name)) = self.property_access_parts(node) else {
                    return false;
                };
                self.node_kind(name) == Some(SyntaxKind::Identifier)
                    && self.is_entity_name_expression(base)
            }
            _ => false,
        }
    }

    fn is_boolean_literal(&self, node: NodeId) -> bool {
        matches!(
            self.node_kind(node),
            Some(SyntaxKind::TrueKeyword | SyntaxKind::FalseKeyword)
        )
    }

    fn is_dotted_name(&self, node: NodeId) -> bool {
        match self.node_kind(node) {
            Some(
                SyntaxKind::Identifier
                | SyntaxKind::ThisKeyword
                | SyntaxKind::SuperKeyword
                | SyntaxKind::MetaProperty,
            ) => true,
            Some(SyntaxKind::PropertyAccessExpression | SyntaxKind::ParenthesizedExpression) => {
                self.expression_child(node)
                    .is_some_and(|expression| self.is_dotted_name(expression))
            }
            _ => false,
        }
    }

    fn is_assignment_target(&self, mut node_id: NodeId) -> bool {
        loop {
            let Some(parent) = self.ast.get(node_id).and_then(|node| node.parent) else {
                return false;
            };
            match &self.ast.get(parent).expect("parent node exists").data {
                NodeData::BinaryExpression(data) => {
                    return self
                        .node_kind(data.operator_token)
                        .is_some_and(SyntaxKind::is_assignment_operator)
                        && data.left == node_id;
                }
                NodeData::PrefixUnaryExpression(data) => {
                    return matches!(
                        data.operator,
                        SyntaxKind::PlusPlusToken | SyntaxKind::MinusMinusToken
                    );
                }
                NodeData::PostfixUnaryExpression(data) => {
                    return matches!(
                        data.operator,
                        SyntaxKind::PlusPlusToken | SyntaxKind::MinusMinusToken
                    );
                }
                NodeData::ForInOrOfStatement(data) => {
                    return data.initializer == node_id;
                }
                NodeData::PropertyAssignment(data) => {
                    if data.name == node_id {
                        return false;
                    }
                    node_id = parent;
                }
                NodeData::ShorthandPropertyAssignment(data) => {
                    if data.name != node_id {
                        return false;
                    }
                    node_id = parent;
                }
                NodeData::ParenthesizedExpression(_)
                | NodeData::ArrayLiteralExpression(_)
                | NodeData::ObjectLiteralExpression(_)
                | NodeData::SpreadAssignment(_)
                | NodeData::SpreadElement(_)
                | NodeData::NonNullExpression(_) => node_id = parent,
                _ => return false,
            }
        }
    }

    fn is_destructuring_assignment(&self, node_id: NodeId) -> bool {
        let Some(NodeData::BinaryExpression(data)) = self.ast.get(node_id).map(|node| &node.data)
        else {
            return false;
        };
        self.node_kind(data.operator_token) == Some(SyntaxKind::EqualsToken)
            && matches!(
                self.node_kind(data.left),
                Some(SyntaxKind::ArrayLiteralExpression | SyntaxKind::ObjectLiteralExpression)
            )
    }

    fn skip_parentheses(&self, mut node: NodeId) -> NodeId {
        while let Some(NodeData::ParenthesizedExpression(data)) =
            self.ast.get(node).map(|node| &node.data)
        {
            node = data.expression;
        }
        node
    }

    fn directly_invoked_function_target(&self, expression: NodeId) -> Option<NodeId> {
        let expression = self.skip_parentheses(expression);
        matches!(
            self.node_kind(expression),
            Some(SyntaxKind::FunctionExpression | SyntaxKind::ArrowFunction)
        )
        .then_some(expression)
    }

    fn unsupported_direct_function_call_kind(
        &self,
        function: NodeId,
    ) -> Option<UnsupportedFlowKind> {
        if self.supported_async_arrow_invocation(function)
            || self.supported_immediately_invoked_closure(function)
        {
            return None;
        }
        self.is_directly_invoked_function(function).then(|| {
            if self.is_immediately_invoked_function(function) {
                UnsupportedFlowKind::ImmediatelyInvokedFunction
            } else {
                UnsupportedFlowKind::DirectFunctionCall
            }
        })
    }

    #[allow(clippy::too_many_lines)] // Authenticate the complete async IIFE and throwing body.
    fn supported_async_arrow_invocation(&self, function: NodeId) -> bool {
        let Some(function_record) = self.ast.get(function) else {
            return false;
        };
        let NodeData::ArrowFunction(arrow) = &function_record.data else {
            return false;
        };
        let Some(modifiers) = arrow.modifiers.as_ref() else {
            return false;
        };
        let [modifier] = modifiers.list.nodes.as_slice() else {
            return false;
        };
        let Some(modifier_record) = self.ast.get(*modifier) else {
            return false;
        };
        let Some(parenthesized) = function_record.parent else {
            return false;
        };
        let Some(parenthesized_record) = self.ast.get(parenthesized) else {
            return false;
        };
        let NodeData::ParenthesizedExpression(parenthesized_expression) =
            &parenthesized_record.data
        else {
            return false;
        };
        let Some(call) = parenthesized_record.parent else {
            return false;
        };
        let Some(call_record) = self.ast.get(call) else {
            return false;
        };
        let NodeData::CallExpression(invocation) = &call_record.data else {
            return false;
        };
        let Some(body_record) = self.ast.get(arrow.body) else {
            return false;
        };
        let NodeData::Block(body) = &body_record.data else {
            return false;
        };
        let [await_statement, throw_statement] = body.statements.nodes.as_slice() else {
            return false;
        };
        let Some(await_statement_record) = self.ast.get(*await_statement) else {
            return false;
        };
        let NodeData::ExpressionStatement(await_statement_data) = &await_statement_record.data
        else {
            return false;
        };
        let Some(await_record) = self.ast.get(await_statement_data.expression) else {
            return false;
        };
        let NodeData::AwaitExpression(awaited) = &await_record.data else {
            return false;
        };
        let Some(operand) = self.ast.get(awaited.expression) else {
            return false;
        };
        let NodeData::NumericLiteral(number) = &operand.data else {
            return false;
        };
        let Some(throw_record) = self.ast.get(*throw_statement) else {
            return false;
        };
        let NodeData::ThrowStatement(thrown) = &throw_record.data else {
            return false;
        };
        let Some(construction) = self.ast.get(thrown.expression) else {
            return false;
        };
        let NodeData::NewExpression(new_expression) = &construction.data else {
            return false;
        };
        let Some(arguments) = new_expression.arguments.as_ref() else {
            return false;
        };
        let Some(name) = self.ast.get(new_expression.expression) else {
            return false;
        };
        let NodeData::Identifier(identifier) = &name.data else {
            return false;
        };

        function_record.kind == SyntaxKind::ArrowFunction
            && function_record.flags.0 == 0
            && arrow.parameters.nodes.is_empty()
            && !arrow.parameters.has_trailing_comma
            && arrow.type_parameters.is_none()
            && arrow.type_.is_none()
            && modifiers.flags.0 == 0
            && !modifiers.list.has_trailing_comma
            && modifier_record.kind == SyntaxKind::AsyncKeyword
            && modifier_record.flags.0 == 0
            && modifier_record.parent == Some(function)
            && matches!(modifier_record.data, NodeData::Token(_))
            && parenthesized_record.kind == SyntaxKind::ParenthesizedExpression
            && parenthesized_record.flags.0 == 0
            && parenthesized_expression.expression == function
            && call_record.kind == SyntaxKind::CallExpression
            && call_record.flags.0 == 0
            && invocation.expression == parenthesized
            && invocation.arguments.nodes.is_empty()
            && !invocation.arguments.has_trailing_comma
            && invocation.type_arguments.is_none()
            && invocation.question_dot_token.is_none()
            && invocation.symbol.is_none()
            && invocation.facts == 0
            && body_record.kind == SyntaxKind::Block
            && body_record.flags.0 == 0
            && body_record.parent == Some(function)
            && !body.statements.has_trailing_comma
            && await_statement_record.kind == SyntaxKind::ExpressionStatement
            && await_statement_record.flags.0 == 0
            && await_statement_record.parent == Some(arrow.body)
            && await_statement_data.flow_node.is_none()
            && await_record.kind == SyntaxKind::AwaitExpression
            && await_record.flags.0 == 0
            && await_record.parent == Some(*await_statement)
            && operand.kind == SyntaxKind::NumericLiteral
            && operand.flags.0 == 0
            && operand.parent == Some(await_statement_data.expression)
            && number.token_flags.0 == 0
            && throw_record.kind == SyntaxKind::ThrowStatement
            && throw_record.flags.0 == 0
            && throw_record.parent == Some(arrow.body)
            && thrown.flow_node.is_none()
            && thrown.facts == 0
            && construction.kind == SyntaxKind::NewExpression
            && construction.flags.0 == 0
            && construction.parent == Some(*throw_statement)
            && arguments.nodes.is_empty()
            && !arguments.has_trailing_comma
            && new_expression.type_arguments.is_none()
            && new_expression.facts == 0
            && name.kind == SyntaxKind::Identifier
            && name.flags.0 == 0
            && name.parent == Some(thrown.expression)
            && identifier.text == "Error"
            && identifier.flow_node.is_none()
    }

    /// Keeps authenticated zero-argument closure calls inside their real flow containers.
    fn supported_immediately_invoked_closure(&self, function: NodeId) -> bool {
        if self.current.is_none_or(|flow| self.is_unreachable(flow)) {
            return false;
        }
        let Some(record) = self.ast.get(function) else {
            return false;
        };
        let parameters = match &record.data {
            NodeData::FunctionExpression(data)
                if record.kind == SyntaxKind::FunctionExpression
                    && data.name.is_none()
                    && data.asterisk_token.is_none()
                    && data.type_parameters.is_none() =>
            {
                &data.parameters
            }
            NodeData::ArrowFunction(data)
                if record.kind == SyntaxKind::ArrowFunction
                    && data.asterisk_token.is_none()
                    && data.type_parameters.is_none() =>
            {
                &data.parameters
            }
            _ => return false,
        };
        if record.flags.0 != 0 || !parameters.nodes.is_empty() || parameters.has_trailing_comma {
            return false;
        }

        let mut expression = function;
        loop {
            let Some(parent) = self.ast.get(expression).and_then(|node| node.parent) else {
                return false;
            };
            let Some(parent_record) = self.ast.get(parent) else {
                return false;
            };
            if parent_record.flags.0 != 0 {
                return false;
            }
            match &parent_record.data {
                NodeData::ParenthesizedExpression(parenthesized)
                    if parent_record.kind == SyntaxKind::ParenthesizedExpression
                        && parenthesized.expression == expression =>
                {
                    expression = parent;
                }
                NodeData::CallExpression(call)
                    if parent_record.kind == SyntaxKind::CallExpression
                        && call.expression == expression =>
                {
                    return call.arguments.nodes.is_empty()
                        && !call.arguments.has_trailing_comma
                        && call.arguments.range.end == parent_record.range.end
                        && call.question_dot_token.is_none()
                        && call.symbol.is_none()
                        && call.type_arguments.is_none()
                        && call.facts == 0;
                }
                _ => return false,
            }
        }
    }

    fn is_immediately_invoked_function(&self, function: NodeId) -> bool {
        self.is_directly_invoked_function(function)
            && !self.is_async_function(function)
            && !self.is_generator_function_expression(function)
    }

    fn is_directly_invoked_function(&self, function: NodeId) -> bool {
        let mut expression = function;
        loop {
            let Some(parent) = self.ast.get(expression).and_then(|node| node.parent) else {
                return false;
            };
            match &self.ast.get(parent).expect("parent node exists").data {
                NodeData::ParenthesizedExpression(data) if data.expression == expression => {
                    expression = parent;
                }
                NodeData::CallExpression(data) => return data.expression == expression,
                _ => return false,
            }
        }
    }

    fn is_async_function(&self, function: NodeId) -> bool {
        let modifiers = match &self.ast.get(function).expect("known function node").data {
            NodeData::FunctionExpression(data) if data.asterisk_token.is_none() => &data.modifiers,
            NodeData::ArrowFunction(data) if data.asterisk_token.is_none() => &data.modifiers,
            _ => return false,
        };
        modifiers.as_ref().is_some_and(|modifiers| {
            modifiers
                .list
                .nodes
                .iter()
                .any(|modifier| self.node_kind(*modifier) == Some(SyntaxKind::AsyncKeyword))
        })
    }

    fn is_generator_function_expression(&self, function: NodeId) -> bool {
        matches!(
            self.ast.get(function).map(|node| &node.data),
            Some(NodeData::FunctionExpression(data)) if data.asterisk_token.is_some()
        )
    }
}

fn statements_in_pinned_order(ast: &NodeArena, statements: &[NodeId]) -> Vec<NodeId> {
    let mut ordered = Vec::with_capacity(statements.len());
    ordered.extend(statements.iter().copied().filter(|statement| {
        ast.get(*statement)
            .is_some_and(|node| node.kind == SyntaxKind::FunctionDeclaration)
    }));
    ordered.extend(statements.iter().copied().filter(|statement| {
        ast.get(*statement)
            .is_none_or(|node| node.kind != SyntaxKind::FunctionDeclaration)
    }));
    ordered
}

const NODE_FLAG_LET: u32 = 1 << 0;
const NODE_FLAG_CONST: u32 = 1 << 1;
const NODE_FLAG_USING: u32 = 1 << 2;
const NODE_FLAGS_BLOCK_SCOPED: u32 = NODE_FLAG_LET | NODE_FLAG_CONST | NODE_FLAG_USING;

fn is_flow_statement(kind: SyntaxKind) -> bool {
    (kind as u16) >= (SyntaxKind::FIRST_STATEMENT as u16)
        && (kind as u16) <= (SyntaxKind::LAST_STATEMENT as u16)
}

fn is_logical_operator(kind: SyntaxKind) -> bool {
    matches!(
        kind,
        SyntaxKind::AmpersandAmpersandToken
            | SyntaxKind::BarBarToken
            | SyntaxKind::QuestionQuestionToken
            | SyntaxKind::AmpersandAmpersandEqualsToken
            | SyntaxKind::BarBarEqualsToken
            | SyntaxKind::QuestionQuestionEqualsToken
    )
}

fn is_optional_chain(kind: SyntaxKind, flags: NodeFlags) -> bool {
    flags.0 & (1 << 5) != 0
        && matches!(
            kind,
            SyntaxKind::PropertyAccessExpression
                | SyntaxKind::ElementAccessExpression
                | SyntaxKind::CallExpression
                | SyntaxKind::NonNullExpression
        )
}

#[cfg(test)]
mod tests {
    use ts_ast::{FileId, FlowFlags, FlowNodePayload, NodeArena, NodeData, NodeRef, SyntaxKind};
    use ts_parser::parse_source_file;

    use crate::{BoundFlowGraph, UnsupportedFlowKind, bind_source_file_in_file};

    fn assigned_identifiers<'arena>(
        arena: &'arena NodeArena,
        graph: &BoundFlowGraph,
    ) -> Vec<&'arena str> {
        graph
            .nodes()
            .iter()
            .filter(|flow| flow.flags.contains(FlowFlags::ASSIGNMENT))
            .filter_map(|flow| {
                let Some(FlowNodePayload::Ast(node)) = flow.payload.as_ref() else {
                    return None;
                };
                let Some(NodeData::Identifier(identifier)) =
                    arena.get(node.node).map(|node| &node.data)
                else {
                    return None;
                };
                Some(identifier.text.as_str())
            })
            .collect()
    }

    #[test]
    fn exact_async_arrow_iife_keeps_outer_and_arrow_flow_complete() {
        let parsed = parse_source_file(concat!(
            "function run() {\n",
            "  (async () => {\n",
            "    await 10\n",
            "    throw new Error();\n",
            "  })();\n",
            "  var value = 1;\n",
            "}",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(150);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .expect("program-bound source has a flow graph");

        assert!(graph.is_complete(), "{:?}", graph.unsupported());
        for kind in [SyntaxKind::FunctionDeclaration, SyntaxKind::ArrowFunction] {
            let declaration = parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap();
            assert_eq!(graph.container_is_complete(declaration), Some(true));
            assert!(graph.container_start(declaration).is_some());
        }
    }

    #[test]
    fn authenticated_loop_iifes_keep_outer_and_closure_flow_complete() {
        for (index, source) in [
            concat!(
                "function iterate(value: object) { ",
                "for (let key in value) { (function () { return key; })(); } ",
                "}",
            ),
            concat!(
                "function count() { ",
                "for (let index = 0; index < 1; ++index) { ",
                "(() => [index] = [index + 1])(); ",
                "} }",
            ),
            concat!(
                "(function () { ",
                "\"use strict\"; ",
                "for (let index = 0; index < 1; ++index) { (() => index)(); } ",
                "})();",
            ),
            "(async () => 1)();",
            concat!(
                "function f1() { ",
                "(async () => { await 10; throw new Error(); })(); ",
                "var value = 1; ",
                "}",
            ),
        ]
        .into_iter()
        .enumerate()
        {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{source}");
            let file = FileId::new(160 + u32::try_from(index).unwrap());
            let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
            let graph = result
                .flow_graph(&parsed.arena, parsed.source_file)
                .expect("program-bound source has a flow graph");

            assert!(graph.is_complete(), "{source}: {:?}", graph.unsupported());
            for (node, record) in parsed.arena.iter() {
                if !matches!(
                    record.kind,
                    SyntaxKind::FunctionDeclaration
                        | SyntaxKind::FunctionExpression
                        | SyntaxKind::ArrowFunction
                ) {
                    continue;
                }
                let node = NodeRef::new(parsed.arena.id(), file, node);
                assert_eq!(graph.container_is_complete(node), Some(true), "{source}");
                assert!(graph.container_start(node).is_some(), "{source}");
            }
        }
    }

    #[test]
    fn direct_destructuring_assigns_nested_defaults_and_rest_targets_in_order() {
        let parsed = parse_source_file(concat!(
            "({ first: [first = fallback, nested, ...arrayRest], ",
            "shorthand, ...objectRest } = source); after;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);

        let file = FileId::new(140);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .expect("program-bound source has a flow graph");

        assert!(graph.is_complete(), "{:?}", graph.unsupported());
        assert_eq!(
            assigned_identifiers(&parsed.arena, graph),
            ["first", "nested", "arrayRest", "shorthand", "objectRest"]
        );
    }

    #[test]
    fn destructuring_defaults_bind_effects_before_assignment_targets() {
        let parsed = parse_source_file(concat!(
            "({ item: assigned = (fallback = 1), ",
            "shorthand = (secondFallback = 2) } = (source = input));",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);

        let file = FileId::new(141);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .expect("program-bound source has a flow graph");

        assert!(graph.is_complete(), "{:?}", graph.unsupported());
        assert_eq!(
            assigned_identifiers(&parsed.arena, graph),
            [
                "fallback",
                "secondFallback",
                "source",
                "assigned",
                "shorthand"
            ]
        );
    }

    #[test]
    fn nested_destructuring_defaults_preserve_assignment_pattern_order() {
        let parsed =
            parse_source_file("([[nested] = (fallback = input), trailing] = (source = value));");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);

        let file = FileId::new(142);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .expect("program-bound source has a flow graph");

        assert!(graph.is_complete(), "{:?}", graph.unsupported());
        assert_eq!(
            assigned_identifiers(&parsed.arena, graph),
            ["fallback", "nested", "source", "nested", "trailing"]
        );
    }

    #[test]
    fn nested_destructuring_in_default_expressions_starts_a_new_assignment_pattern() {
        for source in [
            "([target = ([inner = (left = 1)] = (right = 2)), trailing] = source);",
            "({ target = ([inner = (left = 1)] = (right = 2)), trailing } = source);",
        ] {
            let parsed = parse_source_file(source);
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);

            let file = FileId::new(145);
            let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
            let graph = result
                .flow_graph(&parsed.arena, parsed.source_file)
                .expect("program-bound source has a flow graph");

            assert!(graph.is_complete(), "{:?}", graph.unsupported());
            assert_eq!(
                assigned_identifiers(&parsed.arena, graph),
                ["left", "right", "inner", "target", "trailing"],
                "{source}"
            );
        }
    }

    #[test]
    fn nested_function_containers_do_not_inherit_assignment_pattern_state() {
        let parsed = parse_source_file(concat!(
            "([target = (() => ([inner = (left = 1)] = (right = 2))), ",
            "trailing] = source);",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);

        let file = FileId::new(146);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .expect("program-bound source has a flow graph");

        assert!(graph.is_complete(), "{:?}", graph.unsupported());
        assert_eq!(
            assigned_identifiers(&parsed.arena, graph),
            ["left", "right", "inner", "target", "trailing"]
        );
    }

    #[test]
    fn object_destructuring_assigns_private_properties_without_assigning_keys() {
        let parsed = parse_source_file(concat!(
            "class Example { #state = { value: 0 }; ",
            "update(source: { value: { value: number } }) { ",
            "({ value: this.#state } = source); } }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);

        let file = FileId::new(143);
        let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
        let graph = result
            .flow_graph(&parsed.arena, parsed.source_file)
            .expect("program-bound source has a flow graph");

        assert!(graph.is_complete(), "{:?}", graph.unsupported());
        let (property_name, target) = parsed
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::PropertyAssignment(property) = &node.data else {
                    return None;
                };
                let Some(NodeData::PropertyAccessExpression(access)) = parsed
                    .arena
                    .get(property.initializer)
                    .map(|node| &node.data)
                else {
                    return None;
                };
                (parsed.arena.get(access.name)?.kind == SyntaxKind::PrivateIdentifier)
                    .then_some((property.name, property.initializer))
            })
            .expect("destructuring pattern has a private-property assignment");
        let target = NodeRef::new(parsed.arena.id(), file, target);
        let property_name = NodeRef::new(parsed.arena.id(), file, property_name);

        assert!(graph.nodes().iter().any(|flow| {
            flow.flags.contains(FlowFlags::ASSIGNMENT)
                && flow.payload == Some(FlowNodePayload::Ast(target))
        }));
        assert!(!graph.nodes().iter().any(|flow| {
            flow.flags.contains(FlowFlags::ASSIGNMENT)
                && flow.payload == Some(FlowNodePayload::Ast(property_name))
        }));
    }

    #[test]
    fn compound_destructuring_assignment_remains_unsupported() {
        for operator in [
            SyntaxKind::PlusEqualsToken,
            SyntaxKind::AmpersandAmpersandEqualsToken,
            SyntaxKind::BarBarEqualsToken,
            SyntaxKind::QuestionQuestionEqualsToken,
        ] {
            let mut parsed = parse_source_file("([value] = source); after;");
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let operator_node = parsed
                .arena
                .iter()
                .find_map(|(_, node)| match &node.data {
                    NodeData::BinaryExpression(binary)
                        if parsed.arena.get(binary.left).is_some_and(|left| {
                            left.kind == SyntaxKind::ArrayLiteralExpression
                        }) =>
                    {
                        Some(binary.operator_token)
                    }
                    _ => None,
                })
                .expect("the fixture contains one array destructuring assignment");
            parsed.arena.get_mut(operator_node).unwrap().kind = operator;

            let file = FileId::new(144);
            let result = bind_source_file_in_file(&parsed.arena, parsed.source_file, file);
            let graph = result
                .flow_graph(&parsed.arena, parsed.source_file)
                .expect("program-bound source has a flow graph");

            assert!(!graph.is_complete(), "operator: {operator:?}");
            assert_eq!(graph.unsupported().len(), 1, "operator: {operator:?}");
            assert_eq!(
                graph.unsupported()[0].kind,
                UnsupportedFlowKind::DestructuringAssignment,
                "operator: {operator:?}"
            );
            assert_eq!(
                parsed
                    .arena
                    .get(graph.unsupported()[0].node.node)
                    .unwrap()
                    .kind,
                SyntaxKind::BinaryExpression,
                "operator: {operator:?}"
            );
        }
    }
}
