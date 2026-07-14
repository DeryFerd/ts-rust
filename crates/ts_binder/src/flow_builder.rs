use std::collections::{BTreeSet, HashMap};

use ts_ast::{
    FileId, FlowFlags, FlowNode, FlowNodePayload, FlowRef, NodeArena, NodeData, NodeFlags, NodeId,
    NodeRef, SyntaxKind,
};

use crate::{BoundFlowGraph, UnsupportedFlow, UnsupportedFlowKind};

pub(super) fn build_flow_graph(
    arena: &NodeArena,
    children: &HashMap<NodeId, Vec<NodeId>>,
    source_file: NodeId,
    file: FileId,
) -> BoundFlowGraph {
    FlowBuilder::new(arena, children, file).build(source_file)
}

#[derive(Clone, Copy)]
struct SavedFlow {
    current: Option<FlowRef>,
    container: NodeId,
    return_target: Option<FlowRef>,
}

#[derive(Clone, Copy)]
struct FunctionContainer {
    body: Option<NodeId>,
    return_target: bool,
    start_payload: bool,
}

struct FlowBuilder<'a> {
    ast: &'a NodeArena,
    children: &'a HashMap<NodeId, Vec<NodeId>>,
    graph: BoundFlowGraph,
    current: Option<FlowRef>,
    container: NodeId,
    return_target: Option<FlowRef>,
    has_flow_effects: bool,
    effect_dependency_containers: Vec<NodeId>,
    built_containers: BTreeSet<NodeId>,
}

impl<'a> FlowBuilder<'a> {
    fn new(ast: &'a NodeArena, children: &'a HashMap<NodeId, Vec<NodeId>>, file: FileId) -> Self {
        Self {
            ast,
            children,
            graph: BoundFlowGraph::new(ast.id(), file),
            current: None,
            container: NodeId::new(0),
            return_target: None,
            has_flow_effects: false,
            effect_dependency_containers: Vec::new(),
            built_containers: BTreeSet::new(),
        }
    }

    fn build(mut self, source_file: NodeId) -> BoundFlowGraph {
        self.container = source_file;
        self.built_containers.insert(source_file);
        let start = self.alloc_start(None);
        self.graph.container_starts.insert(source_file, start);
        self.current = Some(start);

        let Some(NodeData::SourceFile(source)) = self.ast.get(source_file).map(|node| &node.data)
        else {
            return self.graph;
        };
        let statements = source.statements.nodes.clone();
        let end_of_file = source.end_of_file_token;
        self.bind_statement_list(&statements);
        self.bind_node(end_of_file);
        self.finish_container(source_file, true);
        self.graph
    }

    fn bind_node(&mut self, node_id: NodeId) {
        let Some(node) = self.ast.get(node_id) else {
            self.mark_unsupported(node_id, UnsupportedFlowKind::DestructuringAssignment);
            return;
        };
        let kind = node.kind;
        let flags = node.flags;

        if kind == SyntaxKind::ClassStaticBlockDeclaration {
            self.mark_unsupported(node_id, UnsupportedFlowKind::ClassStaticBlock);
            self.discover_nested_containers(node_id);
            return;
        }

        if let Some(function) = self.function_container(node_id) {
            if let Some(kind) = self.unsupported_direct_function_call_kind(node_id) {
                self.mark_unsupported(node_id, kind);
                self.discover_nested_containers(node_id);
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
            self.discover_nested_containers(node_id);
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

        if is_optional_chain(kind, flags) {
            self.mark_unsupported(node_id, UnsupportedFlowKind::OptionalChain);
            self.discover_nested_containers(node_id);
            return;
        }

        self.bind_node_by_kind(node_id, kind);
    }

    fn bind_node_by_kind(&mut self, node_id: NodeId, kind: SyntaxKind) {
        match kind {
            SyntaxKind::WhileStatement
            | SyntaxKind::DoStatement
            | SyntaxKind::ForStatement
            | SyntaxKind::ForInStatement
            | SyntaxKind::ForOfStatement => {
                self.mark_unsupported(node_id, UnsupportedFlowKind::IterationStatement);
                self.discover_nested_containers(node_id);
            }
            SyntaxKind::SwitchStatement | SyntaxKind::CaseBlock => {
                self.mark_unsupported(node_id, UnsupportedFlowKind::SwitchStatement);
                self.discover_nested_containers(node_id);
            }
            SyntaxKind::TryStatement | SyntaxKind::CatchClause => {
                self.mark_unsupported(node_id, UnsupportedFlowKind::TryStatement);
                self.discover_nested_containers(node_id);
            }
            SyntaxKind::BreakStatement | SyntaxKind::ContinueStatement => {
                self.mark_unsupported(node_id, UnsupportedFlowKind::BreakOrContinueStatement);
            }
            SyntaxKind::LabeledStatement => {
                self.mark_unsupported(node_id, UnsupportedFlowKind::LabeledStatement);
                self.discover_nested_containers(node_id);
            }
            SyntaxKind::WithStatement => {
                self.mark_unsupported(node_id, UnsupportedFlowKind::WithStatement);
                self.discover_nested_containers(node_id);
            }
            SyntaxKind::SourceFile => {}
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
            self.discover_nested_containers(then_statement);
            if let Some(else_statement) = else_statement {
                self.discover_nested_containers(else_statement);
            }
            return;
        }
        let Some(then_flow) = self.finish_label(then_label) else {
            return;
        };
        self.current = Some(then_flow);
        self.bind_node(then_statement);
        if !self.add_current_antecedent(post_if_label) {
            if let Some(else_statement) = else_statement {
                self.discover_nested_containers(else_statement);
            }
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
        self.bind_node(expression);
        let Some(current) = self.current else {
            return;
        };
        let true_flow = self.create_flow_condition(FlowFlags::TRUE_CONDITION, current, expression);
        let false_flow =
            self.create_flow_condition(FlowFlags::FALSE_CONDITION, current, expression);
        self.add_antecedent(true_target, true_flow);
        self.add_antecedent(false_target, false_flow);
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
            self.discover_nested_containers(when_true);
            self.discover_nested_containers(when_false);
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
        if is_logical_operator(operator) {
            self.mark_unsupported(node_id, UnsupportedFlowKind::LogicalExpression);
            self.discover_nested_containers(node_id);
            return;
        }
        if operator.is_assignment_operator()
            && matches!(
                self.node_kind(left),
                Some(SyntaxKind::ArrayLiteralExpression | SyntaxKind::ObjectLiteralExpression)
            )
        {
            self.mark_unsupported(node_id, UnsupportedFlowKind::DestructuringAssignment);
            self.discover_nested_containers(node_id);
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
        if initializer.is_some()
            && matches!(
                self.node_kind(name),
                Some(SyntaxKind::ObjectBindingPattern | SyntaxKind::ArrayBindingPattern)
            )
        {
            self.mark_unsupported(node_id, UnsupportedFlowKind::DestructuringAssignment);
            self.discover_nested_containers(node_id);
            return;
        }
        self.bind_node(name);
        if let Some(exclamation) = exclamation {
            self.bind_node(exclamation);
        }
        if let Some(type_) = type_ {
            self.bind_node(type_);
        }
        if let Some(initializer) = initializer {
            self.bind_node(initializer);
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
        if initializer.is_some()
            && matches!(
                self.node_kind(name),
                Some(SyntaxKind::ObjectBindingPattern | SyntaxKind::ArrayBindingPattern)
            )
        {
            self.mark_unsupported(node_id, UnsupportedFlowKind::DestructuringAssignment);
            self.discover_nested_containers(node_id);
            return;
        }
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
        if initializer.is_some() {
            self.mark_unsupported(node_id, UnsupportedFlowKind::DestructuringAssignment);
            self.discover_nested_containers(node_id);
            return;
        }
        if let Some(dot_dot_dot) = dot_dot_dot {
            self.bind_node(dot_dot_dot);
        }
        if let Some(property_name) = property_name {
            self.bind_node(property_name);
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
        if let Some(function) = self.directly_invoked_function_target(expression) {
            let kind = self
                .unsupported_direct_function_call_kind(function)
                .expect("direct function call target has an unsupported boundary kind");
            self.mark_unsupported(function, kind);
            self.discover_nested_containers(node_id);
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
        if let Some((base, name)) = self.property_access_parts(expression)
            && self.is_narrowable_operand(base)
            && matches!(self.identifier_text(name), Some("push" | "unshift"))
        {
            self.create_flow_mutation(FlowFlags::ARRAY_MUTATION, node_id);
        }
    }

    fn bind_assignment_target_flow(&mut self, node_id: NodeId) {
        if self.is_narrowable_reference(node_id) {
            self.create_flow_mutation(FlowFlags::ASSIGNMENT, node_id);
        }
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

    fn discover_nested_containers(&mut self, node_id: NodeId) {
        let children = self.children.get(&node_id).cloned().unwrap_or_default();
        for child in children {
            if let Some(function) = self.function_container(child) {
                if let Some(kind) = self.unsupported_direct_function_call_kind(child) {
                    self.mark_unsupported(child, kind);
                    self.discover_nested_containers(child);
                } else {
                    if function.start_payload {
                        self.record_node_flow_including_unreachable(child);
                    }
                    self.bind_function_container(child, function);
                }
            } else if self.node_kind(child) == Some(SyntaxKind::ClassStaticBlockDeclaration) {
                self.mark_unsupported(child, UnsupportedFlowKind::ClassStaticBlock);
                self.discover_nested_containers(child);
            } else if self.node_kind(child) == Some(SyntaxKind::ModuleBlock) {
                self.bind_module_block(child);
            } else if self.node_kind(child) == Some(SyntaxKind::PropertyDeclaration)
                && matches!(
                    self.ast.get(child).map(|node| &node.data),
                    Some(NodeData::PropertyDeclaration(data)) if data.initializer.is_some()
                )
            {
                self.bind_property_initializer_container(child);
            } else {
                self.discover_nested_containers(child);
            }
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

    fn save_flow(&self) -> SavedFlow {
        SavedFlow {
            current: self.current,
            container: self.container,
            return_target: self.return_target,
        }
    }

    fn restore_flow(&mut self, saved: SavedFlow) {
        self.current = saved.current;
        self.container = saved.container;
        self.return_target = saved.return_target;
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
                NodeData::ParenthesizedExpression(_)
                | NodeData::ArrayLiteralExpression(_)
                | NodeData::SpreadElement(_)
                | NodeData::NonNullExpression(_) => node_id = parent,
                _ => return false,
            }
        }
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
        self.is_directly_invoked_function(function).then(|| {
            if self.is_immediately_invoked_function(function) {
                UnsupportedFlowKind::ImmediatelyInvokedFunction
            } else {
                UnsupportedFlowKind::DirectFunctionCall
            }
        })
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
