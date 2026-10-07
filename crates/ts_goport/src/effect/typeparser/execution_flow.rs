//! Port of Effect-TS/tsgo `internal/typeparser/execution_flow.go`.

use crate::effect::graph::{Graph, NodeIndex};
use crate::effect::typeparser::*;
use crate::prelude::*;

/// Go `ExecutionNodeKind`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExecutionNodeKind {
    Value,
    Function,
    LogicMerge,
    Transform,
}

impl ExecutionNodeKind {
    /// The Go string value.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            ExecutionNodeKind::Value => "value",
            ExecutionNodeKind::Function => "function",
            ExecutionNodeKind::LogicMerge => "logicMerge",
            ExecutionNodeKind::Transform => "transform",
        }
    }
}

/// Go `ExecutionNode`.
#[derive(Clone)]
pub struct ExecutionNode {
    pub kind: ExecutionNodeKind,
    pub node: Node,
    pub type_: TypeId,

    // Transform nodes preserve the original AST in Node and optionally expose a
    // normalized callee/args view once the visitor reaches that node.
    pub callee: Node,
    pub args: Vec<Node>,
}

/// Go `ExecutionLinkKind`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExecutionLinkKind {
    UsedBy,
    Pipe,
    PotentialReturn,
    Yieldable,
    Parameter,
    TransformArg,
    TransformCallee,
}

impl ExecutionLinkKind {
    /// The Go string value.
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            ExecutionLinkKind::UsedBy => "usedBy",
            ExecutionLinkKind::Pipe => "pipe",
            ExecutionLinkKind::PotentialReturn => "potentialReturn",
            ExecutionLinkKind::Yieldable => "yieldable",
            ExecutionLinkKind::Parameter => "parameter",
            ExecutionLinkKind::TransformArg => "transformArg",
            ExecutionLinkKind::TransformCallee => "transformCallee",
        }
    }
}

/// Go `ExecutionLink`.
#[derive(Clone)]
pub struct ExecutionLink {
    pub kind: ExecutionLinkKind,
    pub node: Node,
}

/// Go `ExecutionFlow = graph.Graph[ExecutionNode, ExecutionLink]`.
pub type ExecutionFlow = Graph<ExecutionNode, ExecutionLink>;

/// Go `GraphSlice`.
/// PORT: Go `Leading` and `Trailing` are `*graph.NodeIndex` that are always
/// set (`buildSlice`, or copied from another slice) and only read through
/// `*`, so the port keeps the index values.
#[derive(Clone, Copy, Debug)]
pub struct GraphSlice {
    pub leading: NodeIndex,
    pub trailing: NodeIndex,
}

/// Go `executionCollector`.
/// PORT: Go `g` is the `*ExecutionFlow` that `ExecutionFlow` returns; the
/// collector owns it here and `ExecutionFlow` takes it at the end. Go
/// `parsed` is a `core.LinkStore[*ast.Node, *GraphSlice]`: a present key
/// with `None` is a stored Go nil.
pub struct ExecutionCollector<'a, 'c> {
    pub tp: &'a mut TypeParser<'c>,
    pub g: ExecutionFlow,
    pub parsed: FxHashMap<Node, Option<Rc<GraphSlice>>>,
    pub usage_target: Option<Rc<GraphSlice>>,
}

/// Go pointer equality of two `*GraphSlice`.
fn same_graph_slice(a: &Option<Rc<GraphSlice>>, b: &Option<Rc<GraphSlice>>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b)) => Rc::ptr_eq(a, b),
        _ => false,
    }
}

impl ExecutionCollector<'_, '_> {
    pub fn build_slice(&mut self, node: ExecutionNode) -> Option<Rc<GraphSlice>> {
        let node_index = self.g.add_node(node);
        Some(Rc::new(GraphSlice {
            leading: node_index,
            trailing: node_index,
        }))
    }

    pub fn build_value_node(&mut self, node: Node) -> Option<Rc<GraphSlice>> {
        let type_ = self.tp.get_type_at_location(node);
        self.build_slice(ExecutionNode {
            kind: ExecutionNodeKind::Value,
            node,
            type_,
            callee: Node::NIL,
            args: Vec::new(),
        })
    }

    pub fn extract_callee_and_args(&mut self, node: Node) -> (Node, Vec<Node>) {
        if is_parenthesized_expression(node) {
            return self.extract_callee_and_args(node.expression());
        } else if is_call_expression(node) {
            return (node.expression(), node.arguments().to_vec());
        }
        (node, Vec::new())
    }

    pub fn connect_slices(
        &mut self,
        from_slice: Option<Rc<GraphSlice>>,
        to_slice: Option<Rc<GraphSlice>>,
        kind: ExecutionLinkKind,
    ) -> Option<Rc<GraphSlice>> {
        let Some(from) = from_slice else {
            return to_slice;
        };
        let Some(to) = to_slice else {
            return Some(from);
        };
        if from.trailing == to.leading {
            return Some(Rc::new(GraphSlice {
                leading: from.leading,
                trailing: to.trailing,
            }));
        }
        self.g.add_edge(
            from.trailing,
            to.leading,
            ExecutionLink {
                kind,
                node: Node::NIL,
            },
        );
        Some(Rc::new(GraphSlice {
            leading: from.leading,
            trailing: to.trailing,
        }))
    }

    pub fn visit_node(&mut self, node: Node) -> Option<Rc<GraphSlice>> {
        // avoid double traversal
        if node.is_nil() {
            return None;
        }
        if let Some(s) = self.parsed.get(&node) {
            return s.clone();
        }

        let previous_usage_target = self.usage_target.take();

        // actual visit logic
        let s;
        if let Some(parsed_effect_gen) = self.tp.effect_gen_call(node) {
            s = self.visit_effect_gen_call(&parsed_effect_gen, node);
        } else if let Some(parsed_effect_fn) = self.tp.effect_fn_call(node) {
            s = self.visit_effect_fn_call(&parsed_effect_fn, node);
        } else if let Some(parsed_pipe_call) = self.tp.parse_pipe_call(node) {
            s = self.visit_pipe_call(&parsed_pipe_call, node);
        } else if let Some(parsed_single_arg) = self.tp.single_arg_inline_call(node) {
            s = self.visit_single_arg_inline_call(&parsed_single_arg, node);
        } else if let Some(parsed_data_first_or_last) = self.tp.data_first_or_last_call(node) {
            s = self.visit_data_first_or_last_call(&parsed_data_first_or_last, node);
        } else if is_function_like_declaration(node) {
            s = self.visit_function_like_declaration(node);
        } else {
            s = self.visit_expression_node(node, previous_usage_target.clone());
        }
        // store to avoid double-traversal
        self.parsed.insert(node, s.clone());
        self.usage_target = previous_usage_target;

        s
    }

    pub fn visit_nodes_and_connect_slice(
        &mut self,
        nodes: &[Node],
        target_slice: Option<Rc<GraphSlice>>,
        kind: ExecutionLinkKind,
    ) -> bool {
        for n in nodes {
            self.visit_node_and_connect_slice(*n, target_slice.clone(), kind);
        }
        false
    }

    pub fn visit_node_and_connect_slice(
        &mut self,
        n: Node,
        target_slice: Option<Rc<GraphSlice>>,
        kind: ExecutionLinkKind,
    ) -> bool {
        let node_slice = self.visit_node(n);
        self.connect_slices(node_slice, target_slice, kind);
        false
    }

    pub fn visit_node_visitor_connect_usage_target(&mut self, node: Node) -> bool {
        if node.is_nil() {
            return false;
        }
        let s = self.visit_node(node);
        let usage_target = self.usage_target.clone();
        self.connect_slices(s, usage_target, ExecutionLinkKind::UsedBy);
        false
    }

    pub fn visit_each_child_with_usage_target(
        &mut self,
        node: Node,
        target: Option<Rc<GraphSlice>>,
    ) -> bool {
        if node.is_nil() {
            return false;
        }
        let previous = std::mem::replace(&mut self.usage_target, target);
        node.for_each_child(|child| self.visit_node_visitor_connect_usage_target(child));
        self.usage_target = previous;
        false
    }

    pub fn visit_expression_node(
        &mut self,
        node: Node,
        parent_expression: Option<Rc<GraphSlice>>,
    ) -> Option<Rc<GraphSlice>> {
        let mut root_expr = parent_expression.clone();
        if parent_expression.is_none()
            && is_expression_node(node)
            && !is_inside_type_only_heritage_expression(node)
        {
            root_expr = self.build_value_node(node);
        }
        self.visit_each_child_with_usage_target(node, root_expr.clone());
        if !same_graph_slice(&root_expr, &parent_expression) {
            return root_expr;
        }
        None
    }

    pub fn visit_pipe_call(
        &mut self,
        p: &ParsedPipeCallResult,
        _node: Node,
    ) -> Option<Rc<GraphSlice>> {
        let mut s = self.visit_node(p.subject);
        for (i, piped_transform) in p.args.iter().copied().enumerate() {
            // TODO: OOB argsouttype check
            let (callee, args) = self.extract_callee_and_args(piped_transform);
            let transform_slice = self.build_slice(ExecutionNode {
                kind: ExecutionNodeKind::Transform,
                node: piped_transform,
                type_: p.args_out_type[i],
                callee,
                args: args.clone(),
            });
            self.parsed.insert(piped_transform, transform_slice.clone());
            self.visit_node_and_connect_slice(
                callee,
                transform_slice.clone(),
                ExecutionLinkKind::TransformCallee,
            );
            self.visit_nodes_and_connect_slice(
                &args,
                transform_slice.clone(),
                ExecutionLinkKind::TransformArg,
            );
            s = self.connect_slices(s, transform_slice, ExecutionLinkKind::Pipe);
        }
        s
    }

    pub fn visit_effect_gen_call(
        &mut self,
        p: &EffectGenCallResult,
        node: Node,
    ) -> Option<Rc<GraphSlice>> {
        let type_ = self.tp.get_type_at_location(node);
        let s = self.build_slice(ExecutionNode {
            kind: ExecutionNodeKind::LogicMerge,
            node,
            type_,
            callee: Node::NIL,
            args: Vec::new(),
        });
        for_each_return_statement(p.body, |stmt| {
            if stmt.kind() == SyntaxKind::ReturnStatement {
                self.visit_node_and_connect_slice(
                    stmt.expression(),
                    s.clone(),
                    ExecutionLinkKind::PotentialReturn,
                );
            }
            false
        });
        for_each_yield_expression(p.body, &mut |expr: Node| -> bool {
            if expr.is_some() && expr.expression().is_some() {
                self.parsed.insert(expr, None);
                self.visit_node_and_connect_slice(
                    expr.expression(),
                    s.clone(),
                    ExecutionLinkKind::Yieldable,
                );
            }
            false
        });
        if p.body.is_some() {
            self.visit_each_child_with_usage_target(p.body, s.clone());
        }
        s
    }

    pub fn visit_effect_fn_call(
        &mut self,
        p: &EffectFnCallResult,
        node: Node,
    ) -> Option<Rc<GraphSlice>> {
        let mut s_exit = self.build_slice(ExecutionNode {
            kind: ExecutionNodeKind::LogicMerge,
            node: p.function_node,
            type_: p.function_return_type,
            callee: Node::NIL,
            args: Vec::new(),
        });
        for (i, piped_transform) in p.pipe_arguments.iter().copied().enumerate() {
            let (callee, args) = self.extract_callee_and_args(piped_transform);
            let transform_slice = self.build_slice(ExecutionNode {
                kind: ExecutionNodeKind::Transform,
                node: piped_transform,
                type_: p.pipe_args_out_type[i], // TODO: OOB?
                callee,
                args: args.clone(),
            });
            self.parsed.insert(piped_transform, transform_slice.clone());
            self.visit_node_and_connect_slice(
                callee,
                transform_slice.clone(),
                ExecutionLinkKind::TransformCallee,
            );
            self.visit_nodes_and_connect_slice(
                &args,
                transform_slice.clone(),
                ExecutionLinkKind::TransformArg,
            );
            s_exit = self.connect_slices(s_exit, transform_slice, ExecutionLinkKind::Pipe);
        }
        if p.is_generator() {
            for_each_yield_expression(p.body(), &mut |expr: Node| -> bool {
                if expr.is_some() && expr.expression().is_some() {
                    self.parsed.insert(expr, None);
                    self.visit_node_and_connect_slice(
                        expr.expression(),
                        s_exit.clone(),
                        ExecutionLinkKind::Yieldable,
                    );
                }
                false
            });
        }
        if is_expression_node(p.body()) {
            self.visit_node_and_connect_slice(p.body(), s_exit.clone(), ExecutionLinkKind::Pipe);
        } else {
            for_each_return_statement(p.body(), |stmt| {
                if stmt.kind() == SyntaxKind::ReturnStatement {
                    self.visit_node_and_connect_slice(
                        stmt.expression(),
                        s_exit.clone(),
                        ExecutionLinkKind::PotentialReturn,
                    );
                }
                false
            });
            self.visit_each_child_with_usage_target(p.body(), s_exit.clone());
        }
        // function with parameters
        let type_ = self.tp.get_type_at_location(node);
        let s = self.build_slice(ExecutionNode {
            kind: ExecutionNodeKind::Function,
            node,
            type_,
            callee: Node::NIL,
            args: Vec::new(),
        });
        for arg in p.function_node.parameters().to_vec() {
            self.visit_node_and_connect_slice(arg, s.clone(), ExecutionLinkKind::Parameter);
        }
        self.connect_slices(s_exit, s.clone(), ExecutionLinkKind::PotentialReturn);
        s
    }

    pub fn visit_single_arg_inline_call(
        &mut self,
        p: &ParsedSingleArgInlineCallTransform,
        node: Node,
    ) -> Option<Rc<GraphSlice>> {
        let mut s = self.visit_node(p.subject);
        let (callee, args) = self.extract_callee_and_args(p.transform);
        let type_ = self.tp.get_type_at_location(node);
        let transform_slice = self.build_slice(ExecutionNode {
            kind: ExecutionNodeKind::Transform,
            node: p.transform,
            type_,
            callee,
            args: args.clone(),
        });
        s = self.connect_slices(s, transform_slice.clone(), ExecutionLinkKind::Pipe);
        self.visit_node_and_connect_slice(
            callee,
            transform_slice.clone(),
            ExecutionLinkKind::TransformCallee,
        );
        self.visit_nodes_and_connect_slice(&args, transform_slice, ExecutionLinkKind::TransformArg);
        s
    }

    pub fn visit_data_first_or_last_call(
        &mut self,
        p: &ParsedDataFirstOrLastCall,
        node: Node,
    ) -> Option<Rc<GraphSlice>> {
        let mut s = self.visit_node(p.subject);
        let type_ = self.tp.get_type_at_location(node);
        let transform_slice = self.build_slice(ExecutionNode {
            kind: ExecutionNodeKind::Transform,
            node,
            type_,
            callee: Node::NIL,
            args: Vec::new(),
        });
        s = self.connect_slices(s, transform_slice, ExecutionLinkKind::Pipe);
        self.visit_node_and_connect_slice(p.callee, s.clone(), ExecutionLinkKind::TransformCallee);
        self.visit_nodes_and_connect_slice(&p.args, s.clone(), ExecutionLinkKind::TransformArg);
        s
    }

    pub fn visit_function_like_declaration(&mut self, node: Node) -> Option<Rc<GraphSlice>> {
        let type_ = self.tp.get_type_at_location(node);
        let s = self.build_slice(ExecutionNode {
            kind: ExecutionNodeKind::Function,
            node,
            type_,
            callee: Node::NIL,
            args: Vec::new(),
        });
        self.visit_nodes_and_connect_slice(
            &node.parameters().to_vec(),
            s.clone(),
            ExecutionLinkKind::Parameter,
        );
        let fn_body = node.body();
        if fn_body.is_some() {
            if is_expression_node(fn_body) {
                self.visit_node_and_connect_slice(
                    fn_body,
                    s.clone(),
                    ExecutionLinkKind::PotentialReturn,
                );
            } else {
                for_each_return_statement(fn_body, |stmt| {
                    if stmt.kind() == SyntaxKind::ReturnStatement {
                        self.visit_node_and_connect_slice(
                            stmt.expression(),
                            s.clone(),
                            ExecutionLinkKind::PotentialReturn,
                        );
                    }
                    false
                });
                self.visit_each_child_with_usage_target(fn_body, s.clone());
            }
        }
        s
    }
}

/// Go `parsedSingleArgInlineCallTransform`.
pub struct ParsedSingleArgInlineCallTransform {
    pub subject: Node,
    pub transform: Node,
}

impl TypeParser<'_> {
    /// Go `ExecutionFlow`.
    /// PORT: the Go `tp == nil || tp.checker == nil` guard cannot fail here.
    pub fn execution_flow(&mut self, sf: Node) -> Option<Rc<ExecutionFlow>> {
        if sf.is_nil() {
            return None;
        }

        cached!(self, execution_flow, sf, {
            let mut ec = ExecutionCollector {
                tp: &mut *self,
                g: Graph::new(),
                parsed: FxHashMap::default(),
                usage_target: None,
            };
            ec.visit_node(sf);
            Some(Rc::new(ec.g))
        })
    }

    pub fn single_arg_inline_call(
        &mut self,
        node: Node,
    ) -> Option<Rc<ParsedSingleArgInlineCallTransform>> {
        if node.is_nil() {
            return None;
        }
        if node.kind() != SyntaxKind::CallExpression {
            return None;
        }
        // Go `outerCallExpr := node.AsCallExpression()`.
        let outer_call_expr_expression = node.expression();
        if outer_call_expr_expression.is_nil() {
            return None;
        }
        let outer_call_args = node.arguments();
        if outer_call_args.len() != 1 {
            return None;
        }
        let called_expr_type = self.get_type_at_location(outer_call_expr_expression);
        if called_expr_type.is_nil() {
            return None;
        }
        let call_sigs = self.checker.get_call_signatures(called_expr_type);
        if call_sigs.len() != 1 {
            return None;
        }
        let params_len = self.checker.sig(call_sigs[0]).parameters.len();
        if params_len != 1 {
            return None;
        }

        Some(Rc::new(ParsedSingleArgInlineCallTransform {
            subject: outer_call_args.get(0),
            transform: outer_call_expr_expression,
        }))
    }
}
