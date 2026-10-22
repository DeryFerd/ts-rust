//! Port of Effect-TS/tsgo `internal/rewriter/piping_flow.go`: edits that
//! replace or collapse the steps of a piping flow while keeping how each
//! step's input is applied in source.

use rustc_hash::FxHashMap;

use crate::ast::visitor::{NodeVisitorHooks, new_node_visitor};
use crate::effect::ls::rewriter::Tracker;
use crate::effect::typeparser::{
    PipingFlow, PipingFlowTransformation, TransformationKind, applied_call_of,
    piping_flow_transformation_call,
};
use crate::prelude::*;

// Go: rewriter/piping_flow.go:11 PipingFlowTransformationReplacement
/// PipingFlowTransformationReplacement describes a replacement operator in its
/// normalized, pipeable form. A nil Arguments list represents a bare operator;
/// a non-nil list represents a call, including an explicit zero-argument call.
// PORT: Go nil lists are `NodeList::NIL`; a list from `new_node_list(&[])`
// is an empty list that is not nil.
#[derive(Clone, Copy, Debug)]
pub struct PipingFlowTransformationReplacement {
    pub callee: Node,
    pub type_arguments: NodeList,
    pub arguments: NodeList,
}

impl PipingFlowTransformationReplacement {
    /// A bare operator: Go `{Callee: callee}`.
    #[must_use]
    pub fn callee(callee: Node) -> Self {
        PipingFlowTransformationReplacement {
            callee,
            type_arguments: NodeList::NIL,
            arguments: NodeList::NIL,
        }
    }
}

impl Tracker {
    // Go: rewriter/piping_flow.go:20 ReplacePipingFlowPrefix
    /// ReplacePipingFlowPrefix replaces the subject and the requested leading
    /// transformations with a complete replacement expression while retaining any
    /// transformations that follow the prefix.
    // PORT: Go's nil tracker, file and flow checks are gone: Rust references
    // are never nil, and the caller skips a match without a flow.
    pub fn replace_piping_flow_prefix(
        &mut self,
        source_file: Node,
        flow: &PipingFlow,
        transformation_count: i32,
        replacement_subject: Node,
    ) -> bool {
        if replacement_subject.is_nil()
            || transformation_count <= 0
            || transformation_count as usize > flow.transformations.len()
        {
            return false;
        }

        let last = &flow.transformations[transformation_count as usize - 1];
        let transformation_node = piping_flow_transformation_node(last);
        let target = match last.kind {
            TransformationKind::Call
            | TransformationKind::DataFirst
            | TransformationKind::DataLast => transformation_node,
            TransformationKind::Pipe => {
                return self.replace_function_pipe_prefix(
                    source_file,
                    transformation_node,
                    replacement_subject,
                );
            }
            TransformationKind::Pipeable => {
                return self.replace_method_pipe_prefix(
                    source_file,
                    transformation_node,
                    replacement_subject,
                );
            }
            _ => return false,
        };
        if target.is_nil() {
            return false;
        }

        set_parent_in_children(replacement_subject);
        self.replace_node(source_file, target, replacement_subject, None);
        true
    }

    // Go: rewriter/piping_flow.go:55 replaceFunctionPipePrefix
    fn replace_function_pipe_prefix(
        &mut self,
        source_file: Node,
        last_transformation: Node,
        replacement_subject: Node,
    ) -> bool {
        let (call_node, argument_index) = containing_call_argument(last_transformation);
        if call_node.is_nil() || argument_index < 1 {
            return false;
        }

        let f = self.node_factory();
        let remaining_arguments =
            clone_node_list_nodes_from(f, call_node.argument_list(), argument_index as usize + 1);
        let mut replacement = replacement_subject;
        if !remaining_arguments.is_empty() {
            let mut arguments = vec![replacement_subject];
            arguments.extend(remaining_arguments);
            replacement = f.new_call_expression(
                f.deep_clone_node(call_node.expression()),
                f.deep_clone_node(call_node.question_dot_token()),
                clone_node_list(f, call_node.type_argument_list()),
                f.new_node_list(&arguments),
                call_node.flags(),
            );
        }
        set_parent_in_children(replacement);
        self.replace_node(source_file, call_node, replacement, None);
        true
    }

    // Go: rewriter/piping_flow.go:78 replaceMethodPipePrefix
    fn replace_method_pipe_prefix(
        &mut self,
        source_file: Node,
        last_transformation: Node,
        replacement_subject: Node,
    ) -> bool {
        let (call_node, argument_index) = containing_call_argument(last_transformation);
        if call_node.is_nil() || argument_index < 0 {
            return false;
        }
        let access = call_node.expression();
        // Go: rewriter/piping_flow.go:83 `call.Expression.AsPropertyAccessExpression()`
        // panics on another kind (`ParsePipeCall` makes a pipeable step only
        // from a property access).
        if access.kind() != SyntaxKind::PropertyAccessExpression {
            go_node_as_panic(access, "PropertyAccessExpression");
        }
        if access.name().is_nil() {
            return false;
        }

        let f = self.node_factory();
        let remaining_arguments =
            clone_node_list_nodes_from(f, call_node.argument_list(), argument_index as usize + 1);
        let mut replacement = replacement_subject;
        if !remaining_arguments.is_empty() {
            let replacement_access = f.new_property_access_expression(
                replacement_subject,
                f.deep_clone_node(access.question_dot_token()),
                f.deep_clone_node(access.name()),
                access.flags(),
            );
            replacement = f.new_call_expression(
                replacement_access,
                f.deep_clone_node(call_node.question_dot_token()),
                clone_node_list(f, call_node.type_argument_list()),
                f.new_node_list(&remaining_arguments),
                call_node.flags(),
            );
        }
        set_parent_in_children(replacement);
        self.replace_node(source_file, call_node, replacement, None);
        true
    }
}

// Go: rewriter/piping_flow.go:110 containingCallArgument
/// The first call up from `node` whose argument list holds the child on the
/// way, and the child's index; `(NIL, -1)` when there is none.
// PORT: Go also returns the `*ast.CallExpression` view of the call node.
fn containing_call_argument(node: Node) -> (Node, i32) {
    let mut child = node;
    while child.is_some() && child.parent().is_some() {
        let parent = child.parent();
        if is_call_expression(parent) && parent.argument_list().is_some() {
            for (index, argument) in parent.arguments().iter().enumerate() {
                if argument == child {
                    return (parent, index as i32);
                }
            }
        }
        child = parent;
    }
    (Node::NIL, -1)
}

// Go: rewriter/piping_flow.go:129 pipingFlowTransformationNode
// PORT: Go's own `callExpressionForCallee` and `appliedCallExpression` are
// copies of typeparser `pipingFlowTransformationCall` and `appliedCallOf`;
// the port calls those.
fn piping_flow_transformation_node(transformation: &PipingFlowTransformation) -> Node {
    if transformation.callee.is_nil() {
        return Node::NIL;
    }
    let mut call = piping_flow_transformation_call(Some(transformation));
    if transformation.kind == TransformationKind::Call {
        // Curried factories decompose into a factory call and a trailing
        // application; the replaced node is the outermost applied call.
        call = applied_call_of(call);
    }
    if call.is_some() {
        return call;
    }
    transformation.callee
}

impl Tracker {
    // Go: rewriter/piping_flow.go:176 ReplacePipingFlowTransformation
    /// ReplacePipingFlowTransformation replaces a transformation while preserving
    /// how its input is applied in source: as a pipe argument, a data-first or
    /// data-last argument, or a unary/curried application.
    pub fn replace_piping_flow_transformation(
        &mut self,
        source_file: Node,
        transformation: &PipingFlowTransformation,
        replacement: PipingFlowTransformationReplacement,
    ) -> bool {
        if replacement.callee.is_nil() {
            return false;
        }
        let transformation_node = piping_flow_transformation_node(transformation);
        if transformation_node.is_nil() {
            return false;
        }

        let f = self.node_factory();
        let replacement_node = match transformation.kind {
            TransformationKind::Pipe
            | TransformationKind::Pipeable
            | TransformationKind::EffectFn
            | TransformationKind::EffectFnUntraced => piping_flow_operator(f, replacement),

            TransformationKind::DataFirst | TransformationKind::DataLast => {
                // Go: rewriter/piping_flow.go:200 `transformationNode.AsCallExpression()`
                // panics when the node is not a call (the callee fallback).
                if !is_call_expression(transformation_node) {
                    go_node_as_panic(transformation_node, "CallExpression");
                }
                if transformation_node.argument_list().is_nil()
                    || transformation_node.arguments().is_empty()
                {
                    return false;
                }
                let call_arguments = transformation_node.arguments();
                let mut arguments = clone_node_list_nodes(f, replacement.arguments);
                let subject_index = if transformation.kind == TransformationKind::DataLast {
                    call_arguments.len() - 1
                } else {
                    0
                };
                let subject = f.deep_clone_node(call_arguments.get(subject_index));
                if transformation.kind == TransformationKind::DataFirst {
                    arguments.insert(0, subject);
                } else {
                    arguments.push(subject);
                }
                f.new_call_expression(
                    replacement.callee,
                    Node::NIL,
                    replacement.type_arguments,
                    f.new_node_list(&arguments),
                    NodeFlags::NONE,
                )
            }

            TransformationKind::Call => {
                // Go: rewriter/piping_flow.go:227 `transformationNode.AsCallExpression()`
                // panics when the node is not a call (the callee fallback).
                if !is_call_expression(transformation_node) {
                    go_node_as_panic(transformation_node, "CallExpression");
                }
                if transformation_node.argument_list().is_nil()
                    || transformation_node.arguments().len() != 1
                {
                    return false;
                }
                let operator = piping_flow_operator(f, replacement);
                f.new_call_expression(
                    operator,
                    Node::NIL,
                    NodeList::NIL,
                    f.new_node_list(&[f.deep_clone_node(transformation_node.arguments().get(0))]),
                    NodeFlags::NONE,
                )
            }
        };
        set_parent_in_children(replacement_node);
        self.replace_node(source_file, transformation_node, replacement_node, None);
        true
    }
}

// Go: rewriter/piping_flow.go:247 pipingFlowOperator
// PORT: a Go `*Tracker` method that only uses the factory.
fn piping_flow_operator(f: &NodeFactory, replacement: PipingFlowTransformationReplacement) -> Node {
    if replacement.arguments.is_nil() && replacement.type_arguments.is_nil() {
        return replacement.callee;
    }
    f.new_call_expression(
        replacement.callee,
        Node::NIL,
        replacement.type_arguments,
        replacement.arguments,
        NodeFlags::NONE,
    )
}

// Go: rewriter/piping_flow.go:260 cloneNodeListNodes
fn clone_node_list_nodes(f: &NodeFactory, list: NodeList) -> Vec<Node> {
    list.nodes()
        .iter()
        .map(|node| f.deep_clone_node(node))
        .collect()
}

// Go: rewriter/piping_flow.go:271 cloneNodeListNodesFrom
fn clone_node_list_nodes_from(f: &NodeFactory, list: NodeList, start: usize) -> Vec<Node> {
    let nodes = list.nodes();
    if start >= nodes.len() {
        return Vec::new();
    }
    nodes
        .iter()
        .skip(start)
        .map(|node| f.deep_clone_node(node))
        .collect()
}

// Go: rewriter/piping_flow.go:282 cloneNodeList
fn clone_node_list(f: &NodeFactory, list: NodeList) -> NodeList {
    if list.is_nil() {
        return NodeList::NIL;
    }
    f.new_node_list(&clone_node_list_nodes(f, list))
}

impl Tracker {
    // Go: rewriter/piping_flow.go:292 CollapsePipingFlowTransformations
    /// CollapsePipingFlowTransformations replaces an inclusive range of adjacent
    /// steps with one operator at the last step. Nested applications are rewritten
    /// together so removing an input step cannot overlap the replacement edit.
    pub fn collapse_piping_flow_transformations(
        &mut self,
        source_file: Node,
        flow: &PipingFlow,
        start: i32,
        end: i32,
        replacement: PipingFlowTransformationReplacement,
    ) -> bool {
        if start < 0
            || end < start
            || end as usize >= flow.transformations.len()
            || replacement.callee.is_nil()
        {
            return false;
        }
        let mut steps: FxHashMap<Node, i32> = FxHashMap::default();
        let mut emptied_pipes: FxHashMap<Node, TransformationKind> = FxHashMap::default();
        for i in start..=end {
            let node = piping_flow_transformation_node(&flow.transformations[i as usize]);
            if node.is_nil() {
                return false;
            }
            steps.insert(node, i);
            let kind = flow.transformations[i as usize].kind;
            if i < end && (kind == TransformationKind::Pipe || kind == TransformationKind::Pipeable)
            {
                let (call, _) = containing_call_argument(node);
                emptied_pipes.insert(call, kind);
            }
        }
        // Find the smallest source subtree containing all edited steps. Pipe
        // arguments require their containing call so they can be removed as a list.
        let mut target = piping_flow_transformation_node(&flow.transformations[end as usize]);
        for i in start..=end {
            let mut node = piping_flow_transformation_node(&flow.transformations[i as usize]);
            if is_piping_flow_argument(flow.transformations[i as usize].kind) {
                node = containing_call_argument(node).0;
            }
            if node.is_nil() {
                return false;
            }
            while target.is_some() && !node_within(node, target) {
                target = target.parent();
            }
        }
        if target.is_nil() {
            return false;
        }
        let result = {
            let f = self.node_factory();
            let mut visitor = new_node_visitor(
                |node: Node, v| {
                    let Some(&index) = steps.get(&node) else {
                        let updated = v.visit_each_child(node);
                        if let Some(&kind) = emptied_pipes.get(&node) {
                            // Go: rewriter/piping_flow.go:335 `updated.AsCallExpression()`
                            if !is_call_expression(updated) {
                                go_node_as_panic(updated, "CallExpression");
                            }
                            let arguments = updated.argument_list();
                            if kind == TransformationKind::Pipeable
                                && (arguments.is_nil() || arguments.nodes().is_empty())
                            {
                                // Go: rewriter/piping_flow.go:337
                                // `call.Expression.AsPropertyAccessExpression()`
                                let access = updated.expression();
                                if access.kind() != SyntaxKind::PropertyAccessExpression {
                                    go_node_as_panic(access, "PropertyAccessExpression");
                                }
                                return access.expression();
                            }
                            if kind == TransformationKind::Pipe
                                && arguments.is_some()
                                && arguments.nodes().len() == 1
                            {
                                return arguments.nodes().get(0);
                            }
                        }
                        return updated;
                    };
                    let step = &flow.transformations[index as usize];
                    if is_piping_flow_argument(step.kind) {
                        if index < end {
                            return Node::NIL;
                        }
                        return piping_flow_operator(v.factory(), replacement);
                    }
                    let input = flow.transformation_input_node(index);
                    if input.is_nil() {
                        return node;
                    }
                    let subject = v.visit_node(input);
                    if index < end {
                        return subject;
                    }
                    let f = v.factory();
                    let mut arguments = clone_node_list_nodes(f, replacement.arguments);
                    match step.kind {
                        TransformationKind::DataFirst => arguments.insert(0, subject),
                        TransformationKind::DataLast => arguments.push(subject),
                        _ => {
                            return f.new_call_expression(
                                piping_flow_operator(f, replacement),
                                Node::NIL,
                                NodeList::NIL,
                                f.new_node_list(&[subject]),
                                NodeFlags::NONE,
                            );
                        }
                    }
                    f.new_call_expression(
                        replacement.callee,
                        Node::NIL,
                        replacement.type_arguments,
                        f.new_node_list(&arguments),
                        NodeFlags::NONE,
                    )
                },
                Some(f),
                NodeVisitorHooks::default(),
                (),
            );
            let visited = visitor.visit_node(target);
            f.deep_clone_node(visited)
        };
        set_parent_in_children(result);
        self.replace_node(source_file, target, result, None);
        true
    }
}

// Go: rewriter/piping_flow.go:377 isPipingFlowArgument
fn is_piping_flow_argument(kind: TransformationKind) -> bool {
    matches!(
        kind,
        TransformationKind::Pipe
            | TransformationKind::Pipeable
            | TransformationKind::EffectFn
            | TransformationKind::EffectFnUntraced
    )
}

// Go: rewriter/piping_flow.go:385 nodeWithin
fn node_within(node: Node, ancestor: Node) -> bool {
    let mut node = node;
    while node.is_some() {
        if node == ancestor {
            return true;
        }
        node = node.parent();
    }
    false
}
