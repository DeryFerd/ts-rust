//! Port of Go `transformers/estransforms/optionalchain.go`.

use super::contract::{TransformOptions, TransformerBox};
use super::utilities::{TxVisitors, create_not_null_condition, impl_es_transformer};
use crate::prelude::*;
use crate::printer::{EmitContext, EmitFlags};
use crate::transformers::utilities::is_simple_copiable_expression;

// Go: transformers/estransforms/optionalchain.go:10 optionalChainTransformer
pub struct OptionalChainTransformer {
    emit_context: Rc<EmitContext>,
}

impl_es_transformer!(OptionalChainTransformer);

impl OptionalChainTransformer {
    // Go: transformers/estransforms/optionalchain.go:14 optionalChainTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        if !node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_OPTIONAL_CHAINING)
        {
            return node;
        }
        match node.kind() {
            SyntaxKind::CallExpression => self.visit_call_expression(node, false),
            SyntaxKind::PropertyAccessExpression | SyntaxKind::ElementAccessExpression => {
                if node.flags().intersects(NodeFlags::OPTIONAL_CHAIN) {
                    return self.visit_optional_expression(node, false, false);
                }
                self.visit_each_child(node)
            }
            SyntaxKind::DeleteExpression => self.visit_delete_expression(node),
            _ => self.visit_each_child(node),
        }
    }

    // Go: transformers/estransforms/optionalchain.go:34 optionalChainTransformer.visitCallExpression
    fn visit_call_expression(&mut self, node: Node, capture_this_arg: bool) -> Node {
        if node.flags().intersects(NodeFlags::OPTIONAL_CHAIN) {
            // If `node` is an optional chain, then it is the outermost chain of an optional expression.
            return self.visit_optional_expression(node, capture_this_arg, false);
        }
        if is_parenthesized_expression(node.expression()) {
            let unwrapped = skip_parentheses(node.expression());
            if unwrapped.flags().intersects(NodeFlags::OPTIONAL_CHAIN) {
                // capture thisArg for calls of parenthesized optional chains like `(foo?.bar)()`
                let expression =
                    self.visit_parenthesized_expression(node.expression(), true, false);
                let args = self.visit_nodes(node.argument_list());
                let ec = self.ec();
                let f = ec.factory();
                if is_synthetic_reference_expression(expression) {
                    let res = f.new_function_call_call(
                        expression.expression(),
                        expression.this_arg(),
                        &args.nodes().to_vec(),
                    );
                    set_node_loc(res, node.loc());
                    ec.set_original(res, node);
                    return res;
                }
                return f.update_call_expression(
                    node,
                    expression,
                    Node::NIL,     /*questionDotToken*/
                    NodeList::NIL, /*typeArguments*/
                    args,
                    node.flags(),
                );
            }
        }
        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/optionalchain.go:57 optionalChainTransformer.visitParenthesizedExpression
    fn visit_parenthesized_expression(
        &mut self,
        node: Node,
        capture_this_arg: bool,
        is_delete: bool,
    ) -> Node {
        let expr =
            self.visit_non_optional_expression(node.expression(), capture_this_arg, is_delete);
        let ec = self.ec();
        let f = ec.factory();
        if is_synthetic_reference_expression(expr) {
            // `(a.b)` -> { expression `((_a = a).b)`, thisArg: `_a` }
            // `(a[b])` -> { expression `((_a = a)[b])`, thisArg: `_a` }
            let res = f.new_synthetic_reference_expression(
                f.update_parenthesized_expression(node, expr.expression()),
                expr.this_arg(),
            );
            ec.set_original(res, node);
            return res;
        }
        f.update_parenthesized_expression(node, expr)
    }

    // Go: transformers/estransforms/optionalchain.go:71 optionalChainTransformer.visitPropertyOrElementAccessExpression
    fn visit_property_or_element_access_expression(
        &mut self,
        node: Node,
        capture_this_arg: bool,
        is_delete: bool,
    ) -> Node {
        if node.flags().intersects(NodeFlags::OPTIONAL_CHAIN) {
            // If `node` is an optional chain, then it is the outermost chain of an optional expression.
            return self.visit_optional_expression(node, capture_this_arg, is_delete);
        }
        let mut expression = self.visit_node(node.expression());
        go_assert!(expression.is_nil() || !is_synthetic_reference_expression(expression));

        let ec = self.ec();
        let f = ec.factory();
        let mut this_arg = Node::NIL;
        if capture_this_arg {
            if !is_simple_copiable_expression(expression) {
                this_arg = f.new_temp_variable();
                ec.add_variable_declaration(this_arg);
                expression = f.new_assignment_expression(this_arg, expression);
            } else {
                this_arg = expression;
            }
        }

        if node.kind() == SyntaxKind::PropertyAccessExpression {
            let name = self.visit_node(node.name());
            expression = f.update_property_access_expression(
                node,
                expression,
                Node::NIL, /*questionDotToken*/
                name,
                node.flags(),
            );
        } else {
            let argument = self.visit_node(node.argument_expression());
            expression = f.update_element_access_expression(
                node,
                expression,
                Node::NIL,
                argument,
                node.flags(),
            );
        }

        if this_arg.is_some() {
            let res = f.new_synthetic_reference_expression(expression, this_arg);
            ec.set_original(res, node);
            return res;
        }
        expression
    }

    // Go: transformers/estransforms/optionalchain.go:106 optionalChainTransformer.visitDeleteExpression
    fn visit_delete_expression(&mut self, node: Node) -> Node {
        let unwrapped = skip_parentheses(node.expression());
        if unwrapped.flags().intersects(NodeFlags::OPTIONAL_CHAIN) {
            return self.visit_non_optional_expression(node.expression(), false, true);
        }
        self.visit_each_child(node)
    }

    // Go: transformers/estransforms/optionalchain.go:114 optionalChainTransformer.visitNonOptionalExpression
    fn visit_non_optional_expression(
        &mut self,
        node: Node,
        capture_this_arg: bool,
        is_delete: bool,
    ) -> Node {
        match node.kind() {
            SyntaxKind::ParenthesizedExpression => {
                self.visit_parenthesized_expression(node, capture_this_arg, is_delete)
            }
            SyntaxKind::ElementAccessExpression | SyntaxKind::PropertyAccessExpression => {
                self.visit_property_or_element_access_expression(node, capture_this_arg, is_delete)
            }
            SyntaxKind::CallExpression => self.visit_call_expression(node, capture_this_arg),
            _ => self.visit_node(node),
        }
    }

    // Go: transformers/estransforms/optionalchain.go:153 optionalChainTransformer.visitOptionalExpression
    fn visit_optional_expression(
        &mut self,
        node: Node,
        capture_this_arg: bool,
        is_delete: bool,
    ) -> Node {
        let (expression, chain) = flatten_chain(node);
        let left = self.visit_non_optional_expression(
            skip_partially_emitted_expressions(expression),
            is_call_chain(chain[0]),
            false,
        );
        let ec = self.ec();
        let f = ec.factory();
        let mut left_this_arg = Node::NIL;
        let mut captured_left = left;
        if is_synthetic_reference_expression(left) {
            left_this_arg = left.this_arg();
            captured_left = left.expression();
        }
        let mut left_expression = f.restore_outer_expressions(
            expression,
            captured_left,
            OuterExpressionKinds::OEK_PARTIALLY_EMITTED_EXPRESSIONS,
        );
        if !is_simple_copiable_expression(captured_left) {
            captured_left = f.new_temp_variable();
            ec.add_variable_declaration(captured_left);
            left_expression = f.new_assignment_expression(captured_left, left_expression);
        }
        let mut right_expression = captured_left;
        let mut this_arg = Node::NIL;

        for (i, &segment) in chain.iter().enumerate() {
            match segment.kind() {
                SyntaxKind::ElementAccessExpression | SyntaxKind::PropertyAccessExpression => {
                    if i == chain.len() - 1 && capture_this_arg {
                        if !is_simple_copiable_expression(right_expression) {
                            this_arg = f.new_temp_variable();
                            ec.add_variable_declaration(this_arg);
                            right_expression =
                                f.new_assignment_expression(this_arg, right_expression);
                        } else {
                            this_arg = right_expression;
                        }
                    }
                    if segment.kind() == SyntaxKind::ElementAccessExpression {
                        let argument = self.visit_node(segment.argument_expression());
                        right_expression = f.new_element_access_expression(
                            right_expression,
                            Node::NIL,
                            argument,
                            NodeFlags::NONE,
                        );
                    } else {
                        let name = self.visit_node(segment.name());
                        right_expression = f.new_property_access_expression(
                            right_expression,
                            Node::NIL,
                            name,
                            NodeFlags::NONE,
                        );
                    }
                }
                SyntaxKind::CallExpression => {
                    if i == 0 && left_this_arg.is_some() {
                        if !ec.has_auto_generate_info(left_this_arg) {
                            left_this_arg = f.clone_node(left_this_arg);
                            ec.add_emit_flags(left_this_arg, EmitFlags::NO_COMMENTS);
                        }
                        let mut call_this_arg = left_this_arg;
                        if left_this_arg.kind() == SyntaxKind::SuperKeyword {
                            call_this_arg = f.new_this_expression();
                        }
                        let arguments = self.visit_nodes(segment.argument_list());
                        right_expression = f.new_function_call_call(
                            right_expression,
                            call_this_arg,
                            &arguments.nodes().to_vec(),
                        );
                    } else {
                        let arguments = self.visit_nodes(segment.argument_list());
                        right_expression = f.new_call_expression(
                            right_expression,
                            Node::NIL,
                            NodeList::NIL,
                            arguments,
                            NodeFlags::NONE,
                        );
                    }
                }
                _ => {}
            }
            ec.set_original(right_expression, segment);
        }

        let mut target = if is_delete {
            f.new_conditional_expression(
                create_not_null_condition(&ec, left_expression, captured_left, true),
                f.new_token(SyntaxKind::QuestionToken),
                f.new_true_expression(),
                f.new_token(SyntaxKind::ColonToken),
                f.new_delete_expression(right_expression),
            )
        } else {
            f.new_conditional_expression(
                create_not_null_condition(&ec, left_expression, captured_left, true),
                f.new_token(SyntaxKind::QuestionToken),
                f.new_void_zero_expression(),
                f.new_token(SyntaxKind::ColonToken),
                right_expression,
            )
        };
        set_node_loc(target, node.loc());
        if this_arg.is_some() {
            target = f.new_synthetic_reference_expression(target, this_arg);
        }
        ec.set_original(target, node);
        target
    }
}

// Go: transformers/estransforms/optionalchain.go:132 isNonNullChain
fn is_non_null_chain(node: Node) -> bool {
    is_non_null_expression(node) && node.flags().intersects(NodeFlags::OPTIONAL_CHAIN)
}

// Go: transformers/estransforms/optionalchain.go:136 flattenChain
/// Returns Go `flattenResult{expression, chain}`.
fn flatten_chain(mut chain: Node) -> (Node, Vec<Node>) {
    go_assert!(!is_non_null_chain(chain));
    let mut links: Vec<Node> = vec![chain];
    while !is_tagged_template_expression(chain) && chain.question_dot_token().is_nil() {
        chain = skip_partially_emitted_expressions(chain.expression());
        go_assert!(!is_non_null_chain(chain));
        links.insert(0, chain);
    }
    (chain.expression(), links)
}

// Go: transformers/estransforms/optionalchain.go:147 isCallChain
fn is_call_chain(node: Node) -> bool {
    is_call_expression(node) && node.flags().intersects(NodeFlags::OPTIONAL_CHAIN)
}

// Go: transformers/estransforms/optionalchain.go:237 newOptionalChainTransformer
pub fn new_optional_chain_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    Some(Box::new(OptionalChainTransformer {
        emit_context: opts.context.clone(),
    }))
}
