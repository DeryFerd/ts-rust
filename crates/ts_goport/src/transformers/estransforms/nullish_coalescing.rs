//! Port of Go `transformers/estransforms/nullishcoalescing.go`.

use super::contract::{TransformOptions, TransformerBox};
use super::utilities::{TxVisitors, create_not_null_condition, impl_es_transformer};
use crate::prelude::*;
use crate::printer::EmitContext;
use crate::transformers::utilities::is_simple_copiable_expression;

// Go: transformers/estransforms/nullishcoalescing.go:8 nullishCoalescingTransformer
pub struct NullishCoalescingTransformer {
    emit_context: Rc<EmitContext>,
}

impl_es_transformer!(NullishCoalescingTransformer);

impl NullishCoalescingTransformer {
    // Go: transformers/estransforms/nullishcoalescing.go:12 nullishCoalescingTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        if !node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_NULLISH_COALESCING)
        {
            return node;
        }
        match node.kind() {
            SyntaxKind::BinaryExpression => self.visit_binary_expression(node),
            _ => self.visit_each_child(node),
        }
    }

    // Go: transformers/estransforms/nullishcoalescing.go:24 nullishCoalescingTransformer.visitBinaryExpression
    fn visit_binary_expression(&mut self, node: Node) -> Node {
        match node.operator_token().kind() {
            SyntaxKind::QuestionQuestionToken => {
                let ec = self.ec();
                let f = ec.factory();
                let mut left = self.visit_node(node.left());
                let mut right = left;
                if !is_simple_copiable_expression(left) {
                    right = f.new_temp_variable();
                    ec.add_variable_declaration(right);
                    left = f.new_assignment_expression(right, left);
                }
                let when_false = self.visit_node(node.right());
                f.new_conditional_expression(
                    create_not_null_condition(&ec, left, right, false),
                    f.new_token(SyntaxKind::QuestionToken),
                    right,
                    f.new_token(SyntaxKind::ColonToken),
                    when_false,
                )
            }
            _ => self.visit_each_child(node),
        }
    }
}

// Go: transformers/estransforms/nullishcoalescing.go:46 newNullishCoalescingTransformer
pub fn new_nullish_coalescing_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    Some(Box::new(NullishCoalescingTransformer {
        emit_context: opts.context.clone(),
    }))
}
