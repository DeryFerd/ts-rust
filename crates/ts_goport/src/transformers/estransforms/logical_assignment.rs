//! Port of Go `transformers/estransforms/logicalassignment.go`.

use super::contract::{TransformOptions, TransformerBox};
use super::utilities::{TxVisitors, impl_es_transformer};
use crate::prelude::*;
use crate::printer::EmitContext;
use crate::transformers::utilities::is_simple_copiable_expression;

// Go: transformers/estransforms/logicalassignment.go:8 logicalAssignmentTransformer
pub struct LogicalAssignmentTransformer {
    emit_context: Rc<EmitContext>,
}

impl_es_transformer!(LogicalAssignmentTransformer);

impl LogicalAssignmentTransformer {
    // Go: transformers/estransforms/logicalassignment.go:12 logicalAssignmentTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        if !node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_LOGICAL_ASSIGNMENTS)
        {
            return node;
        }
        match node.kind() {
            SyntaxKind::BinaryExpression => self.visit_binary_expression(node),
            _ => self.visit_each_child(node),
        }
    }

    // Go: transformers/estransforms/logicalassignment.go:24 logicalAssignmentTransformer.visitBinaryExpression
    fn visit_binary_expression(&mut self, node: Node) -> Node {
        let non_assignment_operator = match node.operator_token().kind() {
            SyntaxKind::BarBarEqualsToken => SyntaxKind::BarBarToken,
            SyntaxKind::AmpersandAmpersandEqualsToken => SyntaxKind::AmpersandAmpersandToken,
            SyntaxKind::QuestionQuestionEqualsToken => SyntaxKind::QuestionQuestionToken,
            _ => return self.visit_each_child(node),
        };

        let mut left = skip_parentheses(self.visit_node(node.left()));
        let mut assignment_target = left;
        let right = skip_parentheses(self.visit_node(node.right()));

        let ec = self.ec();
        let f = ec.factory();
        if is_access_expression(left) {
            let property_access_target_simple_copiable =
                is_simple_copiable_expression(left.expression());
            let mut property_access_target = left.expression();
            let mut property_access_target_assignment = left.expression();
            if !property_access_target_simple_copiable {
                property_access_target = f.new_temp_variable();
                ec.add_variable_declaration(property_access_target);
                property_access_target_assignment =
                    f.new_assignment_expression(property_access_target, left.expression());
            }

            if is_property_access_expression(left) {
                assignment_target = f.new_property_access_expression(
                    property_access_target,
                    Node::NIL,
                    left.name(),
                    NodeFlags::NONE,
                );
                left = f.new_property_access_expression(
                    property_access_target_assignment,
                    Node::NIL,
                    left.name(),
                    NodeFlags::NONE,
                );
            } else {
                let element_access_argument_simple_copiable =
                    is_simple_copiable_expression(left.argument_expression());
                let mut element_access_argument = left.argument_expression();
                let mut argument_expr = element_access_argument;
                if !element_access_argument_simple_copiable {
                    element_access_argument = f.new_temp_variable();
                    ec.add_variable_declaration(element_access_argument);
                    argument_expr = f.new_assignment_expression(
                        element_access_argument,
                        left.argument_expression(),
                    );
                }

                assignment_target = f.new_element_access_expression(
                    property_access_target,
                    Node::NIL,
                    element_access_argument,
                    NodeFlags::NONE,
                );
                left = f.new_element_access_expression(
                    property_access_target_assignment,
                    Node::NIL,
                    argument_expr,
                    NodeFlags::NONE,
                );
            }
        }

        f.new_binary_expression(
            ModifierList::NIL,
            left,
            Node::NIL,
            f.new_token(non_assignment_operator),
            f.new_parenthesized_expression(f.new_assignment_expression(assignment_target, right)),
        )
    }
}

// Go: transformers/estransforms/logicalassignment.go:110 newLogicalAssignmentTransformer
pub fn new_logical_assignment_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    Some(Box::new(LogicalAssignmentTransformer {
        emit_context: opts.context.clone(),
    }))
}
