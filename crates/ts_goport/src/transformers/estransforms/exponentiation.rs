//! Port of Go `transformers/estransforms/exponentiation.go`.

use super::contract::{TransformOptions, TransformerBox};
use super::utilities::{TxVisitors, impl_es_transformer};
use crate::prelude::*;
use crate::printer::EmitContext;

// Go: transformers/estransforms/exponentiation.go:8 exponentiationTransformer
pub struct ExponentiationTransformer {
    emit_context: Rc<EmitContext>,
}

impl_es_transformer!(ExponentiationTransformer);

impl ExponentiationTransformer {
    // Go: transformers/estransforms/exponentiation.go:12 exponentiationTransformer.visit
    fn visit(&mut self, node: Node) -> Node {
        if !node
            .subtree_facts()
            .intersects(SubtreeFacts::SUBTREE_CONTAINS_EXPONENTIATION_OPERATOR)
        {
            return node;
        }
        match node.kind() {
            SyntaxKind::BinaryExpression => self.visit_binary_expression(node),
            _ => self.visit_each_child(node),
        }
    }

    // Go: transformers/estransforms/exponentiation.go:24 exponentiationTransformer.visitBinaryExpression
    fn visit_binary_expression(&mut self, node: Node) -> Node {
        match node.operator_token().kind() {
            SyntaxKind::AsteriskAsteriskEqualsToken => {
                self.visit_exponentiation_assignment_expression(node)
            }
            SyntaxKind::AsteriskAsteriskToken => self.visit_exponentiation_expression(node),
            _ => self.visit_each_child(node),
        }
    }

    // Go: transformers/estransforms/exponentiation.go:34 exponentiationTransformer.visitExponentiationAssignmentExpression
    fn visit_exponentiation_assignment_expression(&mut self, node: Node) -> Node {
        let left = self.visit_node(node.left());
        let right = self.visit_node(node.right());
        let ec = self.ec();
        let f = ec.factory();
        let target;
        let value;
        if is_element_access_expression(left) {
            // Transforms `a[x] **= b` into `(_a = a)[_x = x] = Math.pow(_a[_x], b)`
            let expression_temp = f.new_temp_variable();
            ec.add_variable_declaration(expression_temp);
            let argument_expression_temp = f.new_temp_variable();
            ec.add_variable_declaration(argument_expression_temp);

            let obj_expr = f.new_assignment_expression(expression_temp, left.expression());
            set_node_loc(obj_expr, left.expression().loc());
            let access_expr =
                f.new_assignment_expression(argument_expression_temp, left.argument_expression());
            set_node_loc(access_expr, left.argument_expression().loc());

            target =
                f.new_element_access_expression(obj_expr, Node::NIL, access_expr, NodeFlags::NONE);

            value = f.new_element_access_expression(
                expression_temp,
                Node::NIL,
                argument_expression_temp,
                NodeFlags::NONE,
            );
            set_node_loc(value, left.loc());
        } else if is_property_access_expression(left) {
            // Transforms `a.x **= b` into `(_a = a).x = Math.pow(_a.x, b)`
            let expression_temp = f.new_temp_variable();
            ec.add_variable_declaration(expression_temp);
            let assignment = f.new_assignment_expression(expression_temp, left.expression());
            set_node_loc(assignment, left.expression().loc());
            target = f.new_property_access_expression(
                assignment,
                Node::NIL,
                left.name(),
                NodeFlags::NONE,
            );
            set_node_loc(target, left.loc());

            value = f.new_property_access_expression(
                expression_temp,
                Node::NIL,
                left.name(),
                NodeFlags::NONE,
            );
            set_node_loc(value, left.loc());
        } else {
            // Transforms `a **= b` into `a = Math.pow(a, b)`
            target = left;
            value = left;
        }

        let rhs = f.new_global_method_call("Math", "pow", &[value, right]);
        set_node_loc(rhs, node.loc());
        let result = f.new_assignment_expression(target, rhs);
        set_node_loc(result, node.loc());
        result
    }

    // Go: transformers/estransforms/exponentiation.go:79 exponentiationTransformer.visitExponentiationExpression
    fn visit_exponentiation_expression(&mut self, node: Node) -> Node {
        let left = self.visit_node(node.left());
        let right = self.visit_node(node.right());
        let ec = self.ec();
        let result = ec
            .factory()
            .new_global_method_call("Math", "pow", &[left, right]);
        set_node_loc(result, node.loc());
        result
    }
}

// Go: transformers/estransforms/exponentiation.go:87 newExponentiationTransformer
pub fn new_exponentiation_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    Some(Box::new(ExponentiationTransformer {
        emit_context: opts.context.clone(),
    }))
}
