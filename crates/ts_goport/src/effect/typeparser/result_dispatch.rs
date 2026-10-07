//! Port of Effect-TS/tsgo `internal/typeparser/result_dispatch.go`.

use crate::effect::typeparser::*;
use crate::prelude::*;

impl ResultDispatch {
    /// Go `CommonTagSubject`: the common subject of a tag-based dispatch. It
    /// returns nil when any branch is not tag-based or when the tag subjects
    /// do not refer to the same expression by symbol.
    /// PORT: the Go `dispatch == nil || tp == nil || tp.checker == nil` guards
    /// cannot fail here.
    pub fn common_tag_subject(&self, tp: &mut TypeParser<'_>) -> Node {
        if self.branches.is_empty() {
            return Node::NIL;
        }

        let common = self.branches[0].condition.tag_subject;
        if common.is_nil() || self.branches[0].condition.tag_value.is_nil() {
            return Node::NIL;
        }
        for branch in &self.branches[1..] {
            let condition = branch.condition;
            if condition.tag_subject.is_nil()
                || condition.tag_value.is_nil()
                || !tp.same_result_dispatch_reference(common, condition.tag_subject)
            {
                return Node::NIL;
            }
        }
        common
    }
}

impl TypeParser<'_> {
    pub fn same_result_dispatch_reference(&mut self, left: Node, right: Node) -> bool {
        let left = unwrap_result_dispatch_expression(left);
        let right = unwrap_result_dispatch_expression(right);
        if left.is_nil() || right.is_nil() || left.kind() != right.kind() {
            return false;
        }
        if left == right {
            return true;
        }

        match left.kind() {
            SyntaxKind::Identifier => {
                let left_symbol = self.get_symbol_at_location(left);
                let right_symbol = self.get_symbol_at_location(right);
                same_symbol_reference(self.checker, left_symbol, right_symbol)
            }
            SyntaxKind::PropertyAccessExpression => {
                let left_access_expression = left.expression();
                let right_access_expression = right.expression();
                if left_access_expression.is_nil() || right_access_expression.is_nil() {
                    return false;
                }
                let left_symbol = self.get_symbol_at_location(left);
                let right_symbol = self.get_symbol_at_location(right);
                same_symbol_reference(self.checker, left_symbol, right_symbol)
                    && self.same_result_dispatch_reference(
                        left_access_expression,
                        right_access_expression,
                    )
            }
            SyntaxKind::ThisKeyword | SyntaxKind::SuperKeyword => true,
            _ => false,
        }
    }
}
