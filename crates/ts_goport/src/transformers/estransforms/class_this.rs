//! Port of Go `transformers/estransforms/classthis.go`.

use crate::prelude::*;
use crate::printer::EmitContext;

// Go: transformers/estransforms/classthis.go:10 isClassThisAssignmentBlock
/// Gets whether a node is a `static {}` block containing only a single assignment of the static `this` to the `_classThis`
/// (or similar) variable stored in the `classthis` property of the block's `EmitNode`.
pub(crate) fn is_class_this_assignment_block(emit_context: &EmitContext, node: Node) -> bool {
    if is_class_static_block_declaration(node) {
        let body = node.body();
        let statements = body.statements();
        if statements.len() == 1 {
            let statement = statements.get(0);
            if is_expression_statement(statement) {
                let expression = statement.expression();
                if is_assignment_expression(expression, true /*excludeCompoundAssignment*/) {
                    return is_identifier(expression.left())
                        && emit_context.class_this(node) == expression.left()
                        && expression.right().kind() == SyntaxKind::ThisKeyword;
                }
            }
        }
    }
    false
}
