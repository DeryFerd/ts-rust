//! Port of Effect-TS/tsgo `internal/typeparser/lazy_expression.go`.

use crate::effect::typeparser::*;
use crate::flags_macros::go_flags;
use crate::prelude::*;

/// ParsedLazyExpression represents a parsed arrow function or function expression
/// with its inner expression extracted.
// Go: typeparser/lazy_expression.go ParsedLazyExpression
#[derive(Clone)]
pub struct ParsedLazyExpression {
    /// The original ArrowFunction or FunctionExpression node
    pub node: Node,
    /// Parameter declarations (empty when parsed with thunk=true)
    pub params: Vec<Node>,
    /// The function body as written (Expression or Block)
    pub body: Node,
    /// The inner expression (return value)
    pub expression: Node,
}

// LazyExpressionFlags controls which function shapes ParseLazyExpression accepts.
// PORT: Go assigns `1 << iota` from the second const, so the values are
// 0, 2, 4 and 8, kept here.
// Go: typeparser/lazy_expression.go LazyExpressionFlags
go_flags!(LazyExpressionFlags, u8 {
    NONE = 0;
    /// LazyExpressionThunk requires a function with no parameters.
    THUNK = 1 << 1;
    /// LazyExpressionAllowAsync additionally accepts async functions.
    ALLOW_ASYNC = 1 << 2;
    /// LazyExpressionAllowGenerator additionally accepts generator functions.
    ALLOW_GENERATOR = 1 << 3;
});

/// ParseLazyExpression parses an arrow function or function expression, extracting its inner expression.
/// By default, only synchronous, non-generator functions are accepted.
/// Returns nil if the node is not a valid lazy expression.
// Go: typeparser/lazy_expression.go ParseLazyExpression
pub fn parse_lazy_expression(
    node: Node,
    flags: LazyExpressionFlags,
) -> Option<Rc<ParsedLazyExpression>> {
    let node = skip_parentheses(node);
    if node.is_nil() {
        return None;
    }
    if !flags.intersects(LazyExpressionFlags::ALLOW_ASYNC)
        && get_combined_modifier_flags(node).intersects(ModifierFlags::ASYNC)
    {
        return None;
    }

    let type_params: NodeList;
    let params: NodeList;
    let body: Node;

    match node.kind() {
        SyntaxKind::ArrowFunction => {
            let fn_ = node;
            type_params = fn_.type_parameter_list();
            params = fn_.parameter_list();
            body = fn_.body();
        }
        SyntaxKind::FunctionExpression => {
            let fn_ = node;
            if fn_.asterisk_token().is_some()
                && !flags.intersects(LazyExpressionFlags::ALLOW_GENERATOR)
            {
                return None;
            }
            type_params = fn_.type_parameter_list();
            params = fn_.parameter_list();
            body = fn_.body();
        }
        _ => return None,
    }

    // Reject functions with type parameters
    if !type_params.is_nil() && !type_params.nodes().is_empty() {
        return None;
    }

    // Thunks must not declare parameters.
    if flags.intersects(LazyExpressionFlags::THUNK)
        && !params.is_nil()
        && !params.nodes().is_empty()
    {
        return None;
    }

    if body.is_nil() {
        return None;
    }

    // Build params list
    let mut param_nodes: Vec<Node> = Vec::new();
    if !params.is_nil() {
        param_nodes = params.nodes().to_vec();
    }

    // Extract the inner expression
    let expr: Node;
    if body.kind() == SyntaxKind::Block {
        let block = body;
        if block.statement_list().is_nil() || block.statements().len() != 1 {
            return None;
        }
        let stmt = block.statements().get(0);
        if stmt.kind() != SyntaxKind::ReturnStatement {
            return None;
        }
        let return_expr = stmt.expression();
        if return_expr.is_nil() {
            return None;
        }
        expr = return_expr;
    } else {
        // Expression body (arrow function only)
        expr = body;
    }

    Some(Rc::new(ParsedLazyExpression {
        node,
        params: param_nodes,
        body,
        expression: expr,
    }))
}
