//! Port of Effect-TS/tsgo `internal/typeparser/identity_forwarder.go`.

use crate::effect::typeparser::*;
use crate::prelude::*;

impl TypeParser<'_> {
    // Go: typeparser/identity_forwarder.go TypeParser.UnwrapIdentityForwarder
    /// UnwrapIdentityForwarder returns the callee of a one-argument function that
    /// forwards its argument unchanged, any explicit type arguments on the
    /// forwarded call, and the forwarder's parameter declaration so that callers
    /// can apply stricter checks (e.g. reject annotated parameters). All other
    /// expressions are returned as-is with no type arguments and no parameter.
    ///
    /// For example, both fn and value => fn(value) normalize to fn.
    ///
    /// Returns `(target, type_arguments, parameter)`.
    pub fn unwrap_identity_forwarder(&mut self, node: Node) -> (Node, NodeList, Node) {
        if node.is_nil() {
            return (Node::NIL, NodeList::NIL, Node::NIL);
        }

        let node = skip_parentheses(node);
        let Some(lazy) = parse_lazy_expression(node, LazyExpressionFlags::NONE) else {
            return (node, NodeList::NIL, Node::NIL);
        };
        if lazy.params.len() != 1 || lazy.expression.is_nil() {
            return (node, NodeList::NIL, Node::NIL);
        }

        let parameter_node = lazy.params[0];
        if parameter_node.is_nil() || parameter_node.kind() != SyntaxKind::Parameter {
            return (node, NodeList::NIL, Node::NIL);
        }
        let parameter_declaration = parameter_node;
        if parameter_declaration.name().is_nil()
            || parameter_declaration.name().kind() != SyntaxKind::Identifier
            || parameter_declaration.dot_dot_dot_token().is_some()
            || parameter_declaration.initializer().is_some()
        {
            return (node, NodeList::NIL, Node::NIL);
        }

        let expression = skip_parentheses(lazy.expression);
        if expression.is_nil() || expression.kind() != SyntaxKind::CallExpression {
            return (node, NodeList::NIL, Node::NIL);
        }
        let call = expression;
        if call.expression().is_nil()
            || call.argument_list().is_nil()
            || call.arguments().len() != 1
        {
            return (node, NodeList::NIL, Node::NIL);
        }

        let argument = skip_parentheses(call.arguments().get(0));
        if argument.is_nil() || argument.kind() != SyntaxKind::Identifier {
            return (node, NodeList::NIL, Node::NIL);
        }

        let parameter_symbol = self.get_symbol_at_location(parameter_declaration.name());
        let argument_symbol = self.get_symbol_at_location(argument);
        if parameter_symbol.is_nil()
            || argument_symbol.is_nil()
            || self
                .checker
                .get_symbol_if_same_reference(parameter_symbol, argument_symbol)
                .is_nil()
        {
            return (node, NodeList::NIL, Node::NIL);
        }

        (
            skip_parentheses(call.expression()),
            call.type_argument_list(),
            parameter_node,
        )
    }
}
