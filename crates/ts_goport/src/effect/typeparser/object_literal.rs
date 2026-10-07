//! Port of Effect-TS/tsgo `internal/typeparser/object_literal.go`.

use crate::effect::typeparser::*;
use crate::prelude::*;

/// ObjectLiteralPropertyInitializer returns the initializer of an explicitly
/// assigned identifier or string-literal property in an object literal.
// Go: typeparser/object_literal.go ObjectLiteralPropertyInitializer
pub fn object_literal_property_initializer(node: Node, name: &str) -> Node {
    let node = skip_parentheses(node);
    if node.is_nil() || node.kind() != SyntaxKind::ObjectLiteralExpression {
        return Node::NIL;
    }
    let object = node;
    if object.property_list().is_nil() {
        return Node::NIL;
    }
    for property_node in object.properties().iter() {
        if property_node.is_nil() || property_node.kind() != SyntaxKind::PropertyAssignment {
            continue;
        }
        let property = property_node;
        if property.name().is_nil() {
            continue;
        }
        let property_name = property.name();
        match property_name.kind() {
            SyntaxKind::Identifier => {
                if property_name.text() == name {
                    return property.initializer();
                }
            }
            SyntaxKind::StringLiteral => {
                if property_name.text() == name {
                    return property.initializer();
                }
            }
            _ => {}
        }
    }
    Node::NIL
}
