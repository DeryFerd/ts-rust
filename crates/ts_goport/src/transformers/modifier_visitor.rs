//! Port of Go `transformers/modifiervisitor.go`.

use crate::prelude::*;

use crate::ast::visitor::NodeVisitor;

// Go: transformers/modifiervisitor.go:13 modifierVisitor.visit
// PORT: Go `modifierVisitor` only holds `AllowedModifiers`; it is the
// visitor context here.
fn visit(node: Node, allowed_modifiers: ModifierFlags) -> Node {
    let flags = modifier_to_flag(node.kind());
    if flags != ModifierFlags::NONE && !flags.intersects(allowed_modifiers) {
        return Node::NIL;
    }
    node
}

// Go: transformers/modifiervisitor.go:21 ExtractModifiers
pub fn extract_modifiers(
    emit_context: &EmitContext,
    modifiers: ModifierList,
    allowed: ModifierFlags,
) -> ModifierList {
    if modifiers.is_nil() {
        return ModifierList::NIL;
    }
    let mut visitor = emit_context.new_node_visitor(
        |node, v: &mut NodeVisitor<'_, ModifierFlags>| visit(node, v.ctx),
        allowed,
    );
    visitor.visit_modifiers(modifiers)
}
