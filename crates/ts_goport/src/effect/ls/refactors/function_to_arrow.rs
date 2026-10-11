//! Port of Effect-TS/tsgo `internal/refactors/function_to_arrow.go`.

use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::{clone_node_list, with_kind};
use crate::effect::ls::rewriter::Tracker;
use crate::effect::typeparser::{
    get_function_like_body, get_function_like_parameters, get_function_like_type_parameters,
};
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: refactors/function_to_arrow.go:12 FunctionToArrow
pub static FUNCTION_TO_ARROW: Refactor = Refactor {
    name: "functionToArrow",
    description: "Convert to arrow",
    kind: "rewrite.effect.functionToArrow",
    run: run_function_to_arrow,
};

// Go: refactors/function_to_arrow.go:19 runFunctionToArrow
fn run_function_to_arrow(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let token = astnav::get_token_at_position(ctx.source_file, ctx.span.pos());
    if token.is_nil() {
        return Vec::new();
    }

    // Walk ancestor chain looking for a FunctionDeclaration or MethodDeclaration
    let mut matched_node = Node::NIL;
    let mut node = token;
    while node.is_some() {
        let current = node;
        node = node.parent();
        if current.kind() != SyntaxKind::FunctionDeclaration
            && current.kind() != SyntaxKind::MethodDeclaration
        {
            continue;
        }

        // Must have a body
        let body = get_function_like_body(current);
        if body.is_nil() {
            continue;
        }

        // Exclude async functions (those are handled by asyncAwaitToFn/asyncAwaitToGen)
        if get_combined_modifier_flags(current).intersects(ModifierFlags::ASYNC) {
            continue;
        }

        // Must have a name and cursor must be on it
        let name = current.name();
        if name.is_nil() {
            continue;
        }

        let name_pos = astnav::get_start_of_node(name, ctx.source_file, false);
        let name_end = name.end();
        if ctx.span.pos() < name_pos || ctx.span.pos() > name_end {
            continue;
        }

        matched_node = current;
        break;
    }

    if matched_node.is_nil() {
        return Vec::new();
    }

    let sf = ctx.source_file;
    let action = ctx.new_refactor_action("Convert to arrow", |tracker| {
        let new_node = build_function_to_arrow_replacement(tracker, matched_node);
        if new_node.is_nil() {
            return;
        }
        set_parent_in_children(new_node);
        tracker.replace_node(sf, matched_node, new_node, None);
    });
    with_kind(action, "refactor.rewrite.effect.functionToArrow")
}

// Go: refactors/function_to_arrow.go:89 buildFunctionToArrowReplacement
// buildFunctionToArrowReplacement builds the replacement node for converting a
// FunctionDeclaration or MethodDeclaration to an arrow function.
fn build_function_to_arrow_replacement(tracker: &Tracker, node: Node) -> Node {
    let body = get_function_like_body(node);
    if body.is_nil() {
        return Node::NIL;
    }
    let f = tracker.node_factory();

    // Determine concise vs block body:
    // If body has exactly one ReturnStatement with an expression, use concise body
    let mut new_body = Node::NIL;
    if body.kind() == SyntaxKind::Block {
        let statements = body.statements();
        if statements.len() == 1 {
            let stmt = statements.get(0);
            if stmt.kind() == SyntaxKind::ReturnStatement && stmt.expression().is_some() {
                // Concise body: just the expression
                new_body = f.deep_clone_node(stmt.expression());
            }
        }
        if new_body.is_nil() {
            // Block body
            new_body = f.deep_clone_node(body);
        }
    } else {
        new_body = f.deep_clone_node(body);
    }

    // Build arrow modifiers: strip Export and Default from the arrow itself
    let mut arrow_mods = ModifierList::NIL;
    let src_mods = get_node_modifiers(node);
    if src_mods.is_some() {
        let mod_nodes: Vec<Node> = src_mods
            .nodes()
            .iter()
            .filter(|m| {
                m.kind() != SyntaxKind::ExportKeyword && m.kind() != SyntaxKind::DefaultKeyword
            })
            .map(|m| f.new_modifier(m.kind()))
            .collect();
        if !mod_nodes.is_empty() {
            arrow_mods = f.new_modifier_list(&mod_nodes);
        }
    }

    // Build the arrow function
    let type_params = clone_node_list(tracker, get_function_like_type_parameters(node));
    let params = clone_node_list(tracker, get_function_like_parameters(node));

    let arrow_fn = f.new_arrow_function(
        arrow_mods,
        type_params,
        params,
        Node::NIL, // returnType
        Node::NIL, // fullSignature
        f.new_token(SyntaxKind::EqualsGreaterThanToken),
        new_body,
    );

    // Wrap in appropriate declaration
    match node.kind() {
        SyntaxKind::FunctionDeclaration => {
            wrap_arrow_in_variable_statement(tracker, node, arrow_fn)
        }
        SyntaxKind::MethodDeclaration => {
            wrap_arrow_in_property_declaration(tracker, node, arrow_fn)
        }
        _ => arrow_fn,
    }
}

/// The modifiers of `mods` as new modifier tokens, or nil when there are
/// none.
// PORT: Go repeats this loop in both wrap functions below.
fn clone_modifiers(tracker: &Tracker, mods: ModifierList) -> ModifierList {
    if mods.is_nil() {
        return ModifierList::NIL;
    }
    let f = tracker.node_factory();
    let mod_nodes: Vec<Node> = mods
        .nodes()
        .iter()
        .map(|m| f.new_modifier(m.kind()))
        .collect();
    if mod_nodes.is_empty() {
        return ModifierList::NIL;
    }
    f.new_modifier_list(&mod_nodes)
}

// Go: refactors/function_to_arrow.go:161 wrapArrowInVariableStatement
// wrapArrowInVariableStatement wraps an arrow function in a const variable statement,
// preserving export/default modifiers on the variable statement.
fn wrap_arrow_in_variable_statement(tracker: &Tracker, node: Node, arrow_fn: Node) -> Node {
    if node.name().is_nil() {
        return arrow_fn;
    }

    // Collect modifiers for the variable statement (keep all original modifiers)
    let mods = clone_modifiers(tracker, node.modifiers());

    let f = tracker.node_factory();
    let var_decl = f.new_variable_declaration(
        f.deep_clone_node(node.name()),
        Node::NIL, // exclamationToken
        Node::NIL, // type
        arrow_fn,
    );
    let var_decl_list =
        f.new_variable_declaration_list(f.new_node_list(&[var_decl]), NodeFlags::CONST);
    f.new_variable_statement(mods, var_decl_list)
}

// Go: refactors/function_to_arrow.go:194 wrapArrowInPropertyDeclaration
// wrapArrowInPropertyDeclaration wraps an arrow function in a property declaration,
// preserving modifiers from the method.
fn wrap_arrow_in_property_declaration(tracker: &Tracker, node: Node, arrow_fn: Node) -> Node {
    let mods = clone_modifiers(tracker, node.modifiers());

    let f = tracker.node_factory();
    f.new_property_declaration(
        mods,
        f.deep_clone_node(node.name()),
        Node::NIL, // postfixToken
        Node::NIL, // type
        arrow_fn,
    )
}

// Go: refactors/function_to_arrow.go:218 getNodeModifiers
// getNodeModifiers returns the modifier list from a function-like node.
fn get_node_modifiers(node: Node) -> ModifierList {
    match node.kind() {
        SyntaxKind::FunctionDeclaration | SyntaxKind::MethodDeclaration => node.modifiers(),
        _ => ModifierList::NIL,
    }
}
