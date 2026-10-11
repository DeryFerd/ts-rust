//! Port of Effect-TS/tsgo `internal/refactors/toggle_lazy_const.go`.

use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::with_kind;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: refactors/toggle_lazy_const.go:12 ToggleLazyConst
pub static TOGGLE_LAZY_CONST: Refactor = Refactor {
    name: "toggleLazyConst",
    description: "Toggle lazy const",
    kind: "rewrite.effect.toggleLazyConst",
    run: run_toggle_lazy_const,
};

// Go: refactors/toggle_lazy_const.go:19 runToggleLazyConst
fn run_toggle_lazy_const(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let token = astnav::get_token_at_position(ctx.source_file, ctx.span.pos());
    if token.is_nil() {
        return Vec::new();
    }

    // Walk ancestor chain looking for a VariableDeclaration
    let mut matched_node = Node::NIL;
    let mut node = token;
    while node.is_some() {
        let vd = node;
        node = node.parent();
        if vd.kind() != SyntaxKind::VariableDeclaration {
            continue;
        }

        // Must have an initializer
        if vd.initializer().is_nil() {
            continue;
        }

        // Cursor must be on the name
        let name = vd.name();
        if name.is_nil() {
            continue;
        }
        let name_pos = astnav::get_start_of_node(name, ctx.source_file, false);
        let name_end = name.end();
        if ctx.span.pos() < name_pos || ctx.span.pos() > name_end {
            continue;
        }

        // Exclude arrow functions with block bodies
        let initializer = vd.initializer();
        if initializer.kind() == SyntaxKind::ArrowFunction
            && initializer.body().is_some()
            && initializer.body().kind() == SyntaxKind::Block
        {
            return Vec::new();
        }

        matched_node = vd;
        break;
    }

    if matched_node.is_nil() {
        return Vec::new();
    }

    let initializer = matched_node.initializer();
    let sf = ctx.source_file;

    // Check if this is a zero-param arrow with expression body → unwrap
    if initializer.kind() == SyntaxKind::ArrowFunction {
        let af = initializer;
        if af.parameters().is_empty() && af.body().is_some() {
            // Unwrap: remove the `() => ` prefix and any trailing content
            let body = af.body();
            let action = ctx.new_refactor_action("Toggle lazy const", |tracker| {
                // Delete from body.end to initializer.end (trailing content after body)
                if body.end() != initializer.end() {
                    tracker.delete_range(sf, TextRange::new(body.end(), initializer.end()));
                }
                // Delete from initializer.pos to body.pos (the `() => ` prefix)
                tracker.delete_range(sf, TextRange::new(initializer.pos(), body.pos()));
            });
            return with_kind(action, "refactor.rewrite.effect.toggleLazyConst");
        }
    }

    // Wrap: insert `() => ` before the initializer
    let pos = ctx.byte_pos_to_lsp_position(initializer.pos());
    let action = ctx.new_refactor_action("Toggle lazy const", |tracker| {
        tracker.insert_text(sf, pos, " () =>");
    });
    with_kind(action, "refactor.rewrite.effect.toggleLazyConst")
}
