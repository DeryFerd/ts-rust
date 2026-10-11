//! Port of Effect-TS/tsgo `internal/refactors/remove_unnecessary_effect_gen.go`.

use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::with_kind;
use crate::effect::rules::unnecessary_effect_gen::analyze_unnecessary_effect_gen;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: refactors/remove_unnecessary_effect_gen.go:13 RemoveUnnecessaryEffectGen
pub static REMOVE_UNNECESSARY_EFFECT_GEN: Refactor = Refactor {
    name: "removeUnnecessaryEffectGen",
    description: "Remove unnecessary Effect.gen",
    kind: "rewrite.effect.removeUnnecessaryEffectGen",
    run: run_remove_unnecessary_effect_gen,
};

// Go: refactors/remove_unnecessary_effect_gen.go:20 runRemoveUnnecessaryEffectGen
fn run_remove_unnecessary_effect_gen(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let matches = analyze_unnecessary_effect_gen(ctx.tp, ctx.source_file);
    if matches.is_empty() {
        return Vec::new();
    }

    let token = astnav::get_token_at_position(ctx.source_file, ctx.span.pos());
    if token.is_nil() {
        return Vec::new();
    }

    // Walk ancestor chain to find a call expression that matches one of the analyzed nodes
    let mut node = token;
    while node.is_some() {
        let current = node;
        node = node.parent();
        if current.kind() != SyntaxKind::CallExpression {
            continue;
        }

        let Some(m) = matches.iter().find(|m| m.call_node == current) else {
            continue;
        };

        // Found a matching unnecessary Effect.gen call at cursor
        let sf = ctx.source_file;

        if m.explicit_return || m.success_is_void {
            // Simple unwrap: delete the prefix and suffix around the yielded expression
            let action = ctx.new_refactor_action("Remove unnecessary Effect.gen", |tracker| {
                tracker.delete_range(
                    sf,
                    TextRange::new(m.call_node.pos(), m.yielded_expression.pos()),
                );
                tracker.delete_range(
                    sf,
                    TextRange::new(m.yielded_expression.end(), m.call_node.end()),
                );
            });
            return with_kind(action, "refactor.rewrite.effect.removeUnnecessaryEffectGen");
        }

        // No return + non-void success: wrap with Effect.asVoid(expr)
        let action = ctx.new_refactor_action("Remove unnecessary Effect.gen", |tracker| {
            let f = tracker.node_factory();
            let effect_module_id = if m.effect_module_node.is_some()
                && m.effect_module_node.kind() == SyntaxKind::Identifier
            {
                f.deep_clone_node(m.effect_module_node)
            } else {
                f.new_identifier("Effect")
            };

            let as_void_access = f.new_property_access_expression(
                effect_module_id,
                Node::NIL,
                f.new_identifier("asVoid"),
                NodeFlags::NONE,
            );
            let cloned_expr = f.deep_clone_node(m.yielded_expression);
            let call_expr = f.new_call_expression(
                as_void_access,
                Node::NIL,
                NodeList::NIL,
                f.new_node_list(&[cloned_expr]),
                NodeFlags::NONE,
            );
            set_parent_in_children(call_expr);
            tracker.replace_node(sf, m.call_node, call_expr, None);
        });
        return with_kind(action, "refactor.rewrite.effect.removeUnnecessaryEffectGen");
    }

    Vec::new()
}
