//! Port of Effect-TS/tsgo `internal/fixables/unnecessary_effect_gen.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::effect_module_method;
use crate::effect::rules::unnecessary_effect_gen::analyze_unnecessary_effect_gen;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/unnecessary_effect_gen.go:13 UnnecessaryEffectGenFix
pub static UNNECESSARY_EFFECT_GEN_FIX: Fixable = Fixable {
    name: "unnecessaryEffectGen",
    description: "Remove the Effect.gen, and keep the body",
    // Go: tsdiag.This_Effect_gen_contains_a_single_return_statement_effect_unnecessaryEffectGen
    error_codes: &[377017],
    fix_ids: &["unnecessaryEffectGen_fix"],
    run: run_unnecessary_effect_gen_fix,
};

// Go: fixables/unnecessary_effect_gen.go:21 runUnnecessaryEffectGenFix
fn run_unnecessary_effect_gen_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_unnecessary_effect_gen(ctx.tp, sf);
    for m in matches {
        let diag_range = m.location;
        if !diag_range.intersects(ctx.span) && !ctx.span.contained_by(diag_range) {
            continue;
        }

        if m.explicit_return || m.success_is_void {
            // Simple unwrap: delete the prefix and suffix around the yielded expression
            if let Some(action) = ctx.new_fix_action(
                "Remove the Effect.gen, and keep the body".to_string(),
                |tracker| {
                    tracker.delete_range(
                        sf,
                        TextRange::new(m.call_node.pos(), m.yielded_expression.pos()),
                    );
                    tracker.delete_range(
                        sf,
                        TextRange::new(m.yielded_expression.end(), m.call_node.end()),
                    );
                },
            ) {
                return vec![action];
            }
            continue;
        }

        // No return + non-void success: wrap with Effect.asVoid(...)
        if let Some(action) = ctx.new_fix_action(
            "Remove the Effect.gen, and keep the body".to_string(),
            |tracker| {
                let as_void_access =
                    effect_module_method(tracker, sf, m.effect_module_node, "asVoid");

                // Clone the yielded expression
                let f = tracker.node_factory();
                let cloned_expr = f.deep_clone_node(m.yielded_expression);

                // Build Effect.asVoid(expr) call expression
                let call_expr = f.new_call_expression(
                    as_void_access,
                    Node::NIL,
                    NodeList::NIL,
                    f.new_node_list(&[cloned_expr]),
                    NodeFlags::NONE,
                );

                set_parent_in_children(call_expr);
                tracker.replace_node(sf, m.call_node, call_expr, None);
            },
        ) {
            return vec![action];
        }
    }

    Vec::new()
}
