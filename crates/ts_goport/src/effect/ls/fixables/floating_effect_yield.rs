//! Port of Effect-TS/tsgo `internal/fixables/floating_effect_yield.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::floating_effect::analyze_floating_effect;
use crate::effect::typeparser::EffectContextFlags;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/floating_effect_yield.go:14 FloatingEffectYieldFix
/// FloatingEffectYieldFix yields a floating Effect when it occurs in an Effect generator.
pub static FLOATING_EFFECT_YIELD_FIX: Fixable = Fixable {
    name: "floatingEffectYield",
    description: "Add yield* statement",
    // Go: tsdiag.This_Effect_value_is_neither_yielded_nor_used_in_an_assignment_effect_floatingEffect,
    // tsdiag.This_Effect_able_0_value_is_neither_yielded_nor_assigned_to_a_variable_effect_floatingEffect
    error_codes: &[377001, 377058],
    fix_ids: &["floatingEffectYield_fix"],
    run: run_floating_effect_yield_fix,
};

// Go: fixables/floating_effect_yield.go:25 runFloatingEffectYieldFix
// Only the first match in the request is tried, as in Go.
fn run_floating_effect_yield_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;
    for m in analyze_floating_effect(ctx.tp, sf) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        if !ctx
            .tp
            .get_effect_context_flags(m.expression)
            .intersects(EffectContextFlags::CAN_YIELD_EFFECT)
        {
            return Vec::new();
        }
        let expr_type = ctx.tp.get_type_at_location(m.expression);
        if ctx.tp.effect_yieldable_type(expr_type).is_none() {
            return Vec::new();
        }

        if let Some(action) = ctx.new_fix_action("Add yield* statement".to_string(), |tracker| {
            let f = tracker.node_factory();
            let cloned_expr = f.deep_clone_node(m.expression);
            let yield_expr =
                f.new_yield_expression(f.new_token(SyntaxKind::AsteriskToken), cloned_expr);
            set_parent_in_children(yield_expr);
            tracker.replace_node(sf, m.expression, yield_expr, None);
        }) {
            return vec![action];
        }
        return Vec::new();
    }
    Vec::new()
}
