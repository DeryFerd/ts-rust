//! Port of Effect-TS/tsgo `internal/fixables/return_effect_in_gen.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::return_effect_in_gen::analyze_return_effect_in_gen;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/return_effect_in_gen.go:15 ReturnEffectInGenFix
/// ReturnEffectInGenFix adds "yield*" before the return expression in an Effect generator
/// when the return value is an Effect-able type (which would cause nested Effect<Effect<...>>).
pub static RETURN_EFFECT_IN_GEN_FIX: Fixable = Fixable {
    name: "returnEffectInGen",
    description: "Add yield* statement",
    // Go: tsdiag.This_generator_returns_an_Effect_able_value_directly_which_produces_a_nested_Effect_Effect_If_the_intended_result_is_the_inner_Effect_value_return_yield_Asterisk_represents_that_form_effect_returnEffectInGen
    error_codes: &[377014],
    fix_ids: &["returnEffectInGen_fix"],
    run: run_return_effect_in_gen_fix,
};

// Go: fixables/return_effect_in_gen.go:23 runReturnEffectInGenFix
fn run_return_effect_in_gen_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_return_effect_in_gen(ctx.tp, sf);

    let Some(m) = matches.iter().find(|m| {
        let diag_range = m.location;
        diag_range.intersects(ctx.span) || ctx.span.contained_by(diag_range)
    }) else {
        return Vec::new();
    };
    let return_expr = m.return_node.expression();

    if let Some(action) = ctx.new_fix_action("Add yield* statement".to_string(), |tracker| {
        let f = tracker.node_factory();
        let cloned_expr = f.deep_clone_node(return_expr);
        let new_yield_expr =
            f.new_yield_expression(f.new_token(SyntaxKind::AsteriskToken), cloned_expr);
        set_parent_in_children(new_yield_expr);
        tracker.replace_node(sf, return_expr, new_yield_expr, None);
    }) {
        return vec![action];
    }
    Vec::new()
}
