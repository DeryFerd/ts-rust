//! Port of Effect-TS/tsgo `internal/fixables/missing_star_in_yield_effect_gen.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::missing_star_in_yield_effect_gen::analyze_missing_star_in_yield_effect_gen;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/missing_star_in_yield_effect_gen.go:12 MissingStarInYieldEffectGenFix
pub static MISSING_STAR_IN_YIELD_EFFECT_GEN_FIX: Fixable = Fixable {
    name: "missingStarInYieldEffectGen",
    description: "Replace yield with yield* inside Effect generator scopes",
    // Go: tsdiag.This_uses_yield_for_an_Effect_value_yield_Asterisk_is_the_Effect_aware_form_in_this_context_effect_missingStarInYieldEffectGen
    error_codes: &[377008],
    fix_ids: &["missingStarInYieldEffectGen_fix"],
    run: run_missing_star_in_yield_effect_gen_fix,
};

// Go: fixables/missing_star_in_yield_effect_gen.go:20 runMissingStarInYieldEffectGenFix
fn run_missing_star_in_yield_effect_gen_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_missing_star_in_yield_effect_gen(ctx.tp, sf);

    let mut yield_node = Node::NIL;
    for m in &matches {
        let diag_range = m.location;
        if diag_range.intersects(ctx.span) || ctx.span.contained_by(diag_range) {
            yield_node = m.yield_node;
            break;
        }
    }
    if yield_node.is_nil() {
        return Vec::new();
    }

    if let Some(action) = ctx.new_fix_action("Replace yield with yield*".to_string(), |tracker| {
        let f = tracker.node_factory();
        let cloned_expr = f.deep_clone_node(yield_node.expression());
        let new_yield_expr =
            f.new_yield_expression(f.new_token(SyntaxKind::AsteriskToken), cloned_expr);
        set_parent_in_children(new_yield_expr);
        tracker.replace_node(sf, yield_node, new_yield_expr, None);
    }) {
        return vec![action];
    }
    Vec::new()
}
