//! Port of Effect-TS/tsgo `internal/fixables/match_effect_to_map_both.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::replace_effect_method_callee;
use crate::effect::rules::match_effect_to_map_both::analyze_match_effect_to_map_both;
use crate::ls::CodeAction;

// Go: fixables/match_effect_to_map_both.go:11 MatchEffectToMapBothFix
pub static MATCH_EFFECT_TO_MAP_BOTH_FIX: Fixable = Fixable {
    name: "matchEffectToMapBoth",
    description: "Replace Effect.matchEffect with Effect.mapBoth and unwrap Effect.fail and Effect.succeed handlers",
    // Go: tsdiag.Effect_mapBoth_expresses_these_failure_and_success_transformations_more_directly_than_Effect_matchEffect_effect_matchEffectToMapBoth
    error_codes: &[377126],
    fix_ids: &["matchEffectToMapBoth_fix"],
    run: run_match_effect_to_map_both_fix,
};

// Go: fixables/match_effect_to_map_both.go:17 runMatchEffectToMapBothFix
fn run_match_effect_to_map_both_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    for m in analyze_match_effect_to_map_both(ctx.tp, ctx.source_file) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        if m.callee_node.is_nil() {
            continue;
        }
        if let Some(action) =
            ctx.new_fix_action("Replace with Effect.mapBoth".to_string(), |tracker| {
                replace_effect_method_callee(
                    tracker,
                    m.source_file,
                    m.callee_node,
                    m.callee_name_node,
                    "mapBoth",
                );
                for i in 0..m.handler_results.len() {
                    tracker.replace_node(
                        m.source_file,
                        m.handler_results[i],
                        m.constructor_args[i],
                        None,
                    );
                }
            })
        {
            return vec![action];
        }
    }
    Vec::new()
}
