//! Port of Effect-TS/tsgo `internal/fixables/flat_map_to_map.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::replace_effect_method_callee;
use crate::effect::rules::flat_map_to_map::analyze_flat_map_to_map;
use crate::ls::CodeAction;

// Go: fixables/flat_map_to_map.go:11 FlatMapToMapFix
pub static FLAT_MAP_TO_MAP_FIX: Fixable = Fixable {
    name: "flatMapToMap",
    description: "Replace Effect.flatMap + Effect.succeed with Effect.map",
    // Go: tsdiag.Effect_map_expresses_this_success_value_transformation_more_directly_than_Effect_flatMap_followed_by_Effect_succeed_effect_flatMapToMap
    error_codes: &[377100],
    fix_ids: &["flatMapToMap_fix"],
    run: run_flat_map_to_map_fix,
};

// Go: fixables/flat_map_to_map.go:21 runFlatMapToMapFix
fn run_flat_map_to_map_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_flat_map_to_map(ctx.tp, sf);
    for m in matches {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        if let Some(action) = ctx.new_fix_action("Replace with Effect.map".to_string(), |tracker| {
            replace_effect_method_callee(tracker, sf, m.callee, m.callee_name_node, "map");
            tracker.replace_node(sf, m.succeed_call_expression, m.succeed_argument, None);
        }) {
            return vec![action];
        }
    }

    Vec::new()
}
