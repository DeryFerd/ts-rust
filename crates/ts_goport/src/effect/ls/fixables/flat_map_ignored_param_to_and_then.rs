//! Port of Effect-TS/tsgo `internal/fixables/flat_map_ignored_param_to_and_then.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::replace_effect_method_callee;
use crate::effect::rules::flat_map_ignored_param_to_and_then::analyze_flat_map_ignored_param_to_and_then;
use crate::ls::CodeAction;

// Go: fixables/flat_map_ignored_param_to_and_then.go:11 FlatMapIgnoredParamToAndThenFix
pub static FLAT_MAP_IGNORED_PARAM_TO_AND_THEN_FIX: Fixable = Fixable {
    name: "flatMapIgnoredParamToAndThen",
    description: "Replace Effect.flatMap with Effect.andThen",
    // Go: tsdiag.Effect_andThen_expresses_this_sequencing_more_directly_than_Effect_flatMap_with_a_zero_parameter_callback_effect_flatMapIgnoredParamToAndThen
    error_codes: &[377132],
    fix_ids: &["flatMapIgnoredParamToAndThen_fix"],
    run: run_flat_map_ignored_param_to_and_then_fix,
};

// Go: fixables/flat_map_ignored_param_to_and_then.go:21 runFlatMapIgnoredParamToAndThenFix
fn run_flat_map_ignored_param_to_and_then_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    for m in analyze_flat_map_ignored_param_to_and_then(ctx.tp, ctx.source_file) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }

        let sf = ctx.source_file;
        if let Some(action) =
            ctx.new_fix_action("Replace with Effect.andThen".to_string(), |tracker| {
                replace_effect_method_callee(tracker, sf, m.callee, m.callee_name_node, "andThen");
                tracker.replace_node(sf, m.callback, m.effect_value, None);
            })
        {
            return vec![action];
        }
    }

    Vec::new()
}
