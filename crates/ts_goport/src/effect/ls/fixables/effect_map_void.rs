//! Port of Effect-TS/tsgo `internal/fixables/effect_map_void.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::effect_module_method;
use crate::effect::ls::rewriter::PipingFlowTransformationReplacement;
use crate::effect::rules::effect_map_void::analyze_effect_map_void;
use crate::ls::CodeAction;

// Go: fixables/effect_map_void.go:11 EffectMapVoidFix
pub static EFFECT_MAP_VOID_FIX: Fixable = Fixable {
    name: "effectMapVoid",
    description: "Replace with Effect.asVoid",
    // Go: tsdiag.This_expression_discards_the_success_value_through_mapping_Effect_asVoid_represents_that_form_directly_effect_effectMapVoid
    error_codes: &[377018],
    fix_ids: &["effectMapVoid_fix"],
    run: run_effect_map_void_fix,
};

// Go: fixables/effect_map_void.go:19 runEffectMapVoidFix
// PORT: Go skips a match with a nil `Transformation`; the Rust match always
// has one.
fn run_effect_map_void_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_effect_map_void(ctx.tp, sf);
    for m in matches {
        let diag_range = m.location;
        if !diag_range.intersects(ctx.span) && !ctx.span.contained_by(diag_range) {
            continue;
        }

        if let Some(action) =
            ctx.new_fix_action("Replace with Effect.asVoid".to_string(), |tracker| {
                // Build Effect.asVoid, preserving the original module reference (and any alias).
                let as_void = effect_module_method(tracker, sf, m.effect_module_node, "asVoid");
                tracker.replace_piping_flow_transformation(
                    sf,
                    &m.transformation,
                    PipingFlowTransformationReplacement::callee(as_void),
                );
            })
        {
            return vec![action];
        }
    }

    Vec::new()
}
