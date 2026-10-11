//! Port of Effect-TS/tsgo `internal/fixables/map_some_to_as_some.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::effect_module_method;
use crate::effect::ls::rewriter::PipingFlowTransformationReplacement;
use crate::effect::rules::map_some_to_as_some::analyze_map_some_to_as_some;
use crate::ls::CodeAction;

// Go: fixables/map_some_to_as_some.go:11 MapSomeToAsSomeFix
pub static MAP_SOME_TO_AS_SOME_FIX: Fixable = Fixable {
    name: "mapSomeToAsSome",
    description: "Replace Effect.map(Option.some) with Effect.asSome",
    // Go: tsdiag.Effect_asSome_expresses_wrapping_the_success_value_in_Option_some_directly_effect_mapSomeToAsSome
    error_codes: &[377114],
    fix_ids: &["mapSomeToAsSome_fix"],
    run: run_map_some_to_as_some_fix,
};

// Go: fixables/map_some_to_as_some.go:21 runMapSomeToAsSomeFix
// PORT: Go skips a match with a nil `Transformation`; the Rust match always
// has one.
fn run_map_some_to_as_some_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    for m in analyze_map_some_to_as_some(ctx.tp, ctx.source_file) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }

        let sf = ctx.source_file;
        if let Some(action) =
            ctx.new_fix_action("Replace with Effect.asSome".to_string(), |tracker| {
                let as_some = effect_module_method(tracker, sf, m.effect_module_node, "asSome");
                tracker.replace_piping_flow_transformation(
                    sf,
                    &m.transformation,
                    PipingFlowTransformationReplacement::callee(as_some),
                );
            })
        {
            return vec![action];
        }
    }

    Vec::new()
}
