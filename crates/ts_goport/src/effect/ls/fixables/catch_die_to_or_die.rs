//! Port of Effect-TS/tsgo `internal/fixables/catch_die_to_or_die.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::effect_module_method;
use crate::effect::ls::rewriter::PipingFlowTransformationReplacement;
use crate::effect::rules::catch_die_to_or_die::analyze_catch_die_to_or_die;
use crate::ls::CodeAction;

// Go: fixables/catch_die_to_or_die.go:11 CatchDieToOrDieFix
pub static CATCH_DIE_TO_OR_DIE_FIX: Fixable = Fixable {
    name: "catchDieToOrDie",
    description: "Replace the catch-all Effect.die handler with Effect.orDie",
    // Go: tsdiag.Effect_orDie_expresses_escalating_every_typed_failure_into_a_defect_more_directly_than_Effect_0_with_an_identity_forwarding_Effect_die_handler_effect_catchDieToOrDie
    error_codes: &[377115],
    fix_ids: &["catchDieToOrDie_fix"],
    run: run_catch_die_to_or_die_fix,
};

// Go: fixables/catch_die_to_or_die.go:21 runCatchDieToOrDieFix
// PORT: Go skips a match with a nil `Transformation`; the Rust match always
// has one.
fn run_catch_die_to_or_die_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;
    for m in analyze_catch_die_to_or_die(ctx.tp, sf) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        if m.has_type_arguments {
            continue;
        }

        if let Some(action) =
            ctx.new_fix_action("Replace with Effect.orDie".to_string(), |tracker| {
                let or_die = effect_module_method(tracker, sf, m.effect_module, "orDie");
                tracker.replace_piping_flow_transformation(
                    sf,
                    &m.transformation,
                    PipingFlowTransformationReplacement::callee(or_die),
                );
            })
        {
            return vec![action];
        }
    }
    Vec::new()
}
