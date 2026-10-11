//! Port of Effect-TS/tsgo `internal/fixables/catch_to_or_else_succeed.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::replace_effect_method_callee;
use crate::effect::rules::catch_to_or_else_succeed::analyze_catch_to_or_else_succeed;
use crate::ls::CodeAction;

// Go: fixables/catch_to_or_else_succeed.go:11 CatchToOrElseSucceedFix
pub static CATCH_TO_OR_ELSE_SUCCEED_FIX: Fixable = Fixable {
    name: "catchToOrElseSucceed",
    description: "Replace Effect.catch + Effect.succeed with Effect.orElseSucceed",
    // Go: tsdiag.Effect_orElseSucceed_expresses_the_same_recovery_more_directly_than_Effect_0_followed_by_Effect_succeed_effect_catchToOrElseSucceed
    error_codes: &[377095],
    fix_ids: &["catchToOrElseSucceed_fix"],
    run: run_catch_to_or_else_succeed_fix,
};

// Go: fixables/catch_to_or_else_succeed.go:19 runCatchToOrElseSucceedFix
fn run_catch_to_or_else_succeed_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_catch_to_or_else_succeed(ctx.tp, sf);
    for m in matches {
        let diag_range = m.location;
        if !diag_range.intersects(ctx.span) && !ctx.span.contained_by(diag_range) {
            continue;
        }
        if let Some(action) =
            ctx.new_fix_action("Replace with Effect.orElseSucceed".to_string(), |tracker| {
                replace_effect_method_callee(
                    tracker,
                    sf,
                    m.callee,
                    m.callee_name_node,
                    "orElseSucceed",
                );

                tracker.replace_node(sf, m.succeed_call_expression, m.succeed_argument, None);
            })
        {
            return vec![action];
        }
    }

    Vec::new()
}
