//! Port of Effect-TS/tsgo `internal/fixables/catch_all_to_map_error.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::replace_effect_method_callee;
use crate::effect::rules::catch_all_to_map_error::analyze_catch_all_to_map_error;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/catch_all_to_map_error.go:12 CatchAllToMapErrorFix
pub static CATCH_ALL_TO_MAP_ERROR_FIX: Fixable = Fixable {
    name: "catchAllToMapError",
    description: "Replace Effect.catch + Effect.fail with Effect.mapError",
    // Go: tsdiag.Effect_mapError_expresses_the_same_error_type_transformation_more_directly_than_Effect_0_followed_by_Effect_fail_effect_catchAllToMapError
    error_codes: &[377010],
    fix_ids: &["catchAllToMapError_fix"],
    run: run_catch_all_to_map_error_fix,
};

// Go: fixables/catch_all_to_map_error.go:20 runCatchAllToMapErrorFix
fn run_catch_all_to_map_error_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_catch_all_to_map_error(ctx.tp, sf);
    for m in matches {
        let diag_range = m.location;
        if !diag_range.intersects(ctx.span) && !ctx.span.contained_by(diag_range) {
            continue;
        }
        if let Some(action) =
            ctx.new_fix_action("Replace with Effect.mapError".to_string(), |tracker| {
                // Edit 1: Replace "catch" with "mapError" in the callee
                replace_effect_method_callee(tracker, sf, m.callee, m.callee_name_node, "mapError");

                // Edit 2: Unwrap "Effect.fail(arg)" to "arg" by deleting prefix and suffix
                tracker.delete_range(
                    sf,
                    TextRange::new(m.fail_call_expression.pos(), m.fail_argument.pos()),
                );
                tracker.delete_range(
                    sf,
                    TextRange::new(m.fail_argument.end(), m.fail_call_expression.end()),
                );
            })
        {
            return vec![action];
        }
    }

    Vec::new()
}
