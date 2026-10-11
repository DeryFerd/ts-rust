//! Port of Effect-TS/tsgo `internal/fixables/unnecessary_fail_yieldable_error.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::unnecessary_fail_yieldable_error::analyze_unnecessary_fail_yieldable_error;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/unnecessary_fail_yieldable_error.go:12 UnnecessaryFailYieldableErrorFix
pub static UNNECESSARY_FAIL_YIELDABLE_ERROR_FIX: Fixable = Fixable {
    name: "unnecessaryFailYieldableError",
    description: "Replace yield* Effect.fail with yield*",
    // Go: tsdiag.This_yield_Asterisk_Effect_fail_passes_a_yieldable_error_value_yield_Asterisk_represents_that_value_directly_without_wrapping_it_in_Effect_fail_effect_unnecessaryFailYieldableError
    error_codes: &[377019],
    fix_ids: &["unnecessaryFailYieldableError_fix"],
    run: run_unnecessary_fail_yieldable_error_fix,
};

// Go: fixables/unnecessary_fail_yieldable_error.go:20 runUnnecessaryFailYieldableErrorFix
fn run_unnecessary_fail_yieldable_error_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_unnecessary_fail_yieldable_error(ctx.tp, sf);
    for m in matches {
        let diag_range = m.location;
        if !diag_range.intersects(ctx.span) && !ctx.span.contained_by(diag_range) {
            continue;
        }

        // Unwrap "Effect.fail(arg)" to just "arg" by deleting the prefix and suffix around the argument.
        // This keeps "yield*" in place, changing "yield* Effect.fail(error)" to "yield* error".
        if let Some(action) = ctx.new_fix_action(
            "Replace yield* Effect.fail with yield*".to_string(),
            |tracker| {
                tracker.delete_range(sf, TextRange::new(m.call_node.pos(), m.fail_argument.pos()));
                tracker.delete_range(sf, TextRange::new(m.fail_argument.end(), m.call_node.end()));
            },
        ) {
            return vec![action];
        }
        return Vec::new();
    }

    Vec::new()
}
