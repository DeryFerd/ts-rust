//! Port of Effect-TS/tsgo `internal/fixables/unsafe_effect_type_assertion.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::unsafe_effect_type_assertion::analyze_unsafe_effect_type_assertion;
use crate::ls::CodeAction;

// Go: fixables/unsafe_effect_type_assertion.go:11 UnsafeEffectTypeAssertionFix
pub static UNSAFE_EFFECT_TYPE_ASSERTION_FIX: Fixable = Fixable {
    name: "unsafeEffectTypeAssertion",
    description: "Remove the unsafe assertion",
    // Go: tsdiag.This_type_assertion_unsafely_narrows_the_error_or_requirements_channels_effect_unsafeEffectTypeAssertion
    error_codes: &[377075],
    fix_ids: &["unsafeEffectTypeAssertion_fix"],
    run: run_unsafe_effect_type_assertion_fix,
};

// Go: fixables/unsafe_effect_type_assertion.go:19 runUnsafeEffectTypeAssertionFix
fn run_unsafe_effect_type_assertion_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;
    let matches = analyze_unsafe_effect_type_assertion(ctx.tp, sf);
    for m in matches {
        let diag_range = m.location;
        if !diag_range.intersects(ctx.span) && !ctx.span.contained_by(diag_range) {
            continue;
        }

        if let Some(action) =
            ctx.new_fix_action("Remove the unsafe assertion".to_string(), |tracker| {
                // Go passes the original expression node, not a clone.
                tracker.replace_node(sf, m.assertion_node, m.expression_node, None);
            })
        {
            return vec![action];
        }
        return Vec::new();
    }

    Vec::new()
}
