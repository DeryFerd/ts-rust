//! Port of Effect-TS/tsgo `internal/fixables/effect_succeed_with_void.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::effect_module_method;
use crate::effect::rules::effect_succeed_with_void::analyze_effect_succeed_with_void;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/effect_succeed_with_void.go:12 EffectSucceedWithVoidFix
pub static EFFECT_SUCCEED_WITH_VOID_FIX: Fixable = Fixable {
    name: "effectSucceedWithVoid",
    description: "Replace with Effect.void",
    // Go: tsdiag.Effect_void_represents_the_same_outcome_as_Effect_succeed_undefined_or_Effect_succeed_void_0_effect_effectSucceedWithVoid
    error_codes: &[377016],
    fix_ids: &["effectSucceedWithVoid_fix"],
    run: run_effect_succeed_with_void_fix,
};

// Go: fixables/effect_succeed_with_void.go:20 runEffectSucceedWithVoidFix
fn run_effect_succeed_with_void_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_effect_succeed_with_void(ctx.tp, sf);
    for m in matches {
        let diag_range = m.location;
        if !diag_range.intersects(ctx.span) && !ctx.span.contained_by(diag_range) {
            continue;
        }
        if let Some(action) =
            ctx.new_fix_action("Replace with Effect.void".to_string(), |tracker| {
                let replacement_node =
                    effect_module_method(tracker, sf, m.effect_module_node, "void");
                set_parent_in_children(replacement_node);
                tracker.replace_node(sf, m.call_node, replacement_node, None);
            })
        {
            return vec![action];
        }
    }

    Vec::new()
}
