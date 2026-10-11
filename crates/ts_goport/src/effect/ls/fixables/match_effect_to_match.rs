//! Port of Effect-TS/tsgo `internal/fixables/match_effect_to_match.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::replace_effect_method_callee;
use crate::effect::rules::match_effect_to_match::analyze_match_effect_to_match;
use crate::ls::CodeAction;

// Go: fixables/match_effect_to_match.go:11 MatchEffectToMatchFix
pub static MATCH_EFFECT_TO_MATCH_FIX: Fixable = Fixable {
    name: "matchEffectToMatch",
    description: "Replace Effect.matchEffect with Effect.match and unwrap Effect.succeed handlers",
    // Go: tsdiag.Effect_0_expresses_this_non_effectful_fold_more_directly_than_Effect_1_with_Effect_succeed_handlers_effect_matchEffectToMatch
    error_codes: &[377125],
    fix_ids: &["matchEffectToMatch_fix"],
    run: run_match_effect_to_match_fix,
};

// Go: fixables/match_effect_to_match.go:17 runMatchEffectToMatchFix
fn run_match_effect_to_match_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    for m in analyze_match_effect_to_match(ctx.tp, ctx.source_file) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        if m.callee_node.is_nil() {
            continue;
        }
        if let Some(action) = ctx.new_fix_action(
            format!("Replace with Effect.{}", m.replacement_name),
            |tracker| {
                replace_effect_method_callee(
                    tracker,
                    m.source_file,
                    m.callee_node,
                    m.callee_name_node,
                    &m.replacement_name,
                );
                for i in 0..m.handler_results.len() {
                    tracker.replace_node(
                        m.source_file,
                        m.handler_results[i],
                        m.succeed_arguments[i],
                        None,
                    );
                }
            },
        ) {
            return vec![action];
        }
    }
    Vec::new()
}
