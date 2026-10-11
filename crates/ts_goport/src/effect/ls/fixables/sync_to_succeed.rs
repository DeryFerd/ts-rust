//! Port of Effect-TS/tsgo `internal/fixables/sync_to_succeed.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::replace_effect_method_callee;
use crate::effect::rules::sync_to_succeed::analyze_sync_to_succeed;
use crate::ls::CodeAction;

// Go: fixables/sync_to_succeed.go:11 SyncToSucceedFix
pub static SYNC_TO_SUCCEED_FIX: Fixable = Fixable {
    name: "syncToSucceed",
    description: "Replace Effect.sync with Effect.succeed",
    // Go: tsdiag.Effect_succeed_expresses_this_constant_value_more_directly_than_Effect_sync_effect_syncToSucceed
    error_codes: &[377103],
    fix_ids: &["syncToSucceed_fix"],
    run: run_sync_to_succeed_fix,
};

// Go: fixables/sync_to_succeed.go:21 runSyncToSucceedFix
fn run_sync_to_succeed_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    for m in analyze_sync_to_succeed(ctx.tp, ctx.source_file) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        if m.callee.is_nil() {
            continue;
        }

        let sf = ctx.source_file;
        if let Some(action) =
            ctx.new_fix_action("Replace with Effect.succeed".to_string(), |tracker| {
                replace_effect_method_callee(tracker, sf, m.callee, m.callee_name, "succeed");
                tracker.replace_node(sf, m.thunk, m.constant_value, None);
            })
        {
            return vec![action];
        }
    }

    Vec::new()
}
