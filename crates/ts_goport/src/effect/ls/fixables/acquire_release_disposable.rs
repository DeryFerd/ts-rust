//! Port of Effect-TS/tsgo `internal/fixables/acquire_release_disposable.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::effect_module_method;
use crate::effect::rules::acquire_release_disposable::analyze_acquire_release_disposable;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/acquire_release_disposable.go:12 AcquireReleaseDisposableFix
pub static ACQUIRE_RELEASE_DISPOSABLE_FIX: Fixable = Fixable {
    name: "acquireReleaseDisposable",
    description: "Replace Effect.acquireRelease with Effect.acquireDisposable",
    // Go: tsdiag.Effect_acquireDisposable_expresses_this_disposable_resource_acquisition_more_directly_than_Effect_acquireRelease_with_a_manual_disposal_finalizer_effect_acquireReleaseDisposable
    error_codes: &[377119],
    fix_ids: &["acquireReleaseDisposable_fix"],
    run: run_acquire_release_disposable_fix,
};

// Go: fixables/acquire_release_disposable.go:22 runAcquireReleaseDisposableFix
fn run_acquire_release_disposable_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;
    for m in analyze_acquire_release_disposable(ctx.tp, sf) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        if m.has_type_arguments {
            continue;
        }

        if let Some(action) = ctx.new_fix_action(
            "Replace with Effect.acquireDisposable".to_string(),
            |tracker| {
                let callee =
                    effect_module_method(tracker, sf, m.effect_module, "acquireDisposable");
                let f = tracker.node_factory();
                let replacement = f.new_call_expression(
                    callee,
                    Node::NIL,
                    NodeList::NIL,
                    f.new_node_list(&[f.deep_clone_node(m.acquire)]),
                    NodeFlags::NONE,
                );
                set_parent_in_children(replacement);
                tracker.replace_node(sf, m.call_node, replacement, None);
            },
        ) {
            return vec![action];
        }
    }
    Vec::new()
}
