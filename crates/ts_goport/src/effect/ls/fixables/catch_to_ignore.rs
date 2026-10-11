//! Port of Effect-TS/tsgo `internal/fixables/catch_to_ignore.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::effect_module_method;
use crate::effect::ls::rewriter::{PipingFlowTransformationReplacement, Tracker};
use crate::effect::rules::catch_to_ignore::{CatchToIgnoreMatch, analyze_catch_to_ignore};
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/catch_to_ignore.go:12 CatchToIgnoreFix
pub static CATCH_TO_IGNORE_FIX: Fixable = Fixable {
    name: "catchToIgnore",
    description: "Replace Effect.catch/catchCause + Effect.void with Effect.ignore/ignoreCause",
    // Go: tsdiag.Effect_1_expresses_ignored_failure_more_directly_than_Effect_0_returning_Effect_void_effect_catchToIgnore
    error_codes: &[377099],
    fix_ids: &["catchToIgnore_fix"],
    run: run_catch_to_ignore_fix,
};

// Go: fixables/catch_to_ignore.go:20 runCatchToIgnoreFix
// PORT: Go skips a match with a nil `Transformation`; the Rust match always
// has one.
fn run_catch_to_ignore_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_catch_to_ignore(ctx.tp, sf);
    for m in matches {
        let diag_range = m.location;
        if !diag_range.intersects(ctx.span) && !ctx.span.contained_by(diag_range) {
            continue;
        }

        if let Some(action) = ctx.new_fix_action(
            format!("Replace with Effect.{}", m.ignore_method_name),
            |tracker| {
                let ignore_access = catch_to_ignore_replacement_access(tracker, sf, &m);
                tracker.replace_piping_flow_transformation(
                    sf,
                    &m.transformation,
                    PipingFlowTransformationReplacement::callee(ignore_access),
                );
            },
        ) {
            return vec![action];
        }
    }

    Vec::new()
}

// Go: fixables/catch_to_ignore.go:49 catchToIgnoreReplacementAccess
fn catch_to_ignore_replacement_access(tracker: &Tracker, sf: Node, m: &CatchToIgnoreMatch) -> Node {
    let replacement =
        effect_module_method(tracker, sf, m.effect_module_node, &m.ignore_method_name);
    set_parent_in_children(replacement);
    replacement
}
