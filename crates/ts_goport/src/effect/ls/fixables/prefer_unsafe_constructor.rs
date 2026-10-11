//! Port of Effect-TS/tsgo `internal/fixables/prefer_unsafe_constructor.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::prefer_unsafe_constructor::analyze_prefer_unsafe_constructor;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/prefer_unsafe_constructor.go:14 PreferUnsafeConstructorFix
pub static PREFER_UNSAFE_CONSTRUCTOR_FIX: Fixable = Fixable {
    name: "preferUnsafeConstructor",
    description: "Replace Effect.runSync of a pure constructor with the synchronous *Unsafe variant",
    // Go: tsdiag.X_0_starts_a_fiber_to_run_a_pure_constructor_Use_the_synchronous_variant_1_instead_effect_preferUnsafeConstructor
    error_codes: &[377109],
    fix_ids: &["preferUnsafeConstructor_fix"],
    run: run_prefer_unsafe_constructor_fix,
};

// Go: fixables/prefer_unsafe_constructor.go:24 runPreferUnsafeConstructorFix
fn run_prefer_unsafe_constructor_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    for m in analyze_prefer_unsafe_constructor(ctx.tp, sf) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        // A bare identifier callee (e.g. `import { make } from "effect/Scope"`) has no
        // local binding for the sibling, so renaming it would leave an unbound identifier.
        if m.inner_callee.kind() != SyntaxKind::PropertyAccessExpression {
            continue;
        }

        if let Some(action) = ctx.new_fix_action(
            format!("Replace with {}", m.unsafe_callee_text),
            |tracker| {
                let outer_start = get_token_pos_of_node(m.outer_call, sf, false);
                let inner_start = get_token_pos_of_node(m.inner_call, sf, false);
                tracker.delete_range(sf, TextRange::new(outer_start, inner_start));
                let unsafe_name = tracker
                    .node_factory()
                    .new_identifier(m.unsafe_name.as_str());
                tracker.replace_node(sf, m.inner_callee_name, unsafe_name, None);
                tracker.delete_range(sf, TextRange::new(m.inner_call.end(), m.outer_call.end()));
            },
        ) {
            return vec![action];
        }
    }

    Vec::new()
}
