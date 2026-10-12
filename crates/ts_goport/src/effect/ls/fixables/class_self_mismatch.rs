//! Port of Effect-TS/tsgo `internal/fixables/class_self_mismatch.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::class_self_mismatch::analyze_class_self_mismatch;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/class_self_mismatch.go:12 ClassSelfMismatchFix
pub static CLASS_SELF_MISMATCH_FIX: Fixable = Fixable {
    name: "classSelfMismatch",
    description: "Replace Self type parameter with the correct class name",
    // Go: tsdiag.The_Self_type_parameter_for_this_class_should_be_0_effect_classSelfMismatch
    error_codes: &[377046],
    fix_ids: &["classSelfMismatch_fix"],
    run: run_class_self_mismatch_fix,
};

// Go: fixables/class_self_mismatch.go:20 runClassSelfMismatchFix
fn run_class_self_mismatch_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_class_self_mismatch(ctx.tp, sf);
    for m in matches {
        let diag_range = m.location;
        if !diag_range.intersects(ctx.span) && !ctx.span.contained_by(diag_range) {
            continue;
        }

        // Determine the target node to replace. If the Self type node is a TypeReferenceNode,
        // replace only the TypeName identifier (preserving any type arguments).
        // Otherwise, replace the entire Self type node.
        let mut target_node = m.self_type_node;
        if is_type_reference_node(m.self_type_node) {
            target_node = m.self_type_node.type_name();
        }

        let description = format!("Replace '{}' with '{}'", m.actual_name, m.expected_name);
        if let Some(action) = ctx.new_fix_action(description, |tracker| {
            let name = tracker
                .node_factory()
                .new_identifier(m.expected_name.as_str());
            tracker.replace_node(sf, target_node, name, None);
        }) {
            return vec![action];
        }
        return Vec::new();
    }

    Vec::new()
}
