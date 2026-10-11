//! Port of Effect-TS/tsgo `internal/fixables/unnecessary_typeof_type.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::unnecessary_typeof_type::analyze_unnecessary_typeof_type;
use crate::ls::CodeAction;

// Go: fixables/unnecessary_typeof_type.go:11 UnnecessaryTypeofTypeFix
pub static UNNECESSARY_TYPEOF_TYPE_FIX: Fixable = Fixable {
    name: "unnecessaryTypeofType",
    description: "Replace with the matching named type",
    // Go: tsdiag.This_typeof_Type_query_can_be_replaced_with_0_effect_unnecessaryTypeofType
    error_codes: &[377090],
    fix_ids: &["unnecessaryTypeofType_fix"],
    run: run_unnecessary_typeof_type_fix,
};

// Go: fixables/unnecessary_typeof_type.go:19 runUnnecessaryTypeofTypeFix
fn run_unnecessary_typeof_type_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;
    let matches = analyze_unnecessary_typeof_type(ctx.tp, sf);
    for m in matches {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }

        let description = format!("Replace with '{}'", m.replacement_text);
        if let Some(action) = ctx.new_fix_action(description, |tracker| {
            let new_node = tracker.node_factory().deep_clone_node(m.inner_entity_name);
            tracker.replace_node(sf, m.query_node, new_node, None);
        }) {
            return vec![action];
        }
        return Vec::new();
    }

    Vec::new()
}
