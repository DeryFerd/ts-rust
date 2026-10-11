//! Port of Effect-TS/tsgo `internal/fixables/all_of_map_to_for_each.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::effect_module_method;
use crate::effect::rules::all_of_map_to_for_each::analyze_all_of_map_to_for_each;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/all_of_map_to_for_each.go:12 AllOfMapToForEachFix
pub static ALL_OF_MAP_TO_FOR_EACH_FIX: Fixable = Fixable {
    name: "allOfMapToForEach",
    description: "Replace Effect.all over Array#map with Effect.forEach",
    // Go: tsdiag.Effect_forEach_expresses_this_effectful_array_mapping_more_directly_than_Effect_all_over_Array_map_effect_allOfMapToForEach
    error_codes: &[377113],
    fix_ids: &["allOfMapToForEach_fix"],
    run: run_all_of_map_to_for_each_fix,
};

// Go: fixables/all_of_map_to_for_each.go:22 runAllOfMapToForEachFix
fn run_all_of_map_to_for_each_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    for m in analyze_all_of_map_to_for_each(ctx.tp, ctx.source_file) {
        if !m.can_fix {
            continue;
        }
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        // The generic parameter lists of Array#map, Effect.all, and Effect.forEach
        // differ, so an explicit type argument cannot be moved safely.
        if m.has_type_arguments {
            continue;
        }

        let sf = ctx.source_file;
        if let Some(action) =
            ctx.new_fix_action("Replace with Effect.forEach".to_string(), |tracker| {
                let callee = effect_module_method(tracker, sf, m.effect_module, "forEach");
                let f = tracker.node_factory();
                let mut arguments =
                    vec![f.deep_clone_node(m.receiver), f.deep_clone_node(m.callback)];
                if m.options.is_some() {
                    arguments.push(f.deep_clone_node(m.options));
                }
                let replacement = f.new_call_expression(
                    callee,
                    Node::NIL,
                    NodeList::NIL,
                    f.new_node_list(&arguments),
                    NodeFlags::NONE,
                );
                set_parent_in_children(replacement);
                tracker.replace_node(sf, m.call_node, replacement, None);
            })
        {
            return vec![action];
        }
    }
    Vec::new()
}
