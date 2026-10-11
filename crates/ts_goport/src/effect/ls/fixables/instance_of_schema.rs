//! Port of Effect-TS/tsgo `internal/fixables/instance_of_schema.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::instance_of_schema::analyze_instance_of_schema;
use crate::effect::typeparser::find_module_identifier;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/instance_of_schema.go:13 InstanceOfSchemaFix
pub static INSTANCE_OF_SCHEMA_FIX: Fixable = Fixable {
    name: "instanceOfSchema",
    description: "Replace with Schema.is",
    // Go: tsdiag.This_code_uses_instanceof_with_an_Effect_Schema_type_Schema_is_is_the_schema_aware_runtime_check_for_this_case_effect_instanceOfSchema
    error_codes: &[377042],
    fix_ids: &["instanceOfSchema_fix"],
    run: run_instance_of_schema_fix,
};

// Go: fixables/instance_of_schema.go:21 runInstanceOfSchemaFix
fn run_instance_of_schema_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_instance_of_schema(ctx.tp, sf);
    for m in matches {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }

        if let Some(action) = ctx.new_fix_action("Replace with Schema.is".to_string(), |tracker| {
            let f = tracker.node_factory();
            let cloned_left = f.deep_clone_node(m.left_expr);
            let cloned_right = f.deep_clone_node(m.right_expr);

            // Build Schema.is property access
            let schema_is_access = f.new_property_access_expression(
                f.new_identifier(find_module_identifier(sf, "Schema")),
                Node::NIL,
                f.new_identifier("is"),
                NodeFlags::NONE,
            );

            // Build inner call: Schema.is(right)
            let inner_call = f.new_call_expression(
                schema_is_access,
                Node::NIL,
                NodeList::NIL,
                f.new_node_list(&[cloned_right]),
                NodeFlags::NONE,
            );

            // Build outer call: Schema.is(right)(left)
            let outer_call = f.new_call_expression(
                inner_call,
                Node::NIL,
                NodeList::NIL,
                f.new_node_list(&[cloned_left]),
                NodeFlags::NONE,
            );

            set_parent_in_children(outer_call);
            tracker.replace_node(sf, m.instance_of_node, outer_call, None);
        }) {
            return vec![action];
        }
    }

    Vec::new()
}
