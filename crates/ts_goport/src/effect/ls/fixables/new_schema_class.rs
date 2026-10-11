//! Port of Effect-TS/tsgo `internal/fixables/new_schema_class.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::new_schema_class::analyze_new_schema_class;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/new_schema_class.go:12 NewSchemaClassFix
pub static NEW_SCHEMA_CLASS_FIX: Fixable = Fixable {
    name: "newSchemaClass",
    description: "Replace new Schema class construction with .make",
    // Go: tsdiag.This_Schema_class_is_constructed_with_new_0_make_can_be_used_to_construct_the_Schema_class_instance_effect_newSchemaClass
    error_codes: &[377094],
    fix_ids: &["newSchemaClass_fix"],
    run: run_new_schema_class_fix,
};

// Go: fixables/new_schema_class.go:20 runNewSchemaClassFix
fn run_new_schema_class_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;
    let matches = analyze_new_schema_class(ctx.tp, sf);
    for m in matches {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }

        if let Some(action) = ctx.new_fix_action("Replace with .make".to_string(), |tracker| {
            let f = tracker.node_factory();
            let cloned_class_expr = f.deep_clone_node(m.class_expr);
            let make_access = f.new_property_access_expression(
                cloned_class_expr,
                Node::NIL,
                f.new_identifier("make"),
                NodeFlags::NONE,
            );

            // PORT: Go `NewNodeList(nil)` for no arguments is an empty list,
            // not a nil one, as `new_node_list(&[])` is.
            let cloned_args: Vec<Node> = m
                .arguments
                .iter()
                .map(|&arg| f.deep_clone_node(arg))
                .collect();

            let replacement = f.new_call_expression(
                make_access,
                Node::NIL,
                NodeList::NIL,
                f.new_node_list(&cloned_args),
                NodeFlags::NONE,
            );

            set_parent_in_children(replacement);
            tracker.replace_node(sf, m.new_node, replacement, None);
        }) {
            return vec![action];
        }
        return Vec::new();
    }

    Vec::new()
}
