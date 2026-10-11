//! Port of Effect-TS/tsgo `internal/fixables/schema_struct_with_tag.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::schema_struct_with_tag::analyze_schema_struct_with_tag;
use crate::effect::typeparser::find_module_identifier;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/schema_struct_with_tag.go:13 SchemaStructWithTagFix
pub static SCHEMA_STRUCT_WITH_TAG_FIX: Fixable = Fixable {
    name: "schemaStructWithTag",
    description: "Rewrite as Schema.TaggedStruct",
    // Go: tsdiag.This_Schema_Struct_includes_a_tag_field_Schema_TaggedStruct_is_the_tagged_struct_form_for_this_pattern_and_makes_the_tag_optional_in_the_constructor_effect_schemaStructWithTag
    error_codes: &[377036],
    fix_ids: &["schemaStructWithTag_fix"],
    run: run_schema_struct_with_tag_fix,
};

// Go: fixables/schema_struct_with_tag.go:21 runSchemaStructWithTagFix
fn run_schema_struct_with_tag_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_schema_struct_with_tag(ctx.tp, sf);
    for m in matches {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }

        // Capture loop variables for the closure
        let tag_value = &m.tag_value;
        let other_properties = &m.other_properties;
        let call_node = m.call_node;
        let schema_expr = m.schema_expr;

        if let Some(action) =
            ctx.new_fix_action("Rewrite as Schema.TaggedStruct".to_string(), |tracker| {
                let f = tracker.node_factory();
                let schema_module = if schema_expr.is_some() {
                    f.deep_clone_node(schema_expr)
                } else {
                    f.new_identifier(find_module_identifier(sf, "Schema"))
                };
                // Build Schema.TaggedStruct property access, preserving the receiver.
                let tagged_struct_access = f.new_property_access_expression(
                    schema_module,
                    Node::NIL,
                    f.new_identifier("TaggedStruct"),
                    NodeFlags::NONE,
                );

                // Build the tag value string literal argument
                let tag_literal = f.new_string_literal(tag_value.as_str(), TokenFlags::NONE);

                // Deep-clone each remaining property and build the new object literal
                let cloned_props: Vec<Node> = other_properties
                    .iter()
                    .map(|&prop| f.deep_clone_node(prop))
                    .collect();
                let new_obj_literal =
                    f.new_object_literal_expression(f.new_node_list(&cloned_props), false);

                // Build Schema.TaggedStruct("tagValue", { ...rest })
                let new_call = f.new_call_expression(
                    tagged_struct_access,
                    Node::NIL,
                    NodeList::NIL,
                    f.new_node_list(&[tag_literal, new_obj_literal]),
                    NodeFlags::NONE,
                );

                set_parent_in_children(new_call);
                tracker.replace_node(sf, call_node, new_call, None);
            })
        {
            return vec![action];
        }
        return Vec::new();
    }

    Vec::new()
}
