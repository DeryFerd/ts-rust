//! Port of Effect-TS/tsgo `internal/fixables/schema_union_of_literals.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::schema_union_of_literals::analyze_schema_union_of_literals;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/schema_union_of_literals.go:12 SchemaUnionOfLiteralsFix
pub static SCHEMA_UNION_OF_LITERALS_FIX: Fixable = Fixable {
    name: "schemaUnionOfLiterals",
    description: "Replace with a single Schema.Literal call",
    // Go: tsdiag.This_Schema_Union_contains_multiple_Schema_Literal_members_and_can_be_simplified_to_a_single_Schema_Literal_call_effect_schemaUnionOfLiterals
    error_codes: &[377038],
    fix_ids: &["schemaUnionOfLiterals_fix"],
    run: run_schema_union_of_literals_fix,
};

// Go: fixables/schema_union_of_literals.go:20 runSchemaUnionOfLiteralsFix
fn run_schema_union_of_literals_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_schema_union_of_literals(ctx.tp, sf);
    for m in matches {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }

        // Capture loop variables for the closure
        let union_call_node = m.union_call_node;
        let first_literal_expression = m.first_literal_expression;
        let all_literal_args = &m.all_literal_args;

        if let Some(action) = ctx.new_fix_action(
            "Replace with a single Schema.Literal call".to_string(),
            |tracker| {
                let f = tracker.node_factory();
                let cloned_expression = f.deep_clone_node(first_literal_expression);
                let cloned_args: Vec<Node> = all_literal_args
                    .iter()
                    .map(|&arg| f.deep_clone_node(arg))
                    .collect();
                let new_call = f.new_call_expression(
                    cloned_expression,
                    Node::NIL,
                    NodeList::NIL,
                    f.new_node_list(&cloned_args),
                    NodeFlags::NONE,
                );
                set_parent_in_children(new_call);
                tracker.replace_node(sf, union_call_node, new_call, None);
            },
        ) {
            return vec![action];
        }
        return Vec::new();
    }

    Vec::new()
}
