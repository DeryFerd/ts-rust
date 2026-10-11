//! Port of Effect-TS/tsgo `internal/fixables/prefer_succeed_some_or_none.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::prefer_succeed_some_or_none::analyze_prefer_succeed_some_or_none;
use crate::effect::typeparser::find_effect_module_identifier;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/prefer_succeed_some_or_none.go:13 PreferSucceedSomeOrNoneFix
pub static PREFER_SUCCEED_SOME_OR_NONE_FIX: Fixable = Fixable {
    name: "preferSucceedSomeOrNone",
    description: "Replace with the direct Effect Option constructor",
    // Go: tsdiag.Effect_0_expresses_this_Option_success_value_directly_effect_preferSucceedSomeOrNone
    error_codes: &[377117],
    fix_ids: &["preferSucceedSomeOrNone_fix"],
    run: run_prefer_succeed_some_or_none_fix,
};

// Go: fixables/prefer_succeed_some_or_none.go:23 runPreferSucceedSomeOrNoneFix
fn run_prefer_succeed_some_or_none_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    for m in analyze_prefer_succeed_some_or_none(ctx.tp, ctx.source_file) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        let Some(flow) = m.flow.as_deref() else {
            continue;
        };
        if m.transformation_count <= 0
            || m.replacement_name == "succeedSome" && m.value_node.is_nil()
        {
            continue;
        }

        let description = format!("Replace with Effect.{}", m.replacement_name);
        let sf = ctx.source_file;
        if let Some(action) = ctx.new_fix_action(description, |tracker| {
            let f = tracker.node_factory();
            let module_node = if m.effect_module_node.is_nil() {
                f.new_identifier(find_effect_module_identifier(sf))
            } else {
                f.deep_clone_node(m.effect_module_node)
            };
            let callee = f.new_property_access_expression(
                module_node,
                Node::NIL,
                f.new_identifier(m.replacement_name.as_str()),
                NodeFlags::NONE,
            );
            let mut replacement = callee;
            if m.value_node.is_some() {
                let mut type_arguments = NodeList::NIL;
                if m.value_type_arguments.is_some() && !m.value_type_arguments.nodes().is_empty() {
                    let arguments: Vec<Node> = m
                        .value_type_arguments
                        .nodes()
                        .iter()
                        .map(|argument| f.deep_clone_node(argument))
                        .collect();
                    type_arguments = f.new_node_list(&arguments);
                }
                replacement = f.new_call_expression(
                    callee,
                    Node::NIL,
                    type_arguments,
                    f.new_node_list(&[f.deep_clone_node(m.value_node)]),
                    NodeFlags::NONE,
                );
            }
            tracker.replace_piping_flow_prefix(sf, flow, m.transformation_count, replacement);
        }) {
            return vec![action];
        }
    }

    Vec::new()
}
