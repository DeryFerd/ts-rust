//! Port of Effect-TS/tsgo `internal/fixables/multiple_effect_provide.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::multiple_effect_provide::analyze_multiple_effect_provide;
use crate::effect::typeparser::{find_effect_module_identifier, find_module_identifier};
use crate::ls::CodeAction;
use crate::ls::change::NodeOptions;
use crate::prelude::*;

// Go: fixables/multiple_effect_provide.go:15 MultipleEffectProvideFix
pub static MULTIPLE_EFFECT_PROVIDE_FIX: Fixable = Fixable {
    name: "multipleEffectProvide",
    description: "Combine into a single provide",
    // Go: tsdiag.This_expression_chains_multiple_Effect_provide_calls_Providing_Layers_in_multiple_calls_in_a_chain_can_break_service_lifecycle_behavior_compared_with_a_single_combined_provide_with_merged_layers_effect_multipleEffectProvide
    error_codes: &[377033],
    fix_ids: &["multipleEffectProvide_fix"],
    run: run_multiple_effect_provide_fix,
};

// Go: fixables/multiple_effect_provide.go:23 runMultipleEffectProvideFix
fn run_multiple_effect_provide_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let mut actions = Vec::new();

    let matches = analyze_multiple_effect_provide(ctx.tp, sf);
    for m in matches {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        // Resolve the Effect module name, preserving import aliases
        let mut effect_module_name = find_effect_module_identifier(sf);
        if m.effect_module_node.is_some() && m.effect_module_node.kind() == SyntaxKind::Identifier {
            effect_module_name = get_text_of_node(m.effect_module_node);
        }

        // Resolve the Layer module name from the source file imports
        let layer_module_name = find_module_identifier(sf, "Layer");

        // Capture loop variables for the closure
        let chunk = &m.chunk;
        let layer_args = &m.layer_args;

        if let Some(action) =
            ctx.new_fix_action("Combine into a single provide".to_string(), |tracker| {
                // Step 1: Delete the range spanning all consecutive provide call expressions
                let token_pos = get_token_pos_of_node(chunk[0], sf, false);
                let end_pos = chunk[chunk.len() - 1].end();
                tracker.delete_range(sf, TextRange::new(token_pos, end_pos));

                // Step 2: Build Effect.provide(Layer.mergeAll(arg1, arg2, ...))
                let f = tracker.node_factory();
                let effect_id = f.new_identifier(effect_module_name.as_str());
                let provide_access = f.new_property_access_expression(
                    effect_id,
                    Node::NIL,
                    f.new_identifier("provide"),
                    NodeFlags::NONE,
                );

                let layer_id = f.new_identifier(layer_module_name.as_str());
                let merge_all_access = f.new_property_access_expression(
                    layer_id,
                    Node::NIL,
                    f.new_identifier("mergeAll"),
                    NodeFlags::NONE,
                );

                // Clone all layer arguments
                let cloned_args: Vec<Node> = layer_args
                    .iter()
                    .map(|&arg| f.deep_clone_node(arg))
                    .collect();

                let merge_all_call = f.new_call_expression(
                    merge_all_access,
                    Node::NIL,
                    NodeList::NIL,
                    f.new_node_list(&cloned_args),
                    NodeFlags::NONE,
                );

                let provide_call = f.new_call_expression(
                    provide_access,
                    Node::NIL,
                    NodeList::NIL,
                    f.new_node_list(&[merge_all_call]),
                    NodeFlags::NONE,
                );

                set_parent_in_children(provide_call);

                // Step 3: Insert the new node at the position of the first deleted call
                tracker.insert_node_at(sf, token_pos, provide_call, NodeOptions::default());
            })
        {
            actions.push(action);
        }
    }

    actions
}
