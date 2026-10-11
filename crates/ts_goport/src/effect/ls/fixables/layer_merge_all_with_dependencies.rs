//! Port of Effect-TS/tsgo `internal/fixables/layer_merge_all_with_dependencies.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::layer_merge_all_with_dependencies::analyze_layer_merge_all_with_dependencies;
use crate::effect::typeparser::find_module_identifier;
use crate::ls::CodeAction;
use crate::ls::change::NodeOptions;
use crate::prelude::*;

// Go: fixables/layer_merge_all_with_dependencies.go:14 LayerMergeAllWithDependenciesFix
pub static LAYER_MERGE_ALL_WITH_DEPENDENCIES_FIX: Fixable = Fixable {
    name: "layerMergeAllWithDependencies",
    description: "Move layer to Layer.provideMerge",
    // Go: tsdiag.This_layer_provides_0_which_is_required_by_another_layer_in_the_same_Layer_mergeAll_call_Layer_mergeAll_creates_layers_in_parallel_so_dependencies_between_layers_will_not_be_satisfied_Consider_moving_this_layer_into_a_Layer_provideMerge_after_the_Layer_mergeAll_effect_layerMergeAllWithDependencies
    error_codes: &[377035],
    fix_ids: &["layerMergeAllWithDependencies_fix"],
    run: run_layer_merge_all_with_dependencies_fix,
};

// Go: fixables/layer_merge_all_with_dependencies.go:22 runLayerMergeAllWithDependenciesFix
fn run_layer_merge_all_with_dependencies_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_layer_merge_all_with_dependencies(ctx.tp, sf);
    for m in matches {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        if m.call_node.is_nil() || m.call_node.kind() != SyntaxKind::CallExpression {
            continue;
        }
        let call_expression = m.call_node.expression();
        let mut layer_module_node = Node::NIL;
        if call_expression.is_some()
            && call_expression.kind() == SyntaxKind::PropertyAccessExpression
        {
            layer_module_node = call_expression.expression();
        }
        let ctx: &FixableContext<'_, '_> = ctx;
        if let Some(action) =
            ctx.new_fix_action("Move layer to Layer.provideMerge".to_string(), |tracker| {
                // Step A: Delete the provider argument from the mergeAll call
                if m.provider_index == 0 && m.all_args.len() > 1 {
                    // First argument with more args: delete from arg start to next arg start
                    tracker.delete_range(
                        sf,
                        TextRange::new(m.provider_arg.pos(), m.all_args[1].pos()),
                    );
                } else if m.provider_index > 0 {
                    // Not first argument: delete from previous arg end to this arg end
                    tracker.delete_range(
                        sf,
                        TextRange::new(
                            m.all_args[(m.provider_index - 1) as usize].end(),
                            m.provider_arg.end(),
                        ),
                    );
                }

                // Step B: Build Layer.provideMerge(providerArg) call expression
                let f = tracker.node_factory();
                let cloned_provider_arg = f.deep_clone_node(m.provider_arg);
                let cloned_layer_module = if layer_module_node.is_nil() {
                    f.new_identifier(find_module_identifier(sf, "Layer"))
                } else {
                    f.deep_clone_node(layer_module_node)
                };

                let provide_merge_access = f.new_property_access_expression(
                    cloned_layer_module,
                    Node::NIL,
                    f.new_identifier("provideMerge"),
                    NodeFlags::NONE,
                );

                let provide_merge_call = f.new_call_expression(
                    provide_merge_access,
                    Node::NIL,
                    NodeList::NIL,
                    f.new_node_list(&[cloned_provider_arg]),
                    NodeFlags::NONE,
                );

                set_parent_in_children(provide_merge_call);

                // Step C: Insert .pipe(Layer.provideMerge(...)) at the end of the call
                // Use two separate operations because the Suffix dedup logic in the
                // change tracker skips ")" when the formatted call already ends with ")".
                tracker.insert_node_at(
                    sf,
                    m.call_node.end(),
                    provide_merge_call,
                    NodeOptions {
                        prefix: ".pipe(".to_string(),
                        ..NodeOptions::default()
                    },
                );
                tracker.insert_text(sf, ctx.byte_pos_to_lsp_position(m.call_node.end()), ")");
            })
        {
            return vec![action];
        }
    }

    Vec::new()
}
