//! Port of Effect-TS/tsgo `internal/fixables/effect_fn_iife.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::effect_module_method;
use crate::effect::rules::effect_fn_iife::analyze_effect_fn_iife;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/effect_fn_iife.go:12 EffectFnIifeFix
pub static EFFECT_FN_IIFE_FIX: Fixable = Fixable {
    name: "effectFnIife",
    description: "Convert Effect.fn IIFE to Effect.gen",
    // Go: tsdiag.X_0_1_returns_a_reusable_function_that_can_take_arguments_but_it_is_invoked_immediately_here_Effect_gen_represents_the_immediate_use_form_for_this_pattern_2_effect_effectFnIife
    error_codes: &[377011],
    fix_ids: &["effectFnIife_toEffectGen"],
    run: run_effect_fn_iife_fix,
};

// Go: fixables/effect_fn_iife.go:20 runEffectFnIifeFix
fn run_effect_fn_iife_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    // Use shared analysis to find all IIFE matches, then find the one at the diagnostic span
    let matches = analyze_effect_fn_iife(ctx.tp, sf);
    let Some(result) = matches
        .into_iter()
        .find(|m| m.location.intersects(ctx.span) || ctx.span.contained_by(m.location))
        .map(|m| m.result)
    else {
        return Vec::new();
    };

    // Only produce a fix for generator functions with zero parameters
    let gen_fn = result.generator_function;
    if gen_fn.is_nil() {
        return Vec::new();
    }
    if !gen_fn.parameter_list().is_nil() && !gen_fn.parameters().is_empty() {
        return Vec::new();
    }

    if let Some(action) = ctx.new_fix_action("Convert to Effect.gen".to_string(), |tracker| {
        let f = tracker.node_factory();
        // Deep-clone the generator function to produce a synthesized copy
        let cloned_gen_fn = f.deep_clone_node(gen_fn);

        // Build Effect.gen, preserving a direct receiver or finding the imported module.
        let effect_gen_access = effect_module_method(tracker, sf, result.effect_module, "gen");

        // Build Effect.gen(genFn) call expression
        let f = tracker.node_factory();
        let gen_call_node = f.new_call_expression(
            effect_gen_access,
            Node::NIL,
            NodeList::NIL,
            f.new_node_list(&[cloned_gen_fn]),
            NodeFlags::NONE,
        );

        // If pipe arguments exist, wrap with .pipe(...)
        let mut replacement_node = gen_call_node;
        if !result.pipe_arguments.is_empty() {
            let cloned_args: Vec<Node> = result
                .pipe_arguments
                .iter()
                .map(|&arg| f.deep_clone_node(arg))
                .collect();
            let pipe_access = f.new_property_access_expression(
                gen_call_node,
                Node::NIL,
                f.new_identifier("pipe"),
                NodeFlags::NONE,
            );
            replacement_node = f.new_call_expression(
                pipe_access,
                Node::NIL,
                NodeList::NIL,
                f.new_node_list(&cloned_args),
                NodeFlags::NONE,
            );
        }

        // Set parent pointers on the entire replacement tree so the
        // formatter's token-walking code doesn't panic on nil Parent
        set_parent_in_children(replacement_node);

        tracker.replace_node(sf, result.outer_call, replacement_node, None);
    }) {
        return vec![action];
    }
    Vec::new()
}
