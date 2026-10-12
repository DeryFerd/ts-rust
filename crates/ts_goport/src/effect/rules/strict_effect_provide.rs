//! Port of Effect-TS/tsgo `internal/rules/strict_effect_provide.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// StrictEffectProvide warns when Effect.provide is called with a Layer argument.
/// This rule is disabled by default.
// Go: rules/strict_effect_provide.go StrictEffectProvide
pub static STRICT_EFFECT_PROVIDE: Rule = Rule {
    name: "strictEffectProvide",
    group: "antipattern",
    description: "Warns when using Effect.provide with layers outside of application entry points",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377032],
    run: run_strict_effect_provide,
};

fn run_strict_effect_provide(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diags: Vec<Diagnostic> = Vec::new();

    // Stack-based traversal
    // PERF: Go walks the tree with a stack of nodes; this stack holds node
    // order indexes and pushes and pops at the same points (effperf4).
    let order = ctx.tp.node_order(ctx.source_file);
    let mut node_to_visit: Vec<u32> = order.children(0).collect();

    while let Some(i) = node_to_visit.pop() {
        let node = order.node(i);
        if node.kind() == SyntaxKind::CallExpression {
            if let Some(d) = check_effect_provide_with_layer(ctx, node) {
                diags.push(d);
            }
        }

        // Enqueue children
        node_to_visit.extend(order.children(i));
    }

    diags
}

/// checkEffectProvideWithLayer checks if a call expression is Effect.provide(...) with a Layer argument.
// Go: rules/strict_effect_provide.go checkEffectProvideWithLayer
fn check_effect_provide_with_layer(
    ctx: &mut RuleContext<'_, '_>,
    node: Node,
) -> Option<Diagnostic> {
    if node.kind() != SyntaxKind::CallExpression {
        return None;
    }
    let call = node;
    let args = call.argument_list();
    if args.is_nil() || args.nodes().is_empty() {
        return None;
    }

    // Check if the expression references Effect.provide
    if !ctx
        .tp
        .is_node_reference_to_effect_module_api(call.expression(), member!("provide"))
    {
        return None;
    }

    // Check if any argument is a Layer type
    for arg in args.nodes() {
        let arg_type = ctx.tp.get_type_at_location(arg);
        if arg_type.is_nil() {
            continue;
        }
        if ctx.tp.layer_type(arg_type).is_some() {
            // Found a Layer argument — emit diagnostic on the call expression
            return Some(ctx.new_diagnostic(
                ctx.source_file,
                ctx.get_error_range(node),
                diag::Effect_provide_with_a_Layer_should_only_be_used_at_application_entry_points_If_this_is_an_entry_point_you_can_safely_disable_this_diagnostic_Otherwise_using_Effect_provide_may_break_scope_lifetimes_Compose_all_layers_at_your_entry_point_and_provide_them_at_once_effect_strictEffectProvide,
                Vec::new(),
                vec![],
            ));
        }
    }

    None
}
