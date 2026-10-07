//! Port of Effect-TS/tsgo `internal/rules/catch_unfailable_effect.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// Go `catchFunctions`: the Effect module catch functions to check (V3 and V4).
static CATCH_FUNCTIONS: &[&str] = &[
    "catch",
    "catchAll",
    "catchIf",
    "catchSome",
    "catchTag",
    "catchTags",
];

// Go: rules.CatchUnfailableEffect
/// CatchUnfailableEffect detects when error-handling functions are applied
/// to an Effect whose error type is never, meaning the handler will never trigger.
pub static CATCH_UNFAILABLE_EFFECT: Rule = Rule {
    name: "catchUnfailableEffect",
    group: "antipattern",
    description: "Warns when using error handling on Effects that never fail",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377009],
    run: run_catch_unfailable_effect,
};

fn run_catch_unfailable_effect(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diags = Vec::new();

    let flows = ctx.tp.piping_flows(ctx.source_file, true);
    for flow in flows.iter() {
        for (i, transformation) in flow.transformations.iter().enumerate() {
            if !is_catch_callee(ctx.tp, transformation.callee) {
                continue;
            }

            // Determine the input type for this transformation
            let input_type = if i == 0 {
                flow.subject.out_type
            } else {
                flow.transformations[i - 1].out_type
            };
            if input_type.is_nil() {
                continue;
            }

            // Parse input type as an Effect
            let Some(effect) = ctx.tp.effect_type(input_type) else {
                continue;
            };

            // Check if E is never
            if effect.e.is_nil()
                || !ctx
                    .tp
                    .checker
                    .ty(effect.e)
                    .flags()
                    .intersects(TypeFlags::NEVER)
            {
                continue;
            }

            diags.push(ctx.new_diagnostic(
                get_source_file_of_node(transformation.callee),
                ctx.get_error_range(transformation.callee),
                diag::The_previous_Effect_does_not_fail_so_this_error_handling_branch_will_never_run_effect_catchUnfailableEffect,
                Vec::new(),
                Vec::new(),
            ));
        }
    }

    diags
}

// Go: rules.isCatchCallee
/// isCatchCallee checks if a node references one of the Effect module catch functions.
fn is_catch_callee(tp: &mut TypeParser<'_>, node: Node) -> bool {
    for name in CATCH_FUNCTIONS {
        if tp.is_node_reference_to_effect_module_api(node, name) {
            return true;
        }
    }
    false
}
