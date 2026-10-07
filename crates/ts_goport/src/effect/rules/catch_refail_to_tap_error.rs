// Go: internal/rules/catch_refail_to_tap_error.go

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// CatchRefailToTapError recognizes observation followed by an unchanged refail.
pub static CATCH_REFAIL_TO_TAP_ERROR: Rule = Rule {
    name: "catchRefailToTapError",
    group: "style",
    description: "Suggests Effect.tapError for catch handlers that sequence an effect and then re-fail the original error",
    default_severity: Severity::Suggestion,
    supported_effect: &["v4"],
    codes: &[377133],
    run: run_catch_refail_to_tap_error,
};

fn run_catch_refail_to_tap_error(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    if ctx.tp.supported_effect_version() != EffectMajorVersion::V4 {
        return Vec::new();
    }
    let mut diagnostics = Vec::new();
    let flows = ctx.tp.piping_flows(ctx.source_file, true);
    for flow in flows.iter() {
        for i in 0..flow.transformations.len() {
            let step = &flow.transformations[i];
            if step.args.len() != 1
                || !ctx
                    .tp
                    .is_node_reference_to_effect_module_api(step.callee, "catch")
            {
                continue;
            }
            let input = ctx
                .tp
                .strict_effect_type(flow.transformation_input_type(i as i32));
            let Some(input) = input else {
                continue;
            };
            if input.e.is_nil()
                || ctx
                    .tp
                    .checker
                    .ty(input.e)
                    .flags
                    .intersects(TypeFlags::NEVER)
                || !catch_handler_refails_original_error(ctx.tp, step.args[0])
            {
                continue;
            }
            diagnostics.push(ctx.new_diagnostic(
                ctx.source_file,
                get_error_range_for_node(ctx.source_file, step.callee),
                diag::Use_Effect_tapError_to_observe_the_error_and_preserve_the_original_failure_without_having_to_re_fail_it_effect_catchRefailToTapError,
                Vec::new(),
                Vec::new(),
            ));
        }
    }
    diagnostics
}

// Go: rules/catch_refail_to_tap_error.go catchHandlerRefailsOriginalError
fn catch_handler_refails_original_error(tp: &mut TypeParser<'_>, handler: Node) -> bool {
    let Some(lazy) = parse_lazy_expression(handler, LazyExpressionFlags::NONE) else {
        return false;
    };
    if lazy.params.len() != 1 {
        return false;
    }
    let parameter = lazy.params[0];
    if parameter.name().is_nil()
        || parameter.name().kind() != SyntaxKind::Identifier
        || parameter.initializer().is_some()
        || parameter.dot_dot_dot_token().is_some()
    {
        return false;
    }
    let error_symbol = tp.get_symbol_at_location(parameter.name());
    if error_symbol.is_nil() || tp.checker.is_symbol_assigned(error_symbol) {
        return false;
    }

    let Some(flow) = tp.longest_piping_flow_at(lazy.expression, false) else {
        return false;
    };
    if flow.transformations.is_empty() {
        return false;
    }
    let last = flow.transformations.len() - 1;
    let step = &flow.transformations[last];
    if step.args.len() != 1
        || tp
            .strict_effect_type(flow.transformation_input_type(last as i32))
            .is_none()
    {
        return false;
    }

    let mut refail = step.args[0];
    if tp.is_node_reference_to_effect_module_api(step.callee, "andThen") {
        // andThen accepts both an Effect and a callback. Only a zero-argument
        // callback can be discarded without binding the preceding success value.
        if let Some(thunk) = parse_lazy_expression(refail, LazyExpressionFlags::THUNK) {
            refail = thunk.expression;
        }
    } else if tp.is_node_reference_to_effect_module_api(step.callee, "flatMap") {
        let Some(thunk) = parse_lazy_expression(refail, LazyExpressionFlags::THUNK) else {
            return false;
        };
        refail = thunk.expression;
    } else {
        return false;
    }

    // Matching the whole inner flow excludes recovery or other work after fail,
    // and excludes expressions which merely compute a different error value.
    let Some(inner) = tp.longest_piping_flow_at(refail, false) else {
        // Go: a nil flow does not match.
        return false;
    };
    inner.matches_exactly(
        tp,
        &mut |tp: &mut TypeParser<'_>, subject: &PipingFlowSubject| {
            let node = skip_parentheses(subject.node);
            node.is_some()
                && node.kind() == SyntaxKind::Identifier
                && tp.get_symbol_at_location(node) == error_symbol
        },
        &mut [
            &mut |tp: &mut TypeParser<'_>, step: &PipingFlowTransformation| {
                step.args.is_empty()
                    && tp.is_node_reference_to_effect_module_api(step.callee, "fail")
            },
        ],
    )
}
