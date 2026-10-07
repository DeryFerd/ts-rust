//! Port of Effect-TS/tsgo `internal/rules/flat_map_ignored_param_to_and_then.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// FlatMapIgnoredParamToAndThen suggests Effect.andThen when an Effect.flatMap
/// callback ignores the upstream value and returns an existing Effect value.
// Go: rules/flat_map_ignored_param_to_and_then.go FlatMapIgnoredParamToAndThen
pub static FLAT_MAP_IGNORED_PARAM_TO_AND_THEN: Rule = Rule {
    name: "flatMapIgnoredParamToAndThen",
    group: "style",
    description: "Suggests using Effect.andThen instead of Effect.flatMap when a zero-parameter callback returns an existing Effect value",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377132],
    run: run_flat_map_ignored_param_to_and_then,
};

fn run_flat_map_ignored_param_to_and_then(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let sf = ctx.source_file;
    let matches = analyze_flat_map_ignored_param_to_and_then(ctx.tp, sf);
    let mut diagnostics = Vec::with_capacity(matches.len());
    for m in &matches {
        diagnostics.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_andThen_expresses_this_sequencing_more_directly_than_Effect_flatMap_with_a_zero_parameter_callback_effect_flatMapIgnoredParamToAndThen,
            Vec::new(),
            Vec::new(),
        ));
    }
    diagnostics
}

/// FlatMapIgnoredParamToAndThenMatch holds the nodes needed by the diagnostic
/// and quick fix.
// Go: rules/flat_map_ignored_param_to_and_then.go FlatMapIgnoredParamToAndThenMatch
#[derive(Clone, Debug)]
pub struct FlatMapIgnoredParamToAndThenMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub callee: Node,
    pub callee_name_node: Node,
    pub callback: Node,
    pub effect_value: Node,
}

/// AnalyzeFlatMapIgnoredParamToAndThen finds Effect.flatMap piping
/// transformations whose zero-parameter expression callback returns an Effect
/// value held by an already-initialized const binding.
// Go: rules/flat_map_ignored_param_to_and_then.go AnalyzeFlatMapIgnoredParamToAndThen
pub fn analyze_flat_map_ignored_param_to_and_then(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<FlatMapIgnoredParamToAndThenMatch> {
    let mut matches = Vec::new();

    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        for transformation in &flow.transformations {
            let callee = transformation.callee;
            if callee.is_nil()
                || transformation.args.len() != 1
                || !tp.is_node_reference_to_effect_module_api(callee, "flatMap")
            {
                continue;
            }

            let Some(callback) =
                parse_lazy_expression(transformation.args[0], LazyExpressionFlags::THUNK)
            else {
                continue;
            };
            if callback.expression.is_nil()
                || !tp.is_expression_value_stable_at_location(callback.expression, callee)
            {
                continue;
            }
            let t = tp.get_type_at_location(callback.expression);
            if tp.effect_type(t).is_none() {
                continue;
            }

            let mut callee_name = Node::NIL;
            if callee.kind() == SyntaxKind::PropertyAccessExpression {
                callee_name = callee.name();
            }

            matches.push(FlatMapIgnoredParamToAndThenMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, callee),
                callee,
                callee_name_node: callee_name,
                callback: callback.node,
                effect_value: callback.expression,
            });
        }
    }

    matches
}
