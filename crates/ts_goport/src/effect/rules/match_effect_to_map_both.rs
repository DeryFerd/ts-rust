//! Port of Effect-TS/tsgo `internal/rules/match_effect_to_map_both.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// MatchEffectToMapBoth suggests mapBoth when matchEffect only maps the error
/// and success channels through Effect.fail and Effect.succeed, respectively.
pub static MATCH_EFFECT_TO_MAP_BOTH: Rule = Rule {
    name: "matchEffectToMapBoth",
    group: "style",
    description: "Suggests Effect.mapBoth when Effect.matchEffect only transforms the failure and success channels",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377126],
    run: run_match_effect_to_map_both,
};

fn run_match_effect_to_map_both(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_match_effect_to_map_both(ctx.tp, ctx.source_file);
    let mut diagnostics = Vec::with_capacity(matches.len());
    for m in matches {
        diagnostics.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_mapBoth_expresses_these_failure_and_success_transformations_more_directly_than_Effect_matchEffect_effect_matchEffectToMapBoth,
            Vec::new(),
            Vec::new(),
        ));
    }
    diagnostics
}

pub struct MatchEffectToMapBothMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub callee_node: Node,
    pub callee_name_node: Node,
    pub handler_results: [Node; 2],
    pub constructor_args: [Node; 2],
}

// Go: rules/match_effect_to_map_both.go AnalyzeMatchEffectToMapBoth
pub fn analyze_match_effect_to_map_both(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<MatchEffectToMapBothMatch> {
    if sf.is_nil() {
        return Vec::new();
    }
    let mut matches = Vec::new();
    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        for transformation in &flow.transformations {
            if transformation.args.len() != 1
                || transformation.callee.is_nil()
                || !tp.is_node_reference_to_effect_module_api(transformation.callee, "matchEffect")
            {
                continue;
            }

            let on_failure =
                object_literal_property_initializer(transformation.args[0], "onFailure");
            let on_success =
                object_literal_property_initializer(transformation.args[0], "onSuccess");
            if on_failure.is_nil() || on_success.is_nil() {
                continue;
            }
            let (failure_result, failure_argument, ok) =
                super::match_effect_to_match::match_effect_constructor_handler(
                    tp, on_failure, "fail",
                );
            if !ok {
                continue;
            }
            let (success_result, success_argument, ok) =
                super::match_effect_to_match::match_effect_constructor_handler(
                    tp, on_success, "succeed",
                );
            if !ok {
                continue;
            }
            let mut callee_name = Node::NIL;
            if transformation.callee.kind() == SyntaxKind::PropertyAccessExpression {
                callee_name = transformation.callee.name();
            }
            matches.push(MatchEffectToMapBothMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, transformation.callee),
                callee_node: transformation.callee,
                callee_name_node: callee_name,
                handler_results: [failure_result, success_result],
                constructor_args: [failure_argument, success_argument],
            });
        }
    }
    matches
}
