// Go: internal/rules/match_effect_to_match.go

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// MatchEffectToMatch suggests the non-effectful match variant when both
/// handlers only lift their result with Effect.succeed.
pub static MATCH_EFFECT_TO_MATCH: Rule = Rule {
    name: "matchEffectToMatch",
    group: "style",
    description: "Suggests Effect.match or Effect.matchCause when both Effect.matchEffect handlers only return Effect.succeed",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377125],
    run: run_match_effect_to_match,
};

fn run_match_effect_to_match(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_match_effect_to_match(ctx.tp, ctx.source_file);
    let mut diagnostics = Vec::with_capacity(matches.len());
    for m in &matches {
        diagnostics.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_0_expresses_this_non_effectful_fold_more_directly_than_Effect_1_with_Effect_succeed_handlers_effect_matchEffectToMatch,
            Vec::new(),
            vec![m.replacement_name.clone(), m.match_effect_name.clone()],
        ));
    }
    diagnostics
}

#[derive(Clone, Debug)]
pub struct MatchEffectToMatchMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub callee_node: Node,
    pub callee_name_node: Node,
    pub match_effect_name: String,
    pub replacement_name: String,
    pub handler_results: [Node; 2],
    pub succeed_arguments: [Node; 2],
}

// Go: rules/match_effect_to_match.go AnalyzeMatchEffectToMatch
pub fn analyze_match_effect_to_match(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<MatchEffectToMatchMatch> {
    if sf.is_nil() {
        return Vec::new();
    }
    let mut matches = Vec::new();
    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        for transformation in &flow.transformations {
            if transformation.args.len() != 1 || transformation.callee.is_nil() {
                continue;
            }
            let (match_effect_name, replacement_name) = if tp
                .is_node_reference_to_effect_module_api(transformation.callee, "matchEffect")
            {
                ("matchEffect", "match")
            } else if tp
                .is_node_reference_to_effect_module_api(transformation.callee, "matchCauseEffect")
            {
                ("matchCauseEffect", "matchCause")
            } else {
                continue;
            };

            let on_failure =
                object_literal_property_initializer(transformation.args[0], "onFailure");
            let on_success =
                object_literal_property_initializer(transformation.args[0], "onSuccess");
            if on_failure.is_nil() || on_success.is_nil() {
                continue;
            }
            let (failure_result, failure_argument, ok) =
                match_effect_constructor_handler(tp, on_failure, "succeed");
            if !ok {
                continue;
            }
            let (success_result, success_argument, ok) =
                match_effect_constructor_handler(tp, on_success, "succeed");
            if !ok {
                continue;
            }
            let mut callee_name = Node::NIL;
            if transformation.callee.kind() == SyntaxKind::PropertyAccessExpression {
                callee_name = transformation.callee.name();
            }
            matches.push(MatchEffectToMatchMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, transformation.callee),
                callee_node: transformation.callee,
                callee_name_node: callee_name,
                match_effect_name: match_effect_name.to_string(),
                replacement_name: replacement_name.to_string(),
                handler_results: [failure_result, success_result],
                succeed_arguments: [failure_argument, success_argument],
            });
        }
    }
    matches
}

// Go: rules/match_effect_to_match.go matchEffectConstructorHandler
/// The handler's result expression and the argument of its trailing
/// `Effect.<constructorName>` step, with `ok` false when the handler has
/// another shape.
pub fn match_effect_constructor_handler(
    tp: &mut TypeParser<'_>,
    node: Node,
    constructor_name: &str,
) -> (Node, Node, bool) {
    let Some(lazy) = parse_lazy_expression(node, LazyExpressionFlags::NONE) else {
        return (Node::NIL, Node::NIL, false);
    };
    if lazy.expression.is_nil() {
        return (Node::NIL, Node::NIL, false);
    }
    let Some(flow) = tp.longest_piping_flow_at(lazy.expression, false) else {
        return (Node::NIL, Node::NIL, false);
    };
    if flow.transformations.is_empty() {
        return (Node::NIL, Node::NIL, false);
    }
    let last = flow.transformations.len() - 1;
    let transformation = &flow.transformations[last];
    if !tp.is_node_reference_to_effect_module_api(transformation.callee, constructor_name) {
        return (Node::NIL, Node::NIL, false);
    }
    let argument = flow.transformation_input_node(last as i32);
    if argument.is_nil() {
        return (Node::NIL, Node::NIL, false);
    }
    (lazy.expression, argument, true)
}
