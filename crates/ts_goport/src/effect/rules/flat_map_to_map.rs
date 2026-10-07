// Go: internal/rules/flat_map_to_map.go

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// FlatMapToMap suggests using Effect.map when an Effect.flatMap callback only
/// wraps its result with Effect.succeed.
pub static FLAT_MAP_TO_MAP: Rule = Rule {
    name: "flatMapToMap",
    group: "style",
    description: "Suggests using Effect.map instead of Effect.flatMap when the callback only wraps its result with Effect.succeed",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377100],
    run: run_flat_map_to_map,
};

fn run_flat_map_to_map(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_flat_map_to_map(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_map_expresses_this_success_value_transformation_more_directly_than_Effect_flatMap_followed_by_Effect_succeed_effect_flatMapToMap,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

/// FlatMapToMapMatch holds the AST nodes needed by the diagnostic and quick fix.
#[derive(Clone, Debug)]
pub struct FlatMapToMapMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub callee: Node,
    pub callee_name_node: Node,
    pub succeed_call_expression: Node,
    pub succeed_argument: Node,
}

// Go: rules/flat_map_to_map.go AnalyzeFlatMapToMap
/// AnalyzeFlatMapToMap finds piping transformations whose Effect.flatMap
/// callback consists solely of an Effect.succeed call.
pub fn analyze_flat_map_to_map(tp: &mut TypeParser<'_>, sf: Node) -> Vec<FlatMapToMapMatch> {
    let mut matches = Vec::new();

    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        for transformation in &flow.transformations {
            let callee = transformation.callee;
            let args = &transformation.args;

            if args.is_empty() || callee.is_nil() {
                continue;
            }
            if !tp.is_node_reference_to_effect_module_api(callee, "flatMap") {
                continue;
            }

            let Some(callback) = parse_lazy_expression(args[0], LazyExpressionFlags::NONE) else {
                continue;
            };
            if callback.expression.is_nil()
                || callback.expression.kind() != SyntaxKind::CallExpression
            {
                continue;
            }
            let succeed_call = callback.expression;
            if succeed_call.is_nil()
                || succeed_call.expression().is_nil()
                || succeed_call.argument_list().is_nil()
                || succeed_call.arguments().len() != 1
            {
                continue;
            }
            if !tp.is_node_reference_to_effect_module_api(succeed_call.expression(), "succeed") {
                continue;
            }

            let mut callee_name = Node::NIL;
            if callee.kind() == SyntaxKind::PropertyAccessExpression {
                callee_name = callee.name();
            }

            matches.push(FlatMapToMapMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, callee),
                callee,
                callee_name_node: callee_name,
                succeed_call_expression: callback.expression,
                succeed_argument: succeed_call.arguments().get(0),
            });
        }
    }

    matches
}
