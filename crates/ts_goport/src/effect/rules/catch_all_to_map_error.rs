//! Port of Effect-TS/tsgo `internal/rules/catch_all_to_map_error.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// CatchAllToMapError suggests using Effect.mapError instead of Effect.catch + Effect.fail.
// Go: rules/catch_all_to_map_error.go CatchAllToMapError
pub static CATCH_ALL_TO_MAP_ERROR: Rule = Rule {
    name: "catchAllToMapError",
    group: "style",
    description: "Suggests using Effect.mapError instead of Effect.catch + Effect.fail",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377010],
    run: run_catch_all_to_map_error,
};

fn run_catch_all_to_map_error(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_catch_all_to_map_error(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_mapError_expresses_the_same_error_type_transformation_more_directly_than_Effect_0_followed_by_Effect_fail_effect_catchAllToMapError,
            Vec::new(),
            vec![m.catch_method_name.clone()],
        ));
    }
    diags
}

/// CatchAllToMapErrorMatch holds the AST nodes needed by both the diagnostic rule
/// and the quick-fix for the catchAllToMapError pattern.
// Go: rules/catch_all_to_map_error.go CatchAllToMapErrorMatch
#[derive(Clone, Debug)]
pub struct CatchAllToMapErrorMatch {
    /// The source file of the match
    pub source_file: Node,
    /// The pre-computed error range for this match
    pub location: TextRange,
    /// The Effect.catch callee node (for diagnostic location)
    pub callee: Node,
    /// The "catch" name node within the PropertyAccessExpression (for text replacement)
    pub callee_name_node: Node,
    /// The catch variant name (e.g. "catch" or "catchAll")
    pub catch_method_name: String,
    /// The Effect.fail(arg) call expression node (for replacement range)
    pub fail_call_expression: Node,
    /// The first argument to Effect.fail (the replacement text)
    pub fail_argument: Node,
}

/// AnalyzeCatchAllToMapError finds all Effect.catch callbacks that simply wrap the
/// error with Effect.fail, which can be simplified to Effect.mapError.
// Go: rules/catch_all_to_map_error.go AnalyzeCatchAllToMapError
pub fn analyze_catch_all_to_map_error(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<CatchAllToMapErrorMatch> {
    let mut matches: Vec<CatchAllToMapErrorMatch> = Vec::new();

    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        for transformation in &flow.transformations {
            if !tp.is_node_reference_to_effect_module_api(transformation.callee, "catch")
                && !tp.is_node_reference_to_effect_module_api(transformation.callee, "catchAll")
            {
                continue;
            }

            if transformation.args.is_empty() {
                continue;
            }
            let callback = transformation.args[0];

            let Some(lazy) = parse_lazy_expression(callback, LazyExpressionFlags::NONE) else {
                continue;
            };

            let expr = lazy.expression;
            if expr.is_nil() || expr.kind() != SyntaxKind::CallExpression {
                continue;
            }
            let call = expr;
            if call.is_nil() || call.expression().is_nil() {
                continue;
            }
            if call.argument_list().is_nil() || call.arguments().is_empty() {
                continue;
            }

            if !tp.is_node_reference_to_effect_module_api(call.expression(), "fail") {
                continue;
            }

            // Extract the "catch" name node from the PropertyAccessExpression callee
            let mut callee_name_node = Node::NIL;
            let mut catch_method_name = "catch".to_string();
            let callee = transformation.callee;
            if callee.kind() == SyntaxKind::PropertyAccessExpression {
                let prop = callee;
                if prop.is_some() && prop.name().is_some() {
                    callee_name_node = prop.name();
                    catch_method_name = prop.name().text().to_string();
                }
            }

            matches.push(CatchAllToMapErrorMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, transformation.callee),
                callee: transformation.callee,
                callee_name_node,
                catch_method_name,
                fail_call_expression: expr,
                fail_argument: call.arguments().get(0),
            });
        }
    }

    matches
}
