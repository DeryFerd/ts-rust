//! Port of Effect-TS/tsgo `internal/rules/flat_map_conditional_to_filter_or_fail.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// FlatMapConditionalToFilterOrFail suggests Effect.filterOrFail or
/// Effect.filterOrElse when a flatMap callback implements an identity filter.
// Go: rules/flat_map_conditional_to_filter_or_fail.go FlatMapConditionalToFilterOrFail
pub static FLAT_MAP_CONDITIONAL_TO_FILTER_OR_FAIL: Rule = Rule {
    name: "flatMapConditionalToFilterOrFail",
    group: "style",
    description: "Suggests Effect.filterOrFail or Effect.filterOrElse when Effect.flatMap conditionally passes its input through with Effect.succeed",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377120],
    run: run_flat_map_conditional_to_filter_or_fail,
};

fn run_flat_map_conditional_to_filter_or_fail(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let sf = ctx.source_file;
    let matches = analyze_flat_map_conditional_to_filter_or_fail(ctx.tp, sf);
    let mut diagnostics = Vec::with_capacity(matches.len());
    for m in &matches {
        diagnostics.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_0_expresses_this_conditional_validation_more_directly_than_Effect_flatMap_with_an_identity_Effect_succeed_branch_effect_flatMapConditionalToFilterOrFail,
            Vec::new(),
            vec![m.preferred_method_name.clone()],
        ));
    }
    diagnostics
}

/// FlatMapConditionalToFilterOrFailMatch holds the source evidence needed by
/// the diagnostic and its quick fix.
// PORT: Go `Transformation` is a pointer into the flow; the port keeps a copy.
#[derive(Clone, Debug)]
pub struct FlatMapConditionalToFilterOrFailMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub transformation: PipingFlowTransformation,
    pub effect_module_node: Node,
    pub parameter_node: Node,
    pub predicate_node: Node,
    pub fallback_node: Node,
    pub preferred_method_name: String,
    pub negate_predicate: bool,
    pub can_fix: bool,
}

/// AnalyzeFlatMapConditionalToFilterOrFail finds flatMap transformations whose
/// callback is a two-way conditional with one identity Effect.succeed branch.
// Go: rules/flat_map_conditional_to_filter_or_fail.go AnalyzeFlatMapConditionalToFilterOrFail
pub fn analyze_flat_map_conditional_to_filter_or_fail(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<FlatMapConditionalToFilterOrFailMatch> {
    if sf.is_nil() {
        return Vec::new();
    }

    let mut matches = Vec::new();
    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        for index in 0..flow.transformations.len() {
            let transformation = &flow.transformations[index];
            let callee = transformation.callee;
            let args = &transformation.args;
            if callee.is_nil()
                || args.len() != 1
                || !tp.is_node_reference_to_effect_module_api(callee, "flatMap")
            {
                continue;
            }
            let Some(parsed) = parse_returning_dispatch(args[0]) else {
                continue;
            };
            if parsed.params.len() != 1
                || parsed.dispatch.branches.len() != 1
                || parsed.dispatch.fallback.is_nil()
                || parsed.dispatch.branches[0].condition.kind != DispatchConditionKind::Predicate
                || !super::option_match_to_from_option::is_synchronous_function(parsed.node)
            {
                continue;
            }

            let parameter = parsed.params[0];
            if parameter.is_nil()
                || parameter.name().is_nil()
                || parameter.name().kind() != SyntaxKind::Identifier
            {
                continue;
            }
            let declaration = parameter;
            if declaration.is_nil()
                || declaration.dot_dot_dot_token().is_some()
                || declaration.initializer().is_some()
            {
                continue;
            }
            let parameter_symbol = tp.get_symbol_at_location(parameter.name());
            if parameter_symbol.is_nil() || tp.checker.is_symbol_assigned(parameter_symbol) {
                continue;
            }

            let branch = parsed.dispatch.branches[0];
            let branch_identity = is_identity_succeed(tp, branch.result, parameter_symbol);
            let fallback_identity =
                is_identity_succeed(tp, parsed.dispatch.fallback, parameter_symbol);
            if branch_identity == fallback_identity {
                continue;
            }

            let mut fallback = branch.result;
            let mut negate_predicate = true;
            if branch_identity {
                fallback = parsed.dispatch.fallback;
                negate_predicate = false;
            }

            let mut preferred_method = "filterOrElse";
            let mut fallback_node = fallback;
            let failure = effect_fail_argument(tp, fallback);
            if failure.is_some() {
                preferred_method = "filterOrFail";
                fallback_node = failure;
            } else if !super::catch_tag_to_catch_reason::is_effect_expression(tp, fallback) {
                continue;
            }

            let effect_module =
                super::option_match_to_from_option::effect_module_expression(callee);
            let m = FlatMapConditionalToFilterOrFailMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, callee),
                transformation: transformation.clone(),
                effect_module_node: effect_module,
                parameter_node: parameter,
                predicate_node: branch.condition.subject,
                fallback_node,
                preferred_method_name: preferred_method.to_string(),
                negate_predicate,
                can_fix: true,
            };

            matches.push(m);
        }
    }
    matches
}

// Go: rules/flat_map_conditional_to_filter_or_fail.go isIdentitySucceed
fn is_identity_succeed(
    tp: &mut TypeParser<'_>,
    expression: Node,
    parameter_symbol: SymbolId,
) -> bool {
    let expression = skip_parentheses(expression);
    if expression.is_nil() || expression.kind() != SyntaxKind::CallExpression {
        return false;
    }
    let call = expression;
    if call.is_nil()
        || call.expression().is_nil()
        || call.argument_list().is_nil()
        || call.arguments().len() != 1
        || call.type_argument_list().is_some() && !call.type_arguments().is_empty()
        || !tp.is_node_reference_to_effect_module_api(call.expression(), "succeed")
    {
        return false;
    }
    let argument = skip_parentheses(call.arguments().get(0));
    if argument.is_nil() || argument.kind() != SyntaxKind::Identifier {
        return false;
    }
    let actual_symbol = tp.get_symbol_at_location(argument);
    actual_symbol.is_some()
        && tp
            .checker
            .get_symbol_if_same_reference(actual_symbol, parameter_symbol)
            .is_some()
}

// Go: rules/flat_map_conditional_to_filter_or_fail.go effectFailArgument
fn effect_fail_argument(tp: &mut TypeParser<'_>, expression: Node) -> Node {
    let expression = skip_parentheses(expression);
    if expression.is_nil() || expression.kind() != SyntaxKind::CallExpression {
        return Node::NIL;
    }
    let call = expression;
    if call.is_nil()
        || call.expression().is_nil()
        || call.argument_list().is_nil()
        || call.arguments().len() != 1
        || call.type_argument_list().is_some() && !call.type_arguments().is_empty()
        || !tp.is_node_reference_to_effect_module_api(call.expression(), "fail")
    {
        return Node::NIL;
    }
    call.arguments().get(0)
}
