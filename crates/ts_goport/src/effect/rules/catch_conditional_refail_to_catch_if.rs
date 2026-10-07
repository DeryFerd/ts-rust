// Go: internal/rules/catch_conditional_refail_to_catch_if.go

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// CatchConditionalRefailToCatchIf detects conditional catch handlers that
/// recover in one branch and re-fail the untouched handler parameter in the
/// other branch.
pub static CATCH_CONDITIONAL_REFAIL_TO_CATCH_IF: Rule = Rule {
    name: "catchConditionalRefailToCatchIf",
    group: "style",
    description: "Suggests Effect.catchIf, Effect.catchCauseIf, or Effect.catchTag for conditional catch handlers that re-fail their untouched input",
    default_severity: Severity::Suggestion,
    supported_effect: &["v4"],
    codes: &[377116],
    run: run_catch_conditional_refail_to_catch_if,
};

fn run_catch_conditional_refail_to_catch_if(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_catch_conditional_refail_to_catch_if(ctx.tp, ctx.source_file);
    let mut diagnostics = Vec::with_capacity(matches.len());
    for m in &matches {
        diagnostics.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_2_expresses_selective_recovery_more_directly_than_Effect_0_with_a_conditional_Effect_1_passthrough_effect_catchConditionalRefailToCatchIf,
            Vec::new(),
            vec![
                m.catch_method_name.clone(),
                m.fail_method_name.clone(),
                m.preferred_method_name.clone(),
            ],
        ));
    }
    diagnostics
}

#[derive(Clone, Debug)]
pub struct CatchConditionalRefailToCatchIfMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub catch_method_name: String,
    pub fail_method_name: String,
    pub preferred_method_name: String,
}

/// Go `conditionalRefailCatchMethods`.
#[derive(Clone, Copy, Debug, Default)]
pub struct ConditionalRefailCatchMethods {
    pub catch_method_name: &'static str,
    pub fail_method_name: &'static str,
    pub preferred_method_name: &'static str,
}

// Go: rules/catch_conditional_refail_to_catch_if.go AnalyzeCatchConditionalRefailToCatchIf
/// AnalyzeCatchConditionalRefailToCatchIf finds exact Effect.catch and
/// Effect.catchCause transformations whose handler is a single two-way
/// conditional with one untouched-parameter re-fail branch.
pub fn analyze_catch_conditional_refail_to_catch_if(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<CatchConditionalRefailToCatchIfMatch> {
    if sf.is_nil() || tp.supported_effect_version() != EffectMajorVersion::V4 {
        return Vec::new();
    }

    let mut matches = Vec::new();
    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        for index in 0..flow.transformations.len() {
            let transformation = &flow.transformations[index];
            if transformation.callee.is_nil() {
                continue;
            }
            let (methods, ok) = conditional_refail_methods(tp, transformation.callee);
            if !ok || transformation.args.len() != 1 {
                continue;
            }

            let mut input_type = flow.subject.out_type;
            if index > 0 {
                input_type = flow.transformations[index - 1].out_type;
            }
            if tp.strict_effect_type(input_type).is_none() {
                continue;
            }

            let (preferred_method_name, ok) =
                analyze_conditional_refail_handler(tp, transformation.args[0], methods);
            if !ok {
                continue;
            }

            matches.push(CatchConditionalRefailToCatchIfMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, transformation.callee),
                catch_method_name: methods.catch_method_name.to_string(),
                fail_method_name: methods.fail_method_name.to_string(),
                preferred_method_name,
            });
        }
    }

    matches
}

// Go: rules/catch_conditional_refail_to_catch_if.go conditionalRefailMethods
fn conditional_refail_methods(
    tp: &mut TypeParser<'_>,
    callee: Node,
) -> (ConditionalRefailCatchMethods, bool) {
    if tp.is_node_reference_to_effect_module_api(callee, "catch") {
        (
            ConditionalRefailCatchMethods {
                catch_method_name: "catch",
                fail_method_name: "fail",
                preferred_method_name: "catchIf",
            },
            true,
        )
    } else if tp.is_node_reference_to_effect_module_api(callee, "catchCause") {
        (
            ConditionalRefailCatchMethods {
                catch_method_name: "catchCause",
                fail_method_name: "failCause",
                preferred_method_name: "catchCauseIf",
            },
            true,
        )
    } else {
        (ConditionalRefailCatchMethods::default(), false)
    }
}

// Go: rules/catch_conditional_refail_to_catch_if.go analyzeConditionalRefailHandler
fn analyze_conditional_refail_handler(
    tp: &mut TypeParser<'_>,
    handler_node: Node,
    methods: ConditionalRefailCatchMethods,
) -> (String, bool) {
    // PORT: Go also checks `dispatch.Dispatch == nil`; the port's
    // `ParsedReturningDispatch.dispatch` is always set.
    let Some(dispatch) = parse_returning_dispatch(handler_node) else {
        return (String::new(), false);
    };
    if dispatch.params.len() != 1
        || dispatch.dispatch.branches.len() != 1
        || dispatch.dispatch.fallback.is_nil()
    {
        return (String::new(), false);
    }
    let parameter = dispatch.params[0];
    if parameter.is_nil()
        || parameter.name().is_nil()
        || parameter.name().kind() != SyntaxKind::Identifier
    {
        return (String::new(), false);
    }
    let parameter_declaration = parameter;
    if parameter_declaration.is_nil()
        || parameter_declaration.dot_dot_dot_token().is_some()
        || parameter_declaration.initializer().is_some()
    {
        return (String::new(), false);
    }
    let parameter_symbol = tp.get_symbol_at_location(parameter.name());
    if parameter_symbol.is_nil() || tp.checker.is_symbol_assigned(parameter_symbol) {
        return (String::new(), false);
    }

    // Bare _tag dispatch is handled by catchAllTagDispatchToCatchTag. Keep the
    // generic conditional rule for inverted tag checks, which cannot be
    // represented by catchTag, and for non-tag predicates.
    let branch = dispatch.dispatch.branches[0];
    let tag_subject = dispatch.dispatch.common_tag_subject(tp);
    let (_, ok) = super::result_dispatch::result_dispatch_tag_value(branch.condition);
    if tag_subject.is_some()
        && ok
        && super::result_dispatch::is_result_dispatch_tag_reference(
            tp,
            tag_subject,
            parameter_symbol,
        )
    {
        let branch_refails = is_conditional_refail_expression(
            tp,
            branch.result,
            parameter_symbol,
            methods.fail_method_name,
        );
        let fallback_refails = is_conditional_refail_expression(
            tp,
            dispatch.dispatch.fallback,
            parameter_symbol,
            methods.fail_method_name,
        );
        if branch_refails == fallback_refails {
            return (String::new(), false);
        }
        let mut recovery = branch.result;
        if branch_refails {
            recovery = dispatch.dispatch.fallback;
        } else if methods.catch_method_name == "catch"
            && super::catch_all_tag_dispatch_to_catch_tag::is_bare_parameter_tag_reference(
                tp,
                tag_subject,
                parameter_symbol,
            )
        {
            return (String::new(), false);
        }
        if !super::catch_tag_to_catch_reason::is_effect_expression(tp, recovery) {
            return (String::new(), false);
        }
        return (methods.preferred_method_name.to_string(), true);
    }

    let condition = branch.condition.subject;
    if !is_conditional_refail_predicate(tp, condition, parameter_symbol) {
        return (String::new(), false);
    }

    let true_refails = is_conditional_refail_expression(
        tp,
        branch.result,
        parameter_symbol,
        methods.fail_method_name,
    );
    let false_refails = is_conditional_refail_expression(
        tp,
        dispatch.dispatch.fallback,
        parameter_symbol,
        methods.fail_method_name,
    );
    if true_refails == false_refails {
        return (String::new(), false);
    }

    let mut recovery = branch.result;
    if true_refails {
        recovery = dispatch.dispatch.fallback;
    }
    if !super::catch_tag_to_catch_reason::is_effect_expression(tp, recovery) {
        return (String::new(), false);
    }

    (methods.preferred_method_name.to_string(), true)
}

// Go: rules/catch_conditional_refail_to_catch_if.go isConditionalRefailExpression
fn is_conditional_refail_expression(
    tp: &mut TypeParser<'_>,
    expression: Node,
    parameter_symbol: SymbolId,
    fail_method_name: &str,
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
        || !tp.is_node_reference_to_effect_module_api(call.expression(), fail_method_name)
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

// Go: rules/catch_conditional_refail_to_catch_if.go isConditionalRefailPredicate
fn is_conditional_refail_predicate(
    tp: &mut TypeParser<'_>,
    node: Node,
    parameter_symbol: SymbolId,
) -> bool {
    let node = super::redundant_map_error::unwrap_transparent_expression(node);
    if node.is_nil() {
        return false;
    }

    match node.kind() {
        SyntaxKind::CallExpression
        | SyntaxKind::PropertyAccessExpression
        | SyntaxKind::ElementAccessExpression
        | SyntaxKind::TypeOfExpression => {
            return conditional_refail_node_contains_parameter(tp, node, parameter_symbol);
        }
        SyntaxKind::PrefixUnaryExpression => {
            let prefix = node;
            return prefix.is_some()
                && prefix.operator() == SyntaxKind::ExclamationToken
                && is_conditional_refail_predicate(tp, prefix.operand(), parameter_symbol);
        }
        SyntaxKind::BinaryExpression => {
            let binary = node;
            if binary.is_nil() || binary.operator_token().is_nil() {
                return false;
            }
            match binary.operator_token().kind() {
                SyntaxKind::AmpersandAmpersandToken | SyntaxKind::BarBarToken => {
                    return is_conditional_refail_predicate(tp, binary.left(), parameter_symbol)
                        || is_conditional_refail_predicate(tp, binary.right(), parameter_symbol);
                }
                SyntaxKind::InstanceOfKeyword => {
                    return conditional_refail_node_contains_parameter(
                        tp,
                        binary.left(),
                        parameter_symbol,
                    );
                }
                SyntaxKind::InKeyword => {
                    return conditional_refail_node_contains_parameter(
                        tp,
                        binary.right(),
                        parameter_symbol,
                    );
                }
                SyntaxKind::EqualsEqualsToken
                | SyntaxKind::EqualsEqualsEqualsToken
                | SyntaxKind::ExclamationEqualsToken
                | SyntaxKind::ExclamationEqualsEqualsToken
                | SyntaxKind::LessThanToken
                | SyntaxKind::LessThanEqualsToken
                | SyntaxKind::GreaterThanToken
                | SyntaxKind::GreaterThanEqualsToken => {
                    return conditional_refail_node_contains_parameter(tp, node, parameter_symbol);
                }
                _ => {}
            }
        }
        _ => {}
    }

    false
}

// Go: rules/catch_conditional_refail_to_catch_if.go conditionalRefailNodeContainsParameter
/// Whether `node` contains an identifier that refers to `parameter_symbol`.
pub fn conditional_refail_node_contains_parameter(
    tp: &mut TypeParser<'_>,
    node: Node,
    parameter_symbol: SymbolId,
) -> bool {
    if node.is_nil() || parameter_symbol.is_nil() {
        return false;
    }
    fn visit(
        tp: &mut TypeParser<'_>,
        parameter_symbol: SymbolId,
        found: &mut bool,
        current: Node,
    ) -> bool {
        if current.is_nil() || *found {
            return *found;
        }
        if current.kind() == SyntaxKind::Identifier {
            let actual = tp.get_symbol_at_location(current);
            if actual.is_some()
                && tp
                    .checker
                    .get_symbol_if_same_reference(actual, parameter_symbol)
                    .is_some()
            {
                *found = true;
                return true;
            }
        }
        current.for_each_child(|child| visit(tp, parameter_symbol, found, child));
        *found
    }
    let mut found = false;
    visit(tp, parameter_symbol, &mut found, node);
    found
}
