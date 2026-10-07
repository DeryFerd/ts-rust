//! Port of Effect-TS/tsgo `internal/rules/option_match_to_from_option.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// OptionMatchToFromOption suggests Effect.fromOption when Option.match or an
/// Option tag conditional only lifts Some with Effect.succeed and None with
/// Effect.fail.
pub static OPTION_MATCH_TO_FROM_OPTION: Rule = Rule {
    name: "optionMatchToFromOption",
    group: "style",
    description: "Suggests Effect.fromOption when Option.match or an Option tag conditional only converts Some to Effect.succeed and None to Effect.fail",
    default_severity: Severity::Suggestion,
    supported_effect: &["v4"],
    codes: &[377118],
    run: run_option_match_to_from_option,
};

fn run_option_match_to_from_option(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_option_match_to_from_option(ctx.tp, ctx.source_file);
    let mut diagnostics = Vec::with_capacity(matches.len());
    for m in matches {
        diagnostics.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_fromOption_expresses_this_Option_to_Effect_conversion_more_directly_than_Option_match_or_an_Option_tag_conditional_effect_optionMatchToFromOption,
            Vec::new(),
            Vec::new(),
        ));
    }
    diagnostics
}

/// OptionMatchToFromOptionMatch holds the nodes needed by the diagnostic and
/// quick fix.
// PORT: Go `Transformation` is a `*PipingFlowTransformation` into the flow,
// nil for conditional matches; the port keeps a copy.
#[derive(Default)]
pub struct OptionMatchToFromOptionMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub transformation: Option<PipingFlowTransformation>,
    pub replacement_node: Node,
    pub effect_module_node: Node,
    pub option_node: Node,
    pub failure_node: Node,
    pub default_failure: bool,
    pub can_fix: bool,
}

/// AnalyzeOptionMatchToFromOption finds Option.match and Option result
/// dispatches that are equivalent to Effect.fromOption.
// Go: rules/option_match_to_from_option.go AnalyzeOptionMatchToFromOption
pub fn analyze_option_match_to_from_option(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<OptionMatchToFromOptionMatch> {
    if sf.is_nil() || tp.supported_effect_version() != EffectMajorVersion::V4 {
        return Vec::new();
    }

    let mut matches = analyze_option_match_calls(tp, sf);
    matches.extend(analyze_option_conditionals(tp, sf));
    matches
}

// Go: rules/option_match_to_from_option.go analyzeOptionMatchCalls
fn analyze_option_match_calls(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<OptionMatchToFromOptionMatch> {
    let mut matches = Vec::new();

    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        for transformation in &flow.transformations {
            let callee = transformation.callee;
            let args = &transformation.args;
            if args.len() != 1 || !tp.is_node_reference_to_effect_option_module_api(callee, "match")
            {
                continue;
            }

            let (failure, effect_module, can_fix, ok) = analyze_option_match_handlers(tp, args[0]);
            if !ok {
                continue;
            }

            let m = OptionMatchToFromOptionMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, callee),
                transformation: Some(transformation.clone()),
                effect_module_node: effect_module,
                failure_node: failure,
                default_failure: is_default_no_such_element_error(tp, failure),
                can_fix,
                ..Default::default()
            };

            match transformation.kind {
                TransformationKind::Pipe
                | TransformationKind::Pipeable
                | TransformationKind::DataFirst
                | TransformationKind::DataLast
                | TransformationKind::Call => {}
                _ => continue,
            }

            matches.push(m);
        }
    }

    matches
}

// Go: rules/option_match_to_from_option.go analyzeOptionMatchHandlers
fn analyze_option_match_handlers(tp: &mut TypeParser<'_>, node: Node) -> (Node, Node, bool, bool) {
    let node = skip_parentheses(node);
    if node.is_nil() || node.kind() != SyntaxKind::ObjectLiteralExpression {
        return (Node::NIL, Node::NIL, false, false);
    }
    let object = node;
    if object.property_list().is_nil() || object.property_list().nodes().len() != 2 {
        return (Node::NIL, Node::NIL, false, false);
    }

    let mut on_none = Node::NIL;
    let mut on_some = Node::NIL;
    for property_node in object.property_list().nodes().iter() {
        if property_node.is_nil() || property_node.kind() != SyntaxKind::PropertyAssignment {
            return (Node::NIL, Node::NIL, false, false);
        }
        let property = property_node;
        if property.name().is_nil()
            || property.name().kind() != SyntaxKind::Identifier
            || property.initializer().is_nil()
        {
            return (Node::NIL, Node::NIL, false, false);
        }
        match get_text_of_node(property.name()).as_str() {
            "onNone" => {
                if on_none.is_some() {
                    return (Node::NIL, Node::NIL, false, false);
                }
                on_none = property.initializer();
            }
            "onSome" => {
                if on_some.is_some() {
                    return (Node::NIL, Node::NIL, false, false);
                }
                on_some = property.initializer();
            }
            _ => return (Node::NIL, Node::NIL, false, false),
        }
    }

    let (succeed_module, ok) = analyze_effect_succeed_handler(tp, on_some);
    if !ok {
        return (Node::NIL, Node::NIL, false, false);
    }
    let (failure, fail_module, can_fix, ok) = analyze_effect_fail_handler(tp, on_none);
    if !ok {
        return (Node::NIL, Node::NIL, false, false);
    }
    if succeed_module.is_some() {
        return (failure, succeed_module, can_fix, true);
    }
    (failure, fail_module, can_fix, true)
}

// Go: rules/option_match_to_from_option.go analyzeEffectSucceedHandler
fn analyze_effect_succeed_handler(tp: &mut TypeParser<'_>, node: Node) -> (Node, bool) {
    let (target, type_arguments, _) = tp.unwrap_identity_forwarder(node);
    if type_arguments.is_some() && !type_arguments.nodes().is_empty()
        || !tp.is_node_reference_to_effect_module_api(target, "succeed")
    {
        return (Node::NIL, false);
    }
    (effect_module_expression(target), true)
}

// Go: rules/option_match_to_from_option.go analyzeEffectFailHandler
fn analyze_effect_fail_handler(tp: &mut TypeParser<'_>, node: Node) -> (Node, Node, bool, bool) {
    let Some(lazy) = parse_lazy_expression(node, LazyExpressionFlags::THUNK) else {
        return (Node::NIL, Node::NIL, false, false);
    };
    let expression = skip_parentheses(lazy.expression);
    if expression.is_nil() || expression.kind() != SyntaxKind::CallExpression {
        return (Node::NIL, Node::NIL, false, false);
    }
    let call = expression;
    if call.expression().is_nil()
        || call.argument_list().is_nil()
        || call.argument_list().nodes().len() != 1
        || call.type_argument_list().is_some() && !call.type_argument_list().nodes().is_empty()
        || !tp.is_node_reference_to_effect_module_api(call.expression(), "fail")
    {
        return (Node::NIL, Node::NIL, false, false);
    }
    (
        call.argument_list().nodes().get(0),
        effect_module_expression(call.expression()),
        lazy.node.kind() == SyntaxKind::ArrowFunction,
        true,
    )
}

// Go: rules/option_match_to_from_option.go isSynchronousFunction
pub fn is_synchronous_function(node: Node) -> bool {
    if node.is_nil() || get_combined_modifier_flags(node).intersects(ModifierFlags::ASYNC) {
        return false;
    }
    if node.kind() == SyntaxKind::FunctionExpression {
        let function = node;
        return function.asterisk_token().is_nil();
    }
    node.kind() == SyntaxKind::ArrowFunction
}

// Go: rules/option_match_to_from_option.go effectModuleExpression
pub fn effect_module_expression(node: Node) -> Node {
    let node = skip_parentheses(node);
    if node.is_nil() || node.kind() != SyntaxKind::PropertyAccessExpression {
        return Node::NIL;
    }
    let property = node;
    if property.question_dot_token().is_some() {
        return Node::NIL;
    }
    let receiver = skip_parentheses(property.expression());
    if receiver.is_nil() || receiver.kind() != SyntaxKind::Identifier {
        return Node::NIL;
    }
    receiver
}

// Go: rules/option_match_to_from_option.go analyzeOptionConditionals
fn analyze_option_conditionals(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<OptionMatchToFromOptionMatch> {
    let mut matches = Vec::new();
    fn visit(
        tp: &mut TypeParser<'_>,
        sf: Node,
        node: Node,
        matches: &mut Vec<OptionMatchToFromOptionMatch>,
    ) -> bool {
        if node.is_nil() {
            return false;
        }
        if node.kind() == SyntaxKind::ConditionalExpression {
            let (m, ok) = analyze_option_conditional(tp, sf, node);
            if ok {
                matches.push(m);
            }
        }
        node.for_each_child(|child| visit(tp, sf, child, matches));
        false
    }
    sf.for_each_child(|child| visit(tp, sf, child, &mut matches));
    matches
}

// Go: rules/option_match_to_from_option.go analyzeOptionConditional
fn analyze_option_conditional(
    tp: &mut TypeParser<'_>,
    sf: Node,
    node: Node,
) -> (OptionMatchToFromOptionMatch, bool) {
    let Some(dispatch) = parse_result_dispatch(node) else {
        return (OptionMatchToFromOptionMatch::default(), false);
    };
    if dispatch.branches.len() != 1 || dispatch.fallback.is_nil() {
        return (OptionMatchToFromOptionMatch::default(), false);
    }
    let branch = dispatch.branches[0];
    if branch.condition.kind != DispatchConditionKind::Predicate
        || branch.condition.subject.is_nil()
        || branch.condition.value.is_some()
    {
        return (OptionMatchToFromOptionMatch::default(), false);
    }

    let condition_node = skip_parentheses(branch.condition.subject);
    if condition_node.is_nil() || condition_node.kind() != SyntaxKind::CallExpression {
        return (OptionMatchToFromOptionMatch::default(), false);
    }
    let condition = condition_node;
    if condition.expression().is_nil()
        || condition.argument_list().is_nil()
        || condition.argument_list().nodes().len() != 1
        || condition.type_argument_list().is_some()
            && !condition.type_argument_list().nodes().is_empty()
    {
        return (OptionMatchToFromOptionMatch::default(), false);
    }

    let is_some =
        tp.is_node_reference_to_effect_option_module_api(condition.expression(), "isSome");
    let is_none =
        tp.is_node_reference_to_effect_option_module_api(condition.expression(), "isNone");
    if is_some == is_none {
        return (OptionMatchToFromOptionMatch::default(), false);
    }
    let option_node = skip_parentheses(condition.argument_list().nodes().get(0));
    if option_node.is_nil() || option_node.kind() != SyntaxKind::Identifier {
        return (OptionMatchToFromOptionMatch::default(), false);
    }

    let mut succeed_node = branch.result;
    let mut fail_node = dispatch.fallback;
    if is_none {
        std::mem::swap(&mut succeed_node, &mut fail_node);
    }

    let (mut effect_module, ok) = analyze_conditional_succeed(tp, option_node, succeed_node);
    if !ok {
        return (OptionMatchToFromOptionMatch::default(), false);
    }
    let (failure, fail_module, ok) = analyze_effect_fail_call(tp, fail_node);
    if !ok {
        return (OptionMatchToFromOptionMatch::default(), false);
    }
    if effect_module.is_nil() {
        effect_module = fail_module;
    }

    (
        OptionMatchToFromOptionMatch {
            source_file: sf,
            location: get_error_range_for_node(sf, condition.expression()),
            transformation: None,
            replacement_node: dispatch.node,
            effect_module_node: effect_module,
            option_node,
            failure_node: failure,
            default_failure: is_default_no_such_element_error(tp, failure),
            can_fix: true,
        },
        true,
    )
}

// Go: rules/option_match_to_from_option.go analyzeConditionalSucceed
fn analyze_conditional_succeed(
    tp: &mut TypeParser<'_>,
    option_node: Node,
    node: Node,
) -> (Node, bool) {
    let expression = skip_parentheses(node);
    if expression.is_nil() || expression.kind() != SyntaxKind::CallExpression {
        return (Node::NIL, false);
    }
    let call = expression;
    if call.expression().is_nil()
        || call.argument_list().is_nil()
        || call.argument_list().nodes().len() != 1
        || call.type_argument_list().is_some() && !call.type_argument_list().nodes().is_empty()
        || !tp.is_node_reference_to_effect_module_api(call.expression(), "succeed")
    {
        return (Node::NIL, false);
    }

    let value_node = skip_parentheses(call.argument_list().nodes().get(0));
    if value_node.is_nil() || value_node.kind() != SyntaxKind::PropertyAccessExpression {
        return (Node::NIL, false);
    }
    let value = value_node;
    if value.question_dot_token().is_some()
        || value.name().is_nil()
        || get_text_of_node(value.name()) != "value"
        || !same_identifier_reference(tp, option_node, skip_parentheses(value.expression()))
    {
        return (Node::NIL, false);
    }
    (effect_module_expression(call.expression()), true)
}

// Go: rules/option_match_to_from_option.go analyzeEffectFailCall
fn analyze_effect_fail_call(tp: &mut TypeParser<'_>, node: Node) -> (Node, Node, bool) {
    let expression = skip_parentheses(node);
    if expression.is_nil() || expression.kind() != SyntaxKind::CallExpression {
        return (Node::NIL, Node::NIL, false);
    }
    let call = expression;
    if call.expression().is_nil()
        || call.argument_list().is_nil()
        || call.argument_list().nodes().len() != 1
        || call.type_argument_list().is_some() && !call.type_argument_list().nodes().is_empty()
        || !tp.is_node_reference_to_effect_module_api(call.expression(), "fail")
    {
        return (Node::NIL, Node::NIL, false);
    }
    (
        call.argument_list().nodes().get(0),
        effect_module_expression(call.expression()),
        true,
    )
}

// Go: rules/option_match_to_from_option.go sameIdentifierReference
fn same_identifier_reference(tp: &mut TypeParser<'_>, left: Node, right: Node) -> bool {
    if left.is_nil()
        || right.is_nil()
        || left.kind() != SyntaxKind::Identifier
        || right.kind() != SyntaxKind::Identifier
    {
        return false;
    }
    let left_symbol = tp.get_symbol_at_location(left);
    let right_symbol = tp.get_symbol_at_location(right);
    left_symbol.is_some()
        && right_symbol.is_some()
        && tp
            .checker
            .get_symbol_if_same_reference(left_symbol, right_symbol)
            .is_some()
}

// Go: rules/option_match_to_from_option.go isDefaultNoSuchElementError
fn is_default_no_such_element_error(tp: &mut TypeParser<'_>, node: Node) -> bool {
    let node = skip_parentheses(node);
    if node.is_nil() || node.kind() != SyntaxKind::NewExpression {
        return false;
    }
    let expression = node;
    if expression.expression().is_nil()
        || expression.type_argument_list().is_some()
            && !expression.type_argument_list().nodes().is_empty()
        || expression.argument_list().is_some() && !expression.argument_list().nodes().is_empty()
    {
        return false;
    }
    tp.is_node_reference_to_effect_cause_module_api(expression.expression(), "NoSuchElementError")
}
