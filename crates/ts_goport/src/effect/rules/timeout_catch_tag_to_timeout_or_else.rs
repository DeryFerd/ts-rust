//! Port of Effect-TS/tsgo `internal/rules/timeout_catch_tag_to_timeout_or_else.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

pub static TIMEOUT_CATCH_TAG_TO_TIMEOUT_OR_ELSE: Rule = Rule {
    name: "timeoutCatchTagToTimeoutOrElse",
    group: "style",
    description: "Suggests dedicated timeout combinators instead of catching TimeoutError immediately after Effect.timeout",
    default_severity: Severity::Suggestion,
    supported_effect: &["v4"],
    codes: &[377127],
    run: run_timeout_catch_tag_to_timeout_or_else,
};

fn run_timeout_catch_tag_to_timeout_or_else(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for m in analyze_timeout_catch_tag_to_timeout_or_else(ctx.tp, ctx.source_file) {
        diagnostics.push(ctx.new_diagnostic(
            ctx.source_file,
            m.location,
            diag::Use_Effect_0_to_handle_this_timeout_directly_effect_timeoutCatchTagToTimeoutOrElse,
            Vec::new(),
            args![m.replacement_name],
        ));
    }
    diagnostics
}

pub struct TimeoutCatchTagToTimeoutOrElseMatch {
    pub flow: Rc<PipingFlow>,
    pub start: i32,
    pub end: i32,
    pub location: TextRange,
    pub replacement_name: String,
    pub effect_module: Node,
    pub duration: Node,
    pub handler: Node,
}

// Go: rules/timeout_catch_tag_to_timeout_or_else.go AnalyzeTimeoutCatchTagToTimeoutOrElse
pub fn analyze_timeout_catch_tag_to_timeout_or_else(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<TimeoutCatchTagToTimeoutOrElseMatch> {
    if sf.is_nil() || tp.supported_effect_version() != EffectMajorVersion::V4 {
        return Vec::new();
    }

    let mut matches = Vec::new();
    // Check both alternatives in one pass: collecting and sorting matches per
    // pattern adds work and allocations to this frequently run analysis.
    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        let mut i = 0;
        while i + 1 < flow.transformations.len() {
            let timeout = &flow.transformations[i];
            if timeout.args.len() != 1
                || !tp.is_node_reference_to_effect_module_api(timeout.callee, "timeout")
            {
                i += 1;
                continue;
            }
            let mut end = i + 1;
            let option = timeout_as_some(tp, &flow.transformations[end]);
            if option {
                end += 1;
            }
            if end >= flow.transformations.len() {
                i += 1;
                continue;
            }
            let catch = &flow.transformations[end];
            if catch.args.len() != 2
                || !tp.is_node_reference_to_effect_module_api(catch.callee, "catchTag")
            {
                i += 1;
                continue;
            }
            let tag = skip_parentheses(catch.args[0]);
            if tag.kind() != SyntaxKind::StringLiteral || tag.text() != "TimeoutError" {
                i += 1;
                continue;
            }
            let handler = skip_parentheses(catch.args[1]);
            if !timeout_ignores_error(tp, handler) {
                i += 1;
                continue;
            }
            if option && !timeout_returns_none(tp, handler) {
                i += 1;
                continue;
            }
            let input_type = flow.transformation_input_type(i as i32);
            let input = tp.strict_effect_type(input_type);
            let Some(input) = input else {
                i += 1;
                continue;
            };
            if !timeout_error_excluded(tp, input.e) {
                i += 1;
                continue;
            }
            let mut has_type_args = false;
            for j in i..=end {
                has_type_args = has_type_args
                    || super::catch_die_to_or_die::catch_die_has_type_arguments(Some(
                        &flow.transformations[j],
                    ));
            }
            if has_type_args {
                i += 1;
                continue;
            }
            let mut name = "timeoutOrElse";
            if option {
                name = "timeoutOption";
            }
            let mut module = Node::NIL;
            if catch.callee.kind() == SyntaxKind::PropertyAccessExpression {
                module = catch.callee.expression();
            }
            matches.push(TimeoutCatchTagToTimeoutOrElseMatch {
                flow: flow.clone(),
                start: i as i32,
                end: end as i32,
                location: get_error_range_for_node(sf, catch.callee),
                replacement_name: name.to_string(),
                effect_module: module,
                duration: timeout.args[0],
                handler: catch.args[1],
            });
            i += 1;
        }
    }
    matches
}

// Go: rules/timeout_catch_tag_to_timeout_or_else.go timeoutAsSome
fn timeout_as_some(tp: &mut TypeParser<'_>, step: &PipingFlowTransformation) -> bool {
    step.args.is_empty() && tp.is_node_reference_to_effect_module_api(step.callee, "asSome")
        || step.args.len() == 1
            && tp.is_node_reference_to_effect_module_api(step.callee, "map")
            && tp.is_node_reference_to_effect_option_module_api(step.args[0], "some")
}

// Go: rules/timeout_catch_tag_to_timeout_or_else.go timeoutReturnsNone
fn timeout_returns_none(tp: &mut TypeParser<'_>, handler: Node) -> bool {
    let Some(lazy) = parse_lazy_expression(handler, LazyExpressionFlags::NONE) else {
        return false;
    };
    let flow = tp.longest_piping_flow_at(lazy.expression, false);
    // Go: MatchesExactly on a nil *PipingFlow returns false.
    let Some(flow) = flow else {
        return false;
    };
    flow.matches_exactly(
        tp,
        &mut |tp: &mut TypeParser<'_>, subject: &PipingFlowSubject| {
            tp.is_node_reference_to_effect_module_api(subject.node, "succeedNone")
        },
        &mut [],
    ) || flow.matches_exactly(
        tp,
        &mut |tp: &mut TypeParser<'_>, subject: &PipingFlowSubject| {
            super::prefer_succeed_some_or_none::is_option_none_call(tp, subject.node)
        },
        &mut [
            &mut |tp: &mut TypeParser<'_>, step: &PipingFlowTransformation| {
                step.args.is_empty()
                    && (step.type_arguments.is_nil() || step.type_arguments.nodes().is_empty())
                    && tp.is_node_reference_to_effect_module_api(step.callee, "succeed")
            },
        ],
    )
}

// Fail closed for unknown, generic, or broadly tagged errors: catchTag matches
// structurally by tag, so checking only the canonical TimeoutError is unsafe.
// Go: rules/timeout_catch_tag_to_timeout_or_else.go timeoutErrorExcluded
fn timeout_error_excluded(tp: &mut TypeParser<'_>, error_type: TypeId) -> bool {
    if error_type.is_nil() {
        return false;
    }
    if tp.checker.ty(error_type).flags.intersects(TypeFlags::NEVER) {
        return true;
    }
    for member in tp.unroll_union_members(error_type) {
        let tag = tp
            .checker
            .get_type_of_property_of_type_exported(member, "_tag");
        if tag.is_nil() {
            return false;
        }
        for value in tp.unroll_union_members(tag) {
            if !tp
                .checker
                .ty(value)
                .flags
                .intersects(TypeFlags::STRING_LITERAL)
            {
                return false;
            }
            match tp.checker.ty(value).as_literal_type().value() {
                Some(LiteralValue::String(text)) if text != "TimeoutError" => {}
                _ => return false,
            }
        }
    }
    true
}

// Restrict callbacks to arrows so the caught error cannot be observed through
// a function's arguments object. An unused plain parameter can be removed.
// Go: rules/timeout_catch_tag_to_timeout_or_else.go timeoutIgnoresError
fn timeout_ignores_error(tp: &mut TypeParser<'_>, handler: Node) -> bool {
    if handler.is_nil()
        || handler.kind() != SyntaxKind::ArrowFunction
        || get_combined_modifier_flags(handler).intersects(ModifierFlags::ASYNC)
    {
        return false;
    }
    let type_params = get_function_like_type_parameters(handler);
    if type_params.is_some() && !type_params.nodes().is_empty() {
        return false;
    }
    let params = get_function_like_parameters(handler);
    if params.is_nil() || params.nodes().is_empty() {
        return true;
    }
    if params.nodes().len() != 1 {
        return false;
    }
    let parameter = params.nodes().get(0);
    if parameter.is_nil()
        || parameter.name().kind() != SyntaxKind::Identifier
        || parameter.initializer().is_some()
        || parameter.dot_dot_dot_token().is_some()
    {
        return false;
    }
    let symbol = tp.get_symbol_at_location(parameter.name());
    if symbol.is_nil() {
        return false;
    }
    fn uses_parameter(tp: &mut TypeParser<'_>, symbol: SymbolId, node: Node) -> bool {
        if node.kind() == SyntaxKind::ShorthandPropertyAssignment
            && tp.checker.get_shorthand_assignment_value_symbol(node) == symbol
        {
            return true;
        }
        if node.kind() == SyntaxKind::Identifier && tp.get_symbol_at_location(node) == symbol {
            return true;
        }
        node.for_each_child(|child| uses_parameter(tp, symbol, child))
    }
    !uses_parameter(tp, symbol, handler.body())
        && (handler.type_().is_nil() || !uses_parameter(tp, symbol, handler.type_()))
}
