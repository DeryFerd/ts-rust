//! Port of Effect-TS/tsgo `internal/rules/effect_fn_opportunity.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// EffectFnOpportunity detects functions that can be rewritten as Effect.fn calls.
// Go: rules/effect_fn_opportunity.go EffectFnOpportunity
pub static EFFECT_FN_OPPORTUNITY: Rule = Rule {
    name: "effectFnOpportunity",
    group: "style",
    description: "Suggests using Effect.fn for functions that return an Effect",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377047],
    run: run_effect_fn_opportunity,
};

fn run_effect_fn_opportunity(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let effect_config = ctx.options;
    let matches = analyze_effect_fn_opportunity(ctx.tp, ctx.source_file);
    let mut diags = Vec::new();
    for m in &matches {
        let fix_name = first_available_fix_name(&m.result, effect_config);
        if fix_name.is_empty() {
            continue;
        }
        let expected_signature = build_expected_signature(ctx.source_file, m, fix_name);
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_expression_can_be_rewritten_in_the_reusable_function_form_0_effect_effectFnOpportunity,
            Vec::new(),
            args![expected_signature],
        ));
    }
    diags
}

/// EffectFnOpportunityMatch holds the parsed result needed by both the diagnostic rule
/// and the quick-fix for the effectFnOpportunity pattern.
// Go: rules/effect_fn_opportunity.go EffectFnOpportunityMatch
#[derive(Clone)]
pub struct EffectFnOpportunityMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub result: Rc<EffectFnOpportunityResult>,
}

/// AnalyzeEffectFnOpportunity finds all functions that can be converted to Effect.fn
/// in the given source file.
// Go: rules/effect_fn_opportunity.go AnalyzeEffectFnOpportunity
pub fn analyze_effect_fn_opportunity(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<EffectFnOpportunityMatch> {
    let mut matches = Vec::new();

    // PORT: Go's recursive `walk` closure.
    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        matches: &mut Vec<EffectFnOpportunityMatch>,
        n: Node,
    ) -> bool {
        if n.is_nil() {
            return false;
        }

        if let Some(result) = tp.parse_effect_fn_opportunity(n) {
            // Report on the name identifier if available, otherwise the function node
            let mut report_node = result.name_identifier;
            if report_node.is_nil() {
                report_node = result.target_node;
            }
            matches.push(EffectFnOpportunityMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, report_node),
                result,
            });
        }

        n.for_each_child(|child| walk(tp, sf, matches, child));
        false
    }

    walk(tp, sf, &mut matches, sf);

    matches
}

/// firstAvailableFixName determines which fix variant would be first (highest priority)
/// for the given match, matching the reference implementation's fix ordering.
/// Returns empty string when no fix variant passes the config filter.
// Go: rules/effect_fn_opportunity.go firstAvailableFixName
fn first_available_fix_name(
    result: &EffectFnOpportunityResult,
    effect_config: &ResolvedEffectPluginOptions,
) -> &'static str {
    // Priority order matches upstream: withSpan > untraced > noSpan > spanInferred > spanSuggested
    if effect_config.effect_fn_includes(EFFECT_FN_SPAN)
        && result.explicit_trace_expression.is_some()
    {
        return "effectFnOpportunity_toEffectFnWithSpan";
    }
    if effect_config.effect_fn_includes(EFFECT_FN_UNTRACED) && result.generator_function.is_some() {
        return "effectFnOpportunity_toEffectFnUntraced";
    }
    if effect_config.effect_fn_includes(EFFECT_FN_NO_SPAN) {
        return "effectFnOpportunity_toEffectFnNoSpan";
    }
    if result.explicit_trace_expression.is_nil() {
        if effect_config.effect_fn_includes(EFFECT_FN_INFERRED_SPAN)
            && !result.inferred_trace_name.is_empty()
        {
            return "effectFnOpportunity_toEffectFnSpanInferred";
        }
        if effect_config.effect_fn_includes(EFFECT_FN_SUGGESTED_SPAN)
            && !result.suggested_trace_name.is_empty()
            && (!effect_config.effect_fn_includes(EFFECT_FN_INFERRED_SPAN)
                || result.suggested_trace_name != result.inferred_trace_name)
        {
            return "effectFnOpportunity_toEffectFnSpanSuggested";
        }
    }
    ""
}

/// buildExpectedSignature constructs the human-readable expected signature string
/// for the diagnostic message. The format matches the reference implementation:
/// it shows how the function would look after conversion with the highest-priority fix.
// Go: rules/effect_fn_opportunity.go buildExpectedSignature
fn build_expected_signature(sf: Node, m: &EffectFnOpportunityMatch, fix_name: &str) -> String {
    let result = &m.result;

    // Get the Effect module name
    let mut effect_module_name = "Effect".to_string();
    if result.effect_module.is_some() && result.effect_module.kind() == SyntaxKind::Identifier {
        effect_module_name = get_text_of_node(result.effect_module);
    }

    // Build type parameter string: <T, U, ...>
    let type_param_str = get_type_param_string(result.target_node);

    // Build parameter names string: (x, y, ...)
    let param_str = get_param_names_string(result.target_node);

    let fn_signature = if result.has_gen_body {
        format!("function*{type_param_str}({param_str}) {{ ... }}")
    } else if result.target_node.is_some() && result.target_node.kind() == SyntaxKind::ArrowFunction
    {
        format!("{type_param_str}({param_str}) => {{ ... }}")
    } else {
        format!("function{type_param_str}({param_str}) {{ ... }}")
    };

    let pipe_args: &[Node] = &result.pipe_arguments;
    let mut pipe_args_for_with_span = pipe_args;
    if !pipe_args.is_empty() {
        pipe_args_for_with_span = &pipe_args[..pipe_args.len() - 1];
    }

    let pipe_args_suffix = |args: &[Node]| -> &'static str {
        if !args.is_empty() {
            return ", ...pipeTransformations";
        }
        ""
    };

    match fix_name {
        "effectFnOpportunity_toEffectFnWithSpan" => {
            let mut trace_name = String::new();
            if result.explicit_trace_expression.is_some() {
                let text = source_file_text(sf);
                let expr = result.explicit_trace_expression;
                trace_name = text[expr.pos() as usize..expr.end() as usize]
                    .trim()
                    .to_string();
            }
            format!(
                "{effect_module_name}.fn({trace_name})({fn_signature}{})",
                pipe_args_suffix(pipe_args_for_with_span)
            )
        }

        "effectFnOpportunity_toEffectFnUntraced" => format!(
            "{effect_module_name}.fnUntraced({fn_signature}{})",
            pipe_args_suffix(pipe_args)
        ),

        "effectFnOpportunity_toEffectFnNoSpan" => format!(
            "{effect_module_name}.fn({fn_signature}{})",
            pipe_args_suffix(pipe_args)
        ),

        "effectFnOpportunity_toEffectFnSpanInferred" => format!(
            "{effect_module_name}.fn(\"{}\")({fn_signature}{})",
            result.inferred_trace_name,
            pipe_args_suffix(pipe_args)
        ),

        "effectFnOpportunity_toEffectFnSpanSuggested" => format!(
            "{effect_module_name}.fn(\"{}\")({fn_signature}{})",
            result.suggested_trace_name,
            pipe_args_suffix(pipe_args)
        ),

        _ => format!("{effect_module_name}.fn({fn_signature})"),
    }
}

/// getTypeParamString extracts type parameter names from a function node and returns
/// a string like "<T, U>" or "" if there are no type parameters.
// Go: rules/effect_fn_opportunity.go getTypeParamString
fn get_type_param_string(fn_node: Node) -> String {
    let type_params = get_function_like_type_parameters(fn_node);

    if type_params.is_nil() || type_params.nodes().is_empty() {
        return String::new();
    }

    let mut names: Vec<String> = Vec::new();
    for tp in type_params.nodes().iter() {
        if !is_type_parameter_declaration(tp) {
            continue;
        }
        let name = tp.name();
        if name.is_some() {
            names.push(get_text_of_node(name));
        }
    }
    if names.is_empty() {
        return String::new();
    }
    format!("<{}>", names.join(", "))
}

/// getParamNamesString extracts parameter names from a function node and returns
/// a string like "x, y" or "" if there are no parameters.
/// For destructuring patterns, uses "_" as a placeholder.
// Go: rules/effect_fn_opportunity.go getParamNamesString
fn get_param_names_string(fn_node: Node) -> String {
    let params = get_function_like_parameters(fn_node);

    if params.is_nil() || params.nodes().is_empty() {
        return String::new();
    }

    let mut names: Vec<String> = Vec::new();
    for p in params.nodes().iter() {
        let pd = p;
        let name = pd.name();
        if name.is_some() && name.kind() == SyntaxKind::Identifier {
            names.push(get_text_of_node(name));
        } else {
            names.push("_".to_string());
        }
    }
    names.join(", ")
}
