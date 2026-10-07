//! Port of Effect-TS/tsgo `internal/rules/effect_fn_implicit_any.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// EffectFnImplicitAny mirrors TypeScript's noImplicitAny behavior for
/// Effect.fn-family callbacks, which are otherwise
/// contextually typed by the helper's internal any[] fallback.
pub static EFFECT_FN_IMPLICIT_ANY: Rule = Rule {
    name: "effectFnImplicitAny",
    group: "correctness",
    description: "Mirrors noImplicitAny for unannotated Effect.fn, Effect.fnUntraced, and Effect.fnUntracedEager callback parameters when no outer contextual function type exists. Requires TS's noImplicitAny: true",
    default_severity: Severity::Error,
    supported_effect: &["v3", "v4"],
    codes: &[377062],
    run: run_effect_fn_implicit_any,
};

fn run_effect_fn_implicit_any(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let options = ctx.program.options;
    if !options.get_strict_option_value(options.no_implicit_any) {
        return Vec::new();
    }

    let mut diags = Vec::new();

    fn walk(ctx: &mut RuleContext<'_, '_>, n: Node, diags: &mut Vec<Diagnostic>) -> bool {
        if n.is_nil() {
            return false;
        }

        if let Some(result) = ctx.tp.effect_fn_call(n) {
            if result.is_generator() {
                diags.extend(check_effect_fn_implicit_any(ctx, &result));
            } else {
                diags.extend(check_effect_fn_implicit_any_body(
                    ctx,
                    result.call,
                    result.function_node,
                ));
            }
        }

        n.for_each_child(|child| walk(ctx, child, diags));
        false
    }

    let sf = ctx.source_file;
    walk(ctx, sf, &mut diags);

    diags
}

// Go: rules/effect_fn_implicit_any.go checkEffectFnImplicitAny
fn check_effect_fn_implicit_any(
    ctx: &mut RuleContext<'_, '_>,
    result: &EffectFnCallResult,
) -> Vec<Diagnostic> {
    let gen_fn = result.generator_function();
    if gen_fn.is_nil() || gen_fn.parameter_list().is_nil() {
        return Vec::new();
    }
    check_effect_fn_implicit_any_parameters(ctx, result.call, &gen_fn.parameters().to_vec())
}

// Go: rules/effect_fn_implicit_any.go checkEffectFnImplicitAnyBody
fn check_effect_fn_implicit_any_body(
    ctx: &mut RuleContext<'_, '_>,
    call_node: Node,
    fn_node: Node,
) -> Vec<Diagnostic> {
    if fn_node.is_nil() {
        return Vec::new();
    }

    match fn_node.kind() {
        SyntaxKind::ArrowFunction => {
            let fn_ = fn_node;
            if fn_.parameter_list().is_nil() {
                return Vec::new();
            }
            check_effect_fn_implicit_any_parameters(ctx, call_node, &fn_.parameters().to_vec())
        }
        SyntaxKind::FunctionExpression => {
            let fn_ = fn_node;
            if fn_.parameter_list().is_nil() {
                return Vec::new();
            }
            check_effect_fn_implicit_any_parameters(ctx, call_node, &fn_.parameters().to_vec())
        }
        _ => Vec::new(),
    }
}

// Go: rules/effect_fn_implicit_any.go checkEffectFnImplicitAnyParameters
fn check_effect_fn_implicit_any_parameters(
    ctx: &mut RuleContext<'_, '_>,
    call_node: Node,
    params: &[Node],
) -> Vec<Diagnostic> {
    if has_outer_contextual_function_type(ctx.tp, call_node) {
        return Vec::new();
    }

    let mut diags = Vec::new();
    for &param in params {
        if param.is_nil() || param.type_().is_some() || param.initializer().is_some() {
            continue;
        }

        let mut name = declaration_name_to_string(param.name());
        if name.is_empty() {
            name = "parameter".to_string();
        }

        diags.push(ctx.new_diagnostic(
            ctx.source_file,
            ctx.get_error_range(param.name()),
            diag::Parameter_0_implicitly_has_type_any_in_Effect_fn_Effect_fnUntraced_or_Effect_fnUntracedEager_No_parameter_type_is_available_from_an_explicit_annotation_or_contextual_function_type_effect_effectFnImplicitAny,
            Vec::new(),
            args![name],
        ));
    }

    diags
}

// Go: rules/effect_fn_implicit_any.go hasOuterContextualFunctionType
fn has_outer_contextual_function_type(tp: &mut TypeParser<'_>, node: Node) -> bool {
    if node.is_nil() || !is_expression(node) {
        return false;
    }

    // Go `c.GetContextualType(node, ContextFlagsNone)`: without
    // ContextFlagsIgnoreNodeInferences it calls getContextualType directly.
    let contextual_type = tp.checker.get_contextual_type(node, ContextFlags::NONE);
    if contextual_type.is_nil() {
        return false;
    }

    for member in tp.unroll_union_members(contextual_type) {
        if !tp
            .checker
            .get_signatures_of_type(member, SignatureKind::CALL)
            .is_empty()
        {
            return true;
        }
    }

    false
}
