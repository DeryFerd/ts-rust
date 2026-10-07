//! Port of Effect-TS/tsgo `internal/rules/global_error_in_effect_catch.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// Go `globalErrorCatchApis`: the Effect module APIs that have a catch callback parameter.
static GLOBAL_ERROR_CATCH_APIS: &[&str] = &["tryPromise", "try", "tryMap", "tryMapPromise"];

// Go: rules.GlobalErrorInEffectCatch
/// GlobalErrorInEffectCatch detects when catch callbacks in Effect APIs return the global 'Error'
/// type instead of providing typed errors.
pub static GLOBAL_ERROR_IN_EFFECT_CATCH: Rule = Rule {
    name: "globalErrorInEffectCatch",
    group: "antipattern",
    description: "Warns when catch callbacks return global Error type instead of typed errors",
    default_severity: Severity::Warning,
    supported_effect: &["v3", "v4"],
    codes: &[377022],
    run: run_global_error_in_effect_catch,
};

fn run_global_error_in_effect_catch(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diags = Vec::new();

    let source_file = ctx.source_file;
    walk(ctx, &mut diags, source_file);

    diags
}

fn walk(ctx: &mut RuleContext<'_, '_>, diags: &mut Vec<Diagnostic>, n: Node) -> bool {
    if n.is_nil() {
        return false;
    }

    if n.kind() == SyntaxKind::CallExpression {
        if let Some(diag) = check_global_error_in_effect_catch(ctx, n) {
            diags.push(diag);
        }
    }

    n.for_each_child(|child| walk(ctx, diags, child));
    false
}

// Go: rules.checkGlobalErrorInEffectCatch
/// checkGlobalErrorInEffectCatch checks a single call expression for the global-error-in-catch pattern.
fn check_global_error_in_effect_catch(
    ctx: &mut RuleContext<'_, '_>,
    node: Node,
) -> Option<Diagnostic> {
    if node.kind() != SyntaxKind::CallExpression {
        return None;
    }
    let call = node;

    let callee = call.expression();
    if !is_global_error_catch_callee(ctx.tp, callee) {
        return None;
    }

    let sig = ctx.tp.checker.get_resolved_signature_exported(node);
    if sig.is_nil() {
        return None;
    }

    let params = ctx.tp.checker.sig(sig).parameters().to_vec();
    if params.is_empty() {
        return None;
    }

    let param_type = ctx
        .tp
        .checker
        .get_type_of_symbol_at_location(params[0], node);
    if param_type.is_nil() {
        return None;
    }

    for object_type in ctx.tp.unroll_union_members(param_type) {
        let catch_symbol = ctx
            .tp
            .checker
            .get_property_of_type_exported(object_type, "catch");
        if catch_symbol.is_nil() {
            continue;
        }

        let catch_type = ctx
            .tp
            .checker
            .get_type_of_symbol_at_location(catch_symbol, node);
        if catch_type.is_nil() {
            continue;
        }

        let signatures = ctx
            .tp
            .checker
            .get_signatures_of_type_exported(catch_type, SignatureKind::CALL);
        if signatures.is_empty() {
            continue;
        }

        let return_type = ctx
            .tp
            .checker
            .get_return_type_of_signature_exported(signatures[0]);
        if return_type.is_nil() {
            continue;
        }

        if ctx.tp.is_global_error_type(return_type) {
            let callee_text =
                get_source_text_of_node_from_source_file(ctx.source_file, callee, false);
            return Some(ctx.new_diagnostic(
                ctx.source_file,
                ctx.get_error_range(callee),
                diag::The_catch_callback_in_0_returns_the_global_Error_type_Untagged_errors_merge_together_in_the_Effect_error_channel_and_lose_type_level_distinction_a_tagged_error_preserves_that_distinction_and_can_wrap_the_original_error_in_a_cause_property_effect_globalErrorInEffectCatch,
                Vec::new(),
                vec![callee_text],
            ));
        }
    }

    None
}

// Go: rules.isGlobalErrorCatchCallee
/// isGlobalErrorCatchCallee checks if a node references one of the Effect module catch APIs.
fn is_global_error_catch_callee(tp: &mut TypeParser<'_>, node: Node) -> bool {
    for name in GLOBAL_ERROR_CATCH_APIS {
        if tp.is_node_reference_to_effect_module_api(node, name) {
            return true;
        }
    }
    false
}
