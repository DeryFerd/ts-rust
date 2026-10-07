//! Port of Effect-TS/tsgo `internal/rules/global_error_in_effect_failure.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// GlobalErrorInEffectFailure detects when `new Error(...)` expressions appear inside an Effect
/// context where the failure channel (E type parameter) contains the global Error type.
pub static GLOBAL_ERROR_IN_EFFECT_FAILURE: Rule = Rule {
    name: "globalErrorInEffectFailure",
    group: "antipattern",
    description: "Warns when the global Error type is used in an Effect failure channel",
    default_severity: Severity::Warning,
    supported_effect: &["v3", "v4"],
    codes: &[377023],
    run: run_global_error_in_effect_failure,
};

fn run_global_error_in_effect_failure(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diags = Vec::new();

    fn walk(ctx: &mut RuleContext<'_, '_>, diags: &mut Vec<Diagnostic>, n: Node) -> bool {
        if n.is_nil() {
            return false;
        }

        if n.kind() == SyntaxKind::NewExpression {
            if let Some(diag) = check_global_error_in_effect_failure(ctx, n) {
                diags.push(diag);
            }
        }

        n.for_each_child(|child| walk(ctx, diags, child));
        false
    }

    let sf = ctx.source_file;
    walk(ctx, &mut diags, sf);

    diags
}

/// checkGlobalErrorInEffectFailure checks a single new expression for the global-error-in-failure pattern.
fn check_global_error_in_effect_failure(
    ctx: &mut RuleContext<'_, '_>,
    node: Node,
) -> Option<Diagnostic> {
    // Get the type of the new expression
    let new_expr_type = ctx.tp.get_type_at_location(node);
    if new_expr_type.is_nil() {
        return None;
    }

    // Skip if not a global Error type
    if !ctx.tp.is_global_error_type(new_expr_type) {
        return None;
    }

    // Walk up the parent chain to find an enclosing Effect type
    let tp = &mut *ctx.tp;
    let ancestor = find_ancestor_or_quit(node.parent(), |current| {
        let current_type = tp.get_type_at_location(current);
        if current_type.is_nil() {
            return FindAncestorResult::FIND_ANCESTOR_FALSE;
        }

        let Some(effect_type) = tp.effect_type(current_type) else {
            return FindAncestorResult::FIND_ANCESTOR_FALSE;
        };

        // Found an Effect type — check if the failure channel contains global Error
        if tp
            .unroll_union_members(effect_type.e)
            .into_iter()
            .any(|member| tp.is_global_error_type(member))
        {
            return FindAncestorResult::FIND_ANCESTOR_TRUE;
        }

        // Effect type found but failure channel doesn't contain global Error — stop searching
        FindAncestorResult::FIND_ANCESTOR_QUIT
    });

    if ancestor.is_some() {
        return Some(ctx.new_diagnostic(
            ctx.source_file,
            ctx.get_error_range(node),
            diag::Global_Error_loses_type_safety_as_untagged_errors_merge_together_in_the_Effect_failure_channel_Consider_using_a_tagged_error_and_optionally_wrapping_the_original_in_a_cause_property_effect_globalErrorInEffectFailure,
            Vec::new(),
            Vec::new(),
        ));
    }

    None
}
