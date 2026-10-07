// Go: internal/rules/missing_layer_context.go

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// MissingLayerContext detects when a Layer has context requirements that are not
/// handled by the expected type. This happens when assigning a Layer with requirements
/// to a variable/parameter expecting a Layer with fewer or no requirements.
pub static MISSING_LAYER_CONTEXT: Rule = Rule {
    name: "missingLayerContext",
    group: "correctness",
    description: "Detects Layer values with unhandled context requirements",
    default_severity: Severity::Error,
    supported_effect: &["v3", "v4"],
    codes: &[377034],
    run: run_missing_layer_context,
};

fn run_missing_layer_context(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diags = Vec::new();

    let sf = ctx.source_file;
    for re in ctx.tp.checker.get_relation_errors(sf) {
        // Parse both types as Layers
        let src_layer = ctx.tp.layer_type(re.source);
        let tgt_layer = ctx.tp.layer_type(re.target);

        // Both must be Layer types
        let (Some(src_layer), Some(tgt_layer)) = (src_layer, tgt_layer) else {
            continue;
        };

        // Find unhandled context types by checking each source RIn member
        // against the target RIn type
        let mut unhandled = find_unhandled_layer_contexts(ctx.tp, src_layer.r_in, tgt_layer.r_in);
        if !unhandled.is_empty() {
            // Sort deterministically by type name (alphabetical)
            let c = &mut *ctx.tp.checker;
            crate::gostd::slices::sort_slice(&mut unhandled, |a, b| {
                c.type_to_string_exported(*a) < c.type_to_string_exported(*b)
            });
            let context_type_str = format_layer_context_types(ctx.tp.checker, &unhandled);
            let diag = ctx.new_diagnostic(
                ctx.source_file,
                ctx.get_error_range(re.error_node),
                diag::Missing_0_in_the_expected_Layer_context_effect_missingLayerContext,
                Vec::new(),
                vec![context_type_str],
            );
            diags.push(diag);
        }
    }

    diags
}

// Go: rules/missing_layer_context.go findUnhandledLayerContexts
/// findUnhandledLayerContexts returns the source Layer RIn types that are not assignable to the target RIn type.
fn find_unhandled_layer_contexts(
    tp: &mut TypeParser<'_>,
    src_r_in: TypeId,
    tgt_r_in: TypeId,
) -> Vec<TypeId> {
    // Unroll source RIn union into individual members
    let src_members = tp.unroll_union_members(src_r_in);

    let mut unhandled = Vec::new();
    for member in src_members {
        // Check if this specific member is assignable to target
        if !tp.checker.is_type_assignable_to(member, tgt_r_in) {
            unhandled.push(member);
        }
    }
    unhandled
}

// Go: rules/missing_layer_context.go formatLayerContextTypes
/// formatLayerContextTypes formats a slice of Layer context types as a union string (e.g., "ServiceA | ServiceB").
fn format_layer_context_types(c: &mut Checker, types: &[TypeId]) -> String {
    if types.is_empty() {
        return String::new();
    }
    if types.len() == 1 {
        return c.type_to_string_exported(types[0]);
    }
    let mut result = String::new();
    result.push_str(&c.type_to_string_exported(types[0]));
    for t in &types[1..] {
        result.push_str(" | ");
        result.push_str(&c.type_to_string_exported(*t));
    }
    result
}
