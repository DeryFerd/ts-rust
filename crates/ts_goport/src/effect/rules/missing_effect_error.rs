//! Port of Effect-TS/tsgo `internal/rules/missing_effect_error.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// MissingEffectError detects when an Effect has error types that are not
/// handled by the expected type. This happens when assigning an Effect with errors
/// to a variable/parameter expecting an Effect with fewer or no errors.
// Go: rules/missing_effect_error.go MissingEffectError
pub static MISSING_EFFECT_ERROR: Rule = Rule {
    name: "missingEffectError",
    group: "correctness",
    description: "Detects Effect values with unhandled error types",
    default_severity: Severity::Error,
    supported_effect: &["v3", "v4"],
    codes: &[377003],
    run: run_missing_effect_error,
};

fn run_missing_effect_error(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let sf = ctx.source_file;
    let matches = analyze_missing_effect_error(ctx.tp, sf);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Missing_errors_0_in_the_expected_Effect_type_effect_missingEffectError,
            Vec::new(),
            vec![m.error_type_str.clone()],
        ));
    }
    diags
}

/// MissingEffectErrorMatch holds the analysis results needed by both the
/// diagnostic rule and the quick-fixes for the missingEffectError pattern.
// Go: rules/missing_effect_error.go MissingEffectErrorMatch
#[derive(Clone, Debug)]
pub struct MissingEffectErrorMatch {
    /// The source file where the diagnostic should be reported
    pub source_file: Node,
    /// The diagnostic error range
    pub location: TextRange,
    /// The AST node where the type error occurs
    pub error_node: Node,
    /// The individual error types not handled by the target
    pub unhandled_errors: Vec<TypeId>,
    /// The target Effect's error type (.E)
    pub expected_error_type: TypeId,
    /// The formatted union string of unhandled errors
    pub error_type_str: String,
}

/// AnalyzeMissingEffectError finds all relation errors where an Effect has error
/// types that are not handled by the expected type.
// Go: rules/missing_effect_error.go AnalyzeMissingEffectError
pub fn analyze_missing_effect_error(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<MissingEffectErrorMatch> {
    let mut matches = Vec::new();

    for re in tp.checker.get_relation_errors(sf) {
        // Parse both types as Effects
        let src_effect = tp.effect_type(re.source);
        let tgt_effect = tp.effect_type(re.target);

        // Both must be Effect types
        let (Some(src_effect), Some(tgt_effect)) = (src_effect, tgt_effect) else {
            continue;
        };

        // If source has no errors, nothing to report
        if tp
            .checker
            .ty(src_effect.e)
            .flags
            .intersects(TypeFlags::NEVER)
        {
            continue;
        }

        // Find unhandled error types
        let unhandled_errors = find_unhandled_errors(tp, src_effect.e, tgt_effect.e);
        if !unhandled_errors.is_empty() {
            let error_type_str = format_error_types(tp.checker, &unhandled_errors);
            matches.push(MissingEffectErrorMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, re.error_node),
                error_node: re.error_node,
                unhandled_errors,
                expected_error_type: tgt_effect.e,
                error_type_str,
            });
        }
    }

    matches
}

/// findUnhandledErrors returns the source error types that are not assignable to the target error type.
// Go: rules/missing_effect_error.go findUnhandledErrors
fn find_unhandled_errors(tp: &mut TypeParser<'_>, src_e: TypeId, tgt_e: TypeId) -> Vec<TypeId> {
    // Unroll source error union into individual members
    let src_members = tp.unroll_union_members(src_e);

    let mut unhandled = Vec::new();
    for member in src_members {
        // Check if this specific member is assignable to target
        if !tp.checker.is_type_assignable_to(member, tgt_e) {
            unhandled.push(member);
        }
    }
    unhandled
}

/// formatErrorTypes formats a slice of error types as a union string (e.g., "ErrorA | ErrorB").
// Go: rules/missing_effect_error.go formatErrorTypes
fn format_error_types(c: &mut Checker, types: &[TypeId]) -> String {
    if types.is_empty() {
        return String::new();
    }
    if types.len() == 1 {
        return c.type_to_string_exported(types[0]);
    }
    let mut result = String::new();
    result.push_str(&c.type_to_string_exported(types[0]));
    for &t in &types[1..] {
        result.push_str(" | ");
        result.push_str(&c.type_to_string_exported(t));
    }
    result
}
