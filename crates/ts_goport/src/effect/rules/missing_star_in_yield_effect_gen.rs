//! Port of Effect-TS/tsgo `internal/rules/missing_star_in_yield_effect_gen.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// MissingStarInYieldEffectGen detects bare yield (without *) inside Effect generator scopes.
// Go: rules/missing_star_in_yield_effect_gen.go MissingStarInYieldEffectGen
pub static MISSING_STAR_IN_YIELD_EFFECT_GEN: Rule = Rule {
    name: "missingStarInYieldEffectGen",
    group: "correctness",
    description: "Detects bare yield (without *) inside Effect generator scopes",
    default_severity: Severity::Error,
    supported_effect: &["v3", "v4"],
    codes: &[377007, 377008],
    run: run_missing_star_in_yield_effect_gen,
};

fn run_missing_star_in_yield_effect_gen(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let sf = ctx.source_file;
    let matches = analyze_missing_star_in_yield_effect_gen(ctx.tp, sf);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        let related_info = ctx.new_diagnostic(
            m.source_file,
            ctx.get_error_range(m.gen_fn_node),
            diag::Inside_this_Effect_generator_effect_missingStarInYieldEffectGen,
            Vec::new(),
            Vec::new(),
        );
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_uses_yield_for_an_Effect_value_yield_Asterisk_is_the_Effect_aware_form_in_this_context_effect_missingStarInYieldEffectGen,
            vec![related_info],
            Vec::new(),
        ));
    }
    diags
}

/// MissingStarInYieldEffectGenMatch holds the AST node needed by both the diagnostic rule
/// and the quick-fix for the missingStarInYieldEffectGen pattern.
// Go: rules/missing_star_in_yield_effect_gen.go MissingStarInYieldEffectGenMatch
#[derive(Clone, Debug)]
pub struct MissingStarInYieldEffectGenMatch {
    /// The source file where the diagnostic should be reported
    pub source_file: Node,
    /// The pre-computed error range for this match
    pub location: TextRange,
    /// The yield expression node (for fix range)
    pub yield_node: Node,
    /// The generator function node (for related info)
    pub gen_fn_node: Node,
}

/// AnalyzeMissingStarInYieldEffectGen finds all yield expressions inside Effect generators
/// that are missing the asterisk (yield instead of yield*).
// Go: rules/missing_star_in_yield_effect_gen.go AnalyzeMissingStarInYieldEffectGen
pub fn analyze_missing_star_in_yield_effect_gen(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<MissingStarInYieldEffectGenMatch> {
    let mut matches = Vec::new();

    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        matches: &mut Vec<MissingStarInYieldEffectGenMatch>,
        n: Node,
    ) -> bool {
        if n.is_nil() {
            return false;
        }

        if n.kind() == SyntaxKind::YieldExpression {
            let yield_ = n;
            if yield_.is_some() && yield_.expression().is_some() && yield_.asterisk_token().is_nil()
            {
                if tp
                    .get_effect_context_flags(n)
                    .intersects(EffectContextFlags::CAN_YIELD_EFFECT)
                {
                    let gen_fn = tp.get_effect_yield_generator_function(n);
                    if gen_fn.is_some() {
                        matches.push(MissingStarInYieldEffectGenMatch {
                            source_file: sf,
                            location: get_error_range_for_node(sf, n),
                            yield_node: n,
                            gen_fn_node: gen_fn,
                        });
                    }
                }
            }
        }

        n.for_each_child(|child| walk(tp, sf, matches, child));
        false
    }

    walk(tp, sf, &mut matches, sf);

    matches
}
