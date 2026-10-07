//! Port of Effect-TS/tsgo `internal/rules/nested_effect_gen_yield.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// NestedEffectGenYield warns when yield* targets a bare nested Effect.gen inside
/// an existing Effect generator context, since the inner generator can usually be
/// inlined directly into the surrounding Effect generator.
// Go: rules/nested_effect_gen_yield.go NestedEffectGenYield
pub static NESTED_EFFECT_GEN_YIELD: Rule = Rule {
    name: "nestedEffectGenYield",
    group: "style",
    description: "Warns when yielding a nested bare Effect.gen inside an existing Effect generator context",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377083],
    run: run_nested_effect_gen_yield,
};

fn run_nested_effect_gen_yield(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_nested_effect_gen_yield(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            ctx.source_file,
            m.location,
            diag::This_yield_Asterisk_is_applied_to_a_nested_Effect_gen_that_can_be_inlined_in_the_parent_Effect_generator_context_effect_nestedEffectGenYield,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

// Go: rules/nested_effect_gen_yield.go NestedEffectGenYieldMatch
#[derive(Clone, Copy)]
pub struct NestedEffectGenYieldMatch {
    pub location: TextRange,
}

// Go: rules/nested_effect_gen_yield.go AnalyzeNestedEffectGenYield
pub fn analyze_nested_effect_gen_yield(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<NestedEffectGenYieldMatch> {
    let mut matches = Vec::new();

    // PORT: Go's recursive `walk` closure.
    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        matches: &mut Vec<NestedEffectGenYieldMatch>,
        node: Node,
    ) -> bool {
        if node.is_nil() {
            return false;
        }

        if node.kind() == SyntaxKind::YieldExpression {
            let yield_expr = node;
            if yield_expr.asterisk_token().is_some()
                && yield_expr.expression().is_some()
                && tp
                    .get_effect_context_flags(node)
                    .intersects(EffectContextFlags::CAN_YIELD_EFFECT)
                && tp.effect_gen_call(yield_expr.expression()).is_some()
            {
                matches.push(NestedEffectGenYieldMatch {
                    location: get_error_range_for_node(sf, yield_expr.expression()),
                });
            }
        }

        node.for_each_child(|child| walk(tp, sf, matches, child));
        false
    }

    walk(tp, sf, &mut matches, sf);
    matches
}
