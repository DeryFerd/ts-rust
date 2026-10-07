//! Port of Effect-TS/tsgo `internal/rules/return_effect_in_gen.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// ReturnEffectInGen detects return statements inside Effect generators
/// that return an Effect-able type, which would result in nested Effect<Effect<...>>.
// Go: rules/return_effect_in_gen.go ReturnEffectInGen
pub static RETURN_EFFECT_IN_GEN: Rule = Rule {
    name: "returnEffectInGen",
    group: "antipattern",
    description: "Warns when returning an Effect in a generator causes nested Effect<Effect<...>>",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377014],
    run: run_return_effect_in_gen,
};

fn run_return_effect_in_gen(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_return_effect_in_gen(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_generator_returns_an_Effect_able_value_directly_which_produces_a_nested_Effect_Effect_If_the_intended_result_is_the_inner_Effect_value_return_yield_Asterisk_represents_that_form_effect_returnEffectInGen,
            Vec::new(),
            vec![],
        ));
    }
    diags
}

/// ReturnEffectInGenMatch holds the diagnostic and the return statement node needed
/// by both the diagnostic rule and the quick-fix.
// Go: rules/return_effect_in_gen.go ReturnEffectInGenMatch
#[derive(Clone, Debug)]
pub struct ReturnEffectInGenMatch {
    /// The source file where this match was found
    pub source_file: Node,
    /// The pre-computed error range for this match
    pub location: TextRange,
    /// The return statement AST node
    pub return_node: Node,
}

/// AnalyzeReturnEffectInGen finds all return statements inside Effect generators
/// that return an Effect-able type, returning matches with both the diagnostic and the return node.
// Go: rules/return_effect_in_gen.go AnalyzeReturnEffectInGen
pub fn analyze_return_effect_in_gen(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<ReturnEffectInGenMatch> {
    let mut matches: Vec<ReturnEffectInGenMatch> = Vec::new();

    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        matches: &mut Vec<ReturnEffectInGenMatch>,
        n: Node,
    ) -> bool {
        if n.is_nil() {
            return false;
        }

        if n.kind() == SyntaxKind::ReturnStatement {
            if check_return_effect_in_gen_scope(tp, sf, n) {
                matches.push(ReturnEffectInGenMatch {
                    source_file: sf,
                    location: get_error_range_for_node(sf, n),
                    return_node: n,
                });
            }
        }

        n.for_each_child(|child| walk(tp, sf, matches, child));
        false
    }

    walk(tp, sf, &mut matches, sf);
    matches
}

/// checkReturnEffectInGenScope checks if a return statement inside an Effect generator
/// is returning an Effect-able type (which would cause nested Effect<Effect<...>>).
// Go: rules/return_effect_in_gen.go checkReturnEffectInGenScope
fn check_return_effect_in_gen_scope(tp: &mut TypeParser<'_>, _sf: Node, n: Node) -> bool {
    let return_stmt = n;
    if return_stmt.is_nil() || return_stmt.expression().is_nil() {
        return false;
    }

    // return yield* ... is the correct pattern, skip it
    if return_stmt.expression().kind() == SyntaxKind::YieldExpression {
        return false;
    }

    if !tp
        .get_effect_context_flags(n)
        .intersects(EffectContextFlags::CAN_YIELD_EFFECT)
    {
        return false;
    }

    let t = tp.get_type_at_location(return_stmt.expression());
    if t.is_nil() {
        return false;
    }

    if !tp.strict_is_effect_type(t) {
        return false;
    }

    true
}
