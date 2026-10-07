//! Port of Effect-TS/tsgo `internal/rules/missing_return_yield_star.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules.MissingReturnYieldStar
/// MissingReturnYieldStar suggests "return yield*" for Effects that never succeed.
pub static MISSING_RETURN_YIELD_STAR: Rule = Rule {
    name: "missingReturnYieldStar",
    group: "correctness",
    description: "Suggests using return yield* for Effects that never succeed",
    default_severity: Severity::Error,
    supported_effect: &["v3", "v4"],
    codes: &[377006],
    run: run_missing_return_yield_star,
};

fn run_missing_return_yield_star(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_missing_return_yield_star(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_Effect_never_succeeds_using_return_yield_Asterisk_preserves_a_definitive_generator_exit_point_for_type_narrowing_and_tooling_support_effect_missingReturnYieldStar,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

// Go: rules.MissingReturnYieldStarMatch
/// MissingReturnYieldStarMatch holds the AST nodes needed by both the diagnostic rule
/// and the quick-fix for the missingReturnYieldStar pattern.
#[derive(Clone)]
pub struct MissingReturnYieldStarMatch {
    /// The source file where the diagnostic should be reported
    pub source_file: Node,
    /// The pre-computed error range for this match
    pub location: TextRange,
    /// The yield* expression node (for diagnostic location)
    pub yield_node: Node,
    /// The expression statement node (for quickfix replacement)
    pub expr_stmt_node: Node,
}

// Go: rules.AnalyzeMissingReturnYieldStar
/// AnalyzeMissingReturnYieldStar finds all yield* expressions inside Effect generators
/// where the yielded Effect never succeeds, suggesting "return yield*" instead.
pub fn analyze_missing_return_yield_star(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<MissingReturnYieldStarMatch> {
    let mut matches = Vec::new();

    walk(tp, sf, &mut matches, sf);

    matches
}

fn walk(
    tp: &mut TypeParser<'_>,
    sf: Node,
    matches: &mut Vec<MissingReturnYieldStarMatch>,
    n: Node,
) -> bool {
    if n.is_nil() {
        return false;
    }

    if n.kind() == SyntaxKind::ExpressionStatement {
        let expr = n.expression();
        let unwrapped = skip_outer_expressions(expr, OuterExpressionKinds::OEK_ALL);
        if unwrapped.is_some() && unwrapped.kind() == SyntaxKind::YieldExpression {
            let yield_ = unwrapped;
            if yield_.asterisk_token().is_some()
                && yield_.expression().is_some()
                && should_report_missing_return_yield_star(tp, n, unwrapped, yield_.expression())
            {
                matches.push(MissingReturnYieldStarMatch {
                    source_file: sf,
                    location: get_error_range_for_node(sf, unwrapped),
                    yield_node: unwrapped,
                    expr_stmt_node: n,
                });
            }
        }
    }

    n.for_each_child(|child| walk(tp, sf, matches, child));
    false
}

// Go: rules.shouldReportMissingReturnYieldStar
// PORT: Go also returns false for a nil checker; the type parser always has one.
fn should_report_missing_return_yield_star(
    tp: &mut TypeParser<'_>,
    expr_stmt_node: Node,
    yield_node: Node,
    expr: Node,
) -> bool {
    if expr_stmt_node.is_nil() || yield_node.is_nil() || expr.is_nil() {
        return false;
    }

    if !tp
        .get_effect_context_flags(expr_stmt_node)
        .intersects(EffectContextFlags::CAN_YIELD_EFFECT)
    {
        return false;
    }

    let t = tp.get_type_at_location(expr);
    if t.is_nil() {
        return false;
    }
    let Some(effect) = tp.effect_yieldable_type(t) else {
        return false;
    };
    if effect.a.is_nil() {
        return false;
    }
    tp.checker.ty(effect.a).flags().intersects(TypeFlags::NEVER)
}
