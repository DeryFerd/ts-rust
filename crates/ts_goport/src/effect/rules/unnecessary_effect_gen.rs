//! Port of Effect-TS/tsgo `internal/rules/unnecessary_effect_gen.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules.UnnecessaryEffectGen
/// UnnecessaryEffectGen suggests removing Effect.gen when it contains only a single return statement.
pub static UNNECESSARY_EFFECT_GEN: Rule = Rule {
    name: "unnecessaryEffectGen",
    group: "style",
    description: "Suggests removing Effect.gen when it contains only a single return statement",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377017],
    run: run_unnecessary_effect_gen,
};

fn run_unnecessary_effect_gen(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_unnecessary_effect_gen(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_Effect_gen_contains_a_single_return_statement_effect_unnecessaryEffectGen,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

// Go: rules.UnnecessaryEffectGenMatch
/// UnnecessaryEffectGenMatch holds the AST nodes needed by both the diagnostic rule
/// and the quick-fix for the unnecessaryEffectGen pattern.
#[derive(Clone)]
pub struct UnnecessaryEffectGenMatch {
    /// The source file where this match was found
    pub source_file: Node,
    /// The pre-computed error range for this match
    pub location: TextRange,
    /// The Effect.gen(...) call expression (replacement target)
    pub call_node: Node,
    /// The expression being yield*-ed (the replacement value)
    pub yielded_expression: Node,
    /// Whether the statement had an explicit return
    pub explicit_return: bool,
    /// Whether the yielded Effect's success type is void-like
    pub success_is_void: bool,
    /// The Effect module identifier (for Effect.asVoid wrapping)
    pub effect_module_node: Node,
}

// Go: rules.AnalyzeUnnecessaryEffectGen
/// AnalyzeUnnecessaryEffectGen finds all Effect.gen calls that contain only a single
/// yield* statement and can be replaced with the yielded expression directly.
pub fn analyze_unnecessary_effect_gen(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<UnnecessaryEffectGenMatch> {
    let mut matches = Vec::new();

    walk(tp, sf, &mut matches, sf);
    matches
}

fn walk(
    tp: &mut TypeParser<'_>,
    sf: Node,
    matches: &mut Vec<UnnecessaryEffectGenMatch>,
    n: Node,
) -> bool {
    if n.is_nil() {
        return false;
    }

    if n.kind() == SyntaxKind::CallExpression {
        if let Some(m) = analyze_unnecessary_effect_gen_node(tp, sf, n) {
            matches.push(m);
        }
    }

    n.for_each_child(|child| walk(tp, sf, matches, child));
    false
}

// Go: rules.analyzeUnnecessaryEffectGenNode
fn analyze_unnecessary_effect_gen_node(
    tp: &mut TypeParser<'_>,
    sf: Node,
    n: Node,
) -> Option<UnnecessaryEffectGenMatch> {
    let gen_result = tp.effect_gen_call(n)?;

    // Must have exactly one argument (just the generator, no options object)
    if gen_result.call.arguments().len() != 1 {
        return None;
    }

    let body = gen_result.body;
    if body.is_nil() || body.kind() != SyntaxKind::Block {
        return None;
    }

    let block = body;
    if block.statements().len() != 1 {
        return None;
    }

    let stmt = block.statements().get(0);

    let expr;
    let explicit_return;

    match stmt.kind() {
        SyntaxKind::ReturnStatement => {
            expr = stmt.expression();
            if expr.is_nil() {
                return None;
            }
            explicit_return = true;
        }
        SyntaxKind::ExpressionStatement => {
            expr = stmt.expression();
            explicit_return = false;
        }
        _ => return None,
    }

    // Must be a yield* expression
    if expr.kind() != SyntaxKind::YieldExpression {
        return None;
    }
    let yield_ = expr;
    if yield_.asterisk_token().is_nil() || yield_.expression().is_nil() {
        return None;
    }

    let yielded_expr = yield_.expression();
    if for_each_yield_expression(yielded_expr, &mut is_yield_star_expression) {
        return None;
    }

    // Determine if the success type is void-like
    let mut success_is_void = false;
    let t = tp.get_type_at_location(yielded_expr);
    if t.is_some() {
        if let Some(effect) = tp.effect_type(t)
            && effect.a.is_some()
        {
            success_is_void = tp
                .checker
                .ty(effect.a)
                .flags()
                .intersects(TypeFlags::VOID_LIKE);
        }
    }

    Some(UnnecessaryEffectGenMatch {
        source_file: sf,
        location: get_error_range_for_node(sf, n),
        call_node: n,
        yielded_expression: yielded_expr,
        explicit_return,
        success_is_void,
        effect_module_node: gen_result.effect_module,
    })
}

// Go: rules.isYieldStarExpression
fn is_yield_star_expression(expr: Node) -> bool {
    expr.asterisk_token().is_some()
}
