//! Port of Effect-TS/tsgo `internal/rules/floating_effect.go`.
//! Package rules contains all Effect diagnostic rule implementations.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// floatingEffectResult holds information about a detected floating Effect expression.
pub struct FloatingEffectResult {
    /// isStrict is true when the type's symbol name is exactly "Effect"
    pub is_strict: bool,
    /// exprType is the checker type of the floating expression
    pub expr_type: TypeId,
}

/// FloatingEffect detects Effect values that are created as standalone
/// expression statements and are neither yielded nor assigned.
pub static FLOATING_EFFECT: Rule = Rule {
    name: "floatingEffect",
    group: "correctness",
    description: "Detects Effect values that are neither yielded nor assigned",
    default_severity: Severity::Error,
    supported_effect: &["v3", "v4"],
    codes: &[377001, 377058],
    run: run_floating_effect,
};

fn run_floating_effect(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_floating_effect(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in matches {
        if m.is_strict {
            diags.push(ctx.new_diagnostic(
                m.source_file,
                m.location,
                diag::This_Effect_value_is_neither_yielded_nor_used_in_an_assignment_effect_floatingEffect,
                Vec::new(),
                Vec::new(),
            ));
        } else {
            let type_name = ctx.tp.checker.type_to_string(m.expr_type);
            diags.push(ctx.new_diagnostic(
                m.source_file,
                m.location,
                diag::This_Effect_able_0_value_is_neither_yielded_nor_assigned_to_a_variable_effect_floatingEffect,
                Vec::new(),
                args![type_name],
            ));
        }
    }
    diags
}

/// FloatingEffectMatch holds the diagnostic location and expression needed by
/// both the diagnostic rule and its quick-fix.
pub struct FloatingEffectMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub expression: Node,
    pub is_strict: bool,
    pub expr_type: TypeId,
}

/// AnalyzeFloatingEffect finds Effect values used as standalone expression statements.
// Go: rules/floating_effect.go AnalyzeFloatingEffect
pub fn analyze_floating_effect(tp: &mut TypeParser<'_>, sf: Node) -> Vec<FloatingEffectMatch> {
    let mut matches = Vec::new();
    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        node: Node,
        matches: &mut Vec<FloatingEffectMatch>,
    ) -> bool {
        if node.is_nil() {
            return false;
        }

        if let Some(result) = detect_floating_effect(tp, node) {
            let expression = node.expression();
            matches.push(FloatingEffectMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, expression),
                expression,
                is_strict: result.is_strict,
                expr_type: result.expr_type,
            });
        }

        node.for_each_child(|child| walk(tp, sf, child, matches));
        false
    }
    walk(tp, sf, sf, &mut matches);
    matches
}

/// detectFloatingEffect checks if a node is an expression statement containing an Effect type
/// that is neither yielded nor assigned. Returns nil if the node should not be reported,
/// or a result with type info for selecting the appropriate diagnostic message.
// Go: rules/floating_effect.go detectFloatingEffect
fn detect_floating_effect(tp: &mut TypeParser<'_>, node: Node) -> Option<FloatingEffectResult> {
    // Must be an ExpressionStatement
    if node.is_nil() || node.kind() != SyntaxKind::ExpressionStatement {
        return None;
    }

    let expr_stmt = node;
    if expr_stmt.expression().is_nil() {
        return None;
    }

    let expr = expr_stmt.expression();

    // Exclude assignment expressions
    if is_assignment_expression(expr) {
        return None;
    }

    // Get the type of the expression
    let t = tp.get_type_at_location(expr);
    if t.is_nil() {
        return None;
    }

    if tp.has_effect_type_id(t) {
        // Full Effect validation.
        if !tp.is_effect_type(t) {
            return None;
        }

        // Exclude Fiber types (considered valid floating operations)
        if tp.is_fiber_type(t) {
            return None;
        }

        // Exclude Effect subtypes (Exit, Option, Either, Pool, etc.)
        if tp.is_effect_subtype(t) {
            return None;
        }
    } else if tp.stream_type(t).is_none() {
        return None;
    }

    // Determine if this is strictly an Effect or an Effect-able type
    let is_strict = tp.strict_is_effect_type(t);
    Some(FloatingEffectResult {
        is_strict,
        expr_type: t,
    })
}

/// isAssignmentExpression checks if an expression is an assignment (=, ??=, &&=, ||=).
// Go: rules/floating_effect.go isAssignmentExpression
fn is_assignment_expression(node: Node) -> bool {
    if node.is_nil() || node.kind() != SyntaxKind::BinaryExpression {
        return false;
    }

    let bin_expr = node;
    if bin_expr.operator_token().is_nil() {
        return false;
    }

    matches!(
        bin_expr.operator_token().kind(),
        SyntaxKind::EqualsToken
            | SyntaxKind::QuestionQuestionEqualsToken
            | SyntaxKind::AmpersandAmpersandEqualsToken
            | SyntaxKind::BarBarEqualsToken
    )
}
