//! Port of Effect-TS/tsgo `internal/rules/effect_succeed_with_void.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// EffectSucceedWithVoid suggests using Effect.void instead of Effect.succeed(undefined) or Effect.succeed(void 0).
pub static EFFECT_SUCCEED_WITH_VOID: Rule = Rule {
    name: "effectSucceedWithVoid",
    group: "style",
    description: "Suggests using Effect.void instead of Effect.succeed(undefined) or Effect.succeed(void 0)",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377016],
    run: run_effect_succeed_with_void,
};

fn run_effect_succeed_with_void(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_effect_succeed_with_void(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_void_represents_the_same_outcome_as_Effect_succeed_undefined_or_Effect_succeed_void_0_effect_effectSucceedWithVoid,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

/// EffectSucceedWithVoidMatch holds the AST nodes needed by both the diagnostic rule
/// and the quick-fix for the effectSucceedWithVoid pattern.
#[derive(Clone, Debug)]
pub struct EffectSucceedWithVoidMatch {
    /// The source file where the diagnostic should be reported
    pub source_file: Node,
    /// The pre-computed error range for this match
    pub location: TextRange,
    /// The Effect.succeed(...) call expression (replacement target)
    pub call_node: Node,
    /// The Effect module identifier (e.g., "Effect" in Effect.succeed)
    pub effect_module_node: Node,
}

/// isVoidExpression checks if a node is `undefined`, `void 0`, or a parenthesized version of either.
pub fn is_void_expression(node: Node) -> bool {
    // Unwrap parenthesized expressions
    let node = skip_parentheses(node);

    // Check for `undefined`
    if node.kind() == SyntaxKind::Identifier && get_text_of_node(node) == "undefined" {
        return true;
    }

    // Check for `void 0`
    if node.kind() == SyntaxKind::VoidExpression {
        let operand = node.expression();
        if operand.kind() == SyntaxKind::NumericLiteral && get_text_of_node(operand) == "0" {
            return true;
        }
    }

    false
}

/// AnalyzeEffectSucceedWithVoid finds all Effect.succeed(undefined) and Effect.succeed(void 0) calls
/// that can be replaced with Effect.void.
pub fn analyze_effect_succeed_with_void(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<EffectSucceedWithVoidMatch> {
    let mut matches = Vec::new();

    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        matches: &mut Vec<EffectSucceedWithVoidMatch>,
        n: Node,
    ) -> bool {
        if n.is_nil() {
            return false;
        }

        if n.kind() == SyntaxKind::CallExpression {
            let call = n;
            if call.expression().is_some()
                && tp.is_node_reference_to_effect_module_api(call.expression(), "succeed")
            {
                if call.argument_list().is_some() && !call.arguments().is_empty() {
                    let arg = call.arguments().get(0);
                    if is_void_expression(arg) {
                        let mut effect_module = Node::NIL;
                        if call.expression().kind() == SyntaxKind::PropertyAccessExpression {
                            effect_module = call.expression().expression();
                        }
                        matches.push(EffectSucceedWithVoidMatch {
                            source_file: sf,
                            location: get_error_range_for_node(sf, n),
                            call_node: n,
                            effect_module_node: effect_module,
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
