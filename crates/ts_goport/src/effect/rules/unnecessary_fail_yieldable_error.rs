//! Port of Effect-TS/tsgo `internal/rules/unnecessary_fail_yieldable_error.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// UnnecessaryFailYieldableError suggests yielding yieldable errors directly
// instead of wrapping with Effect.fail.
pub static UNNECESSARY_FAIL_YIELDABLE_ERROR: Rule = Rule {
    name: "unnecessaryFailYieldableError",
    group: "style",
    description: "Suggests yielding yieldable errors directly instead of wrapping with Effect.fail",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377019],
    run: run_unnecessary_fail_yieldable_error,
};

fn run_unnecessary_fail_yieldable_error(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_unnecessary_fail_yieldable_error(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_yield_Asterisk_Effect_fail_passes_a_yieldable_error_value_yield_Asterisk_represents_that_value_directly_without_wrapping_it_in_Effect_fail_effect_unnecessaryFailYieldableError,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

// UnnecessaryFailYieldableErrorMatch holds the AST nodes needed by both the
// diagnostic rule and the quick-fix for the unnecessaryFailYieldableError pattern.
#[derive(Clone, Debug)]
pub struct UnnecessaryFailYieldableErrorMatch {
    /// The source file where this match was found
    pub source_file: Node,
    /// The pre-computed error range for this match
    pub location: TextRange,
    /// The yield* expression node
    pub yield_node: Node,
    /// The Effect.fail(...) call expression (fix replaces this)
    pub call_node: Node,
    /// The first argument to Effect.fail (the replacement text)
    pub fail_argument: Node,
}

// AnalyzeUnnecessaryFailYieldableError finds all yield* Effect.fail(...) calls
// where the argument is a yieldable error type that can be yielded directly.
pub fn analyze_unnecessary_fail_yieldable_error(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<UnnecessaryFailYieldableErrorMatch> {
    let mut matches = Vec::new();

    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        matches: &mut Vec<UnnecessaryFailYieldableErrorMatch>,
        n: Node,
    ) -> bool {
        if n.is_nil() {
            return false;
        }

        if n.kind() == SyntaxKind::YieldExpression {
            let yield_ = n;
            // Must be yield* (not plain yield)
            if yield_.asterisk_token().is_some()
                && yield_.expression().is_some()
                && yield_.expression().kind() == SyntaxKind::CallExpression
            {
                let call = yield_.expression();
                if call.expression().is_some()
                    && tp.is_node_reference_to_effect_module_api(call.expression(), "fail")
                {
                    if !call.arguments().is_empty() {
                        let arg = call.arguments().get(0);
                        let arg_type = tp.get_type_at_location(arg);
                        if arg_type.is_some() && tp.is_yieldable_error_type(arg_type) {
                            matches.push(UnnecessaryFailYieldableErrorMatch {
                                source_file: sf,
                                location: get_error_range_for_node(sf, n),
                                yield_node: n,
                                call_node: yield_.expression(),
                                fail_argument: arg,
                            });
                        }
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
