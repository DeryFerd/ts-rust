//! Port of Effect-TS/tsgo `internal/rules/try_catch_in_effect_gen.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// TryCatchInEffectGen detects try/catch statements inside Effect generators
// and suggests using Effect's error handling mechanisms instead.
pub static TRY_CATCH_IN_EFFECT_GEN: Rule = Rule {
    name: "tryCatchInEffectGen",
    group: "antipattern",
    description: "Discourages try/catch in Effect generators in favor of Effect error handling",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377012],
    run: run_try_catch_in_effect_gen,
};

fn run_try_catch_in_effect_gen(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    fn walk(ctx: &mut RuleContext<'_, '_>, diags: &mut Vec<Diagnostic>, n: Node) -> bool {
        if n.is_nil() {
            return false;
        }

        if n.kind() == SyntaxKind::TryStatement {
            let try_stmt = n;
            if try_stmt.catch_clause().is_some() {
                if let Some(d) = check_try_catch_scope(ctx, n) {
                    diags.push(d);
                }
            }
        }

        n.for_each_child(|child| walk(ctx, diags, child));
        false
    }

    let mut diags = Vec::new();
    let sf = ctx.source_file;
    walk(ctx, &mut diags, sf);
    diags
}

// checkTryCatchScope checks if the try statement is directly inside an Effect
// generator scope using FindEnclosingScopes.
fn check_try_catch_scope(ctx: &mut RuleContext<'_, '_>, try_node: Node) -> Option<Diagnostic> {
    if ctx
        .tp
        .get_effect_context_flags(try_node)
        .intersects(EffectContextFlags::CAN_YIELD_EFFECT)
    {
        return Some(ctx.new_diagnostic(
            ctx.source_file,
            ctx.get_error_range(try_node),
            diag::This_Effect_generator_contains_try_Slashcatch_in_this_context_error_handling_is_expressed_with_Effect_APIs_such_as_Effect_try_Effect_tryPromise_Effect_catch_Effect_catchTag_effect_tryCatchInEffectGen,
            Vec::new(),
            Vec::new(),
        ));
    }
    None
}
