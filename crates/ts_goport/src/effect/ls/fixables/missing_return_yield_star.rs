//! Port of Effect-TS/tsgo `internal/fixables/missing_return_yield_star.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::missing_return_yield_star::analyze_missing_return_yield_star;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/missing_return_yield_star.go:14 MissingReturnYieldStarFix
/// MissingReturnYieldStarFix adds "return" before a yield* expression in Effect.gen when needed.
pub static MISSING_RETURN_YIELD_STAR_FIX: Fixable = Fixable {
    name: "missingReturnYieldStar",
    description: "Add return before yield* for never-success Effect yields",
    // Go: tsdiag.This_Effect_never_succeeds_using_return_yield_Asterisk_preserves_a_definitive_generator_exit_point_for_type_narrowing_and_tooling_support_effect_missingReturnYieldStar
    error_codes: &[377006],
    fix_ids: &["missingReturnYieldStar_fix"],
    run: run_missing_return_yield_star_fix,
};

// Go: fixables/missing_return_yield_star.go:22 runMissingReturnYieldStarFix
fn run_missing_return_yield_star_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_missing_return_yield_star(ctx.tp, sf);

    let mut matched_expr_stmt = Node::NIL;
    for m in &matches {
        let diag_range = m.location;
        if diag_range.intersects(ctx.span) || ctx.span.contained_by(diag_range) {
            matched_expr_stmt = m.expr_stmt_node;
            break;
        }
    }
    if matched_expr_stmt.is_nil() {
        return Vec::new();
    }

    if let Some(action) = ctx.new_fix_action("Add return statement".to_string(), |tracker| {
        let f = tracker.node_factory();
        let cloned_expr = f.deep_clone_node(matched_expr_stmt.expression());
        let return_stmt = f.new_return_statement(cloned_expr);
        set_parent_in_children(return_stmt);
        tracker.replace_node(sf, matched_expr_stmt, return_stmt, None);
    }) {
        return vec![action];
    }
    Vec::new()
}
