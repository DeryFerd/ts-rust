//! Port of Effect-TS/tsgo `internal/rules/abort_controller_in_effect.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules.AbortControllerInEffect
pub static ABORT_CONTROLLER_IN_EFFECT: Rule = Rule {
    name: "abortControllerInEffect",
    group: "effectNative",
    description: "Warns when manually constructing AbortController inside Effect generators instead of using Effect.abortSignal",
    default_severity: Severity::Suggestion,
    supported_effect: &["v4"],
    codes: &[377111],
    run: run_abort_controller_in_effect,
};

fn run_abort_controller_in_effect(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let abort_controller_symbol = ctx.tp.checker.resolve_name_exported(
        "AbortController",
        Node::NIL,
        SymbolFlags::VALUE,
        false,
    );
    if abort_controller_symbol.is_nil() {
        return Vec::new();
    }

    let mut diags = Vec::new();
    let source_file = ctx.source_file;
    walk(ctx, abort_controller_symbol, &mut diags, source_file);
    diags
}

fn walk(
    ctx: &mut RuleContext<'_, '_>,
    abort_controller_symbol: SymbolId,
    diags: &mut Vec<Diagnostic>,
    node: Node,
) -> bool {
    if node.is_nil() {
        return false;
    }

    if node.kind() == SyntaxKind::NewExpression
        && ctx
            .tp
            .get_effect_context_flags(node)
            .intersects(EffectContextFlags::CAN_YIELD_EFFECT)
    {
        let new_expr = node;
        let sym = ctx.tp.get_symbol_at_location(new_expr.expression());
        if ctx.tp.resolve_to_global_symbol(sym) == abort_controller_symbol {
            diags.push(ctx.new_diagnostic(
                ctx.source_file,
                get_error_range_for_node(ctx.source_file, node),
                diag::AbortController_is_manually_constructed_inside_Effect_code_Use_Effect_abortSignal_for_Effect_managed_cancellation_effect_abortControllerInEffect,
                Vec::new(),
                Vec::new(),
            ));
        }
    }

    node.for_each_child(|n| walk(ctx, abort_controller_symbol, diags, n));
    false
}
