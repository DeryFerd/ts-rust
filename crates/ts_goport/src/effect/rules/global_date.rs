//! Port of Effect-TS/tsgo `internal/rules/global_date.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules.GlobalDate
pub static GLOBAL_DATE: Rule = Rule {
    name: "globalDate",
    group: "effectNative",
    description: "Warns when using Date.now() or new Date() outside Effect generators instead of Clock/DateTime",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377066, 377068],
    run: run_global_date_rule,
};

fn run_global_date_rule(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    run_global_date(ctx, false)
}

// Go: rules.GlobalDateInEffect
pub static GLOBAL_DATE_IN_EFFECT: Rule = Rule {
    name: "globalDateInEffect",
    group: "effectNative",
    description: "Warns when using Date.now() or new Date() inside Effect generators instead of Clock/DateTime",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377067, 377069],
    run: run_global_date_in_effect_rule,
};

fn run_global_date_in_effect_rule(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    run_global_date(ctx, true)
}

// Go: rules.runGlobalDate
fn run_global_date(ctx: &mut RuleContext<'_, '_>, check_in_effect: bool) -> Vec<Diagnostic> {
    let date_symbol =
        ctx.tp
            .checker
            .resolve_name_exported("Date", Node::NIL, SymbolFlags::VALUE, false);
    if date_symbol.is_nil() {
        return Vec::new();
    }

    let mut diags = Vec::new();
    let source_file = ctx.source_file;
    walk(ctx, check_in_effect, date_symbol, &mut diags, source_file);

    diags
}

fn walk(
    ctx: &mut RuleContext<'_, '_>,
    check_in_effect: bool,
    date_symbol: SymbolId,
    diags: &mut Vec<Diagnostic>,
    node: Node,
) -> bool {
    if node.is_nil() {
        return false;
    }
    let in_effect = ctx
        .tp
        .get_effect_context_flags(node)
        .intersects(EffectContextFlags::IN_EFFECT);
    if in_effect == check_in_effect {
        let mut matched = false;
        let mut message =
            diag::This_code_uses_Date_now_time_access_is_represented_through_Clock_from_Effect_effect_globalDate;

        match node.kind() {
            SyntaxKind::CallExpression => {
                let call = node;
                matched =
                    ctx.tp
                        .is_node_reference_to_global_member(call.expression(), "Date", "now");
                if matched && check_in_effect {
                    message = diag::This_Effect_code_uses_Date_now_time_access_in_Effect_code_is_represented_through_Clock_from_Effect_effect_globalDateInEffect;
                }
            }
            SyntaxKind::NewExpression => {
                let sym = ctx.tp.get_symbol_at_location(node.expression());
                matched = ctx.tp.resolve_to_global_symbol(sym) == date_symbol;
                message = diag::This_code_constructs_new_Date_date_values_are_represented_through_DateTime_from_Effect_effect_globalDate;
                if check_in_effect {
                    message = diag::This_Effect_code_constructs_new_Date_date_values_in_Effect_code_are_represented_through_DateTime_from_Effect_effect_globalDateInEffect;
                }
            }
            _ => {}
        }

        if matched {
            diags.push(ctx.new_diagnostic(
                ctx.source_file,
                get_error_range_for_node(ctx.source_file, node),
                message,
                Vec::new(),
                Vec::new(),
            ));
        }
    }

    node.for_each_child(|n| walk(ctx, check_in_effect, date_symbol, diags, n));
    false
}
