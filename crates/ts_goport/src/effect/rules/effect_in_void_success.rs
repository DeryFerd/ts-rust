//! Port of Effect-TS/tsgo `internal/rules/effect_in_void_success.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules.EffectInVoidSuccess
/// EffectInVoidSuccess detects nested Effects in void success channels.
/// When an Effect has void as its success type but the actual value contains
/// an Effect type, this likely means a nested Effect<Effect<...>> that won't be executed.
pub static EFFECT_IN_VOID_SUCCESS: Rule = Rule {
    name: "effectInVoidSuccess",
    group: "antipattern",
    description: "Detects nested Effects in void success channels that may cause unexecuted effects",
    default_severity: Severity::Warning,
    supported_effect: &["v3", "v4"],
    codes: &[377020],
    run: run_effect_in_void_success,
};

fn run_effect_in_void_success(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diags = Vec::new();

    let entries = ctx.tp.expected_and_real_types(ctx.source_file);
    for entry in entries.iter() {
        if entry.expected_type == entry.real_type {
            continue;
        }

        let Some(real_effect) = ctx.tp.effect_type(entry.real_type) else {
            continue;
        };

        let Some(expected_effect) = ctx.tp.effect_type(entry.expected_type) else {
            continue;
        };

        // Check if the expected Effect's success type is void
        if !ctx
            .tp
            .checker
            .ty(expected_effect.a)
            .flags()
            .intersects(TypeFlags::VOID)
        {
            continue;
        }

        // Unroll the real Effect's success type into union members
        // and check if any member is strictly an Effect type
        let members = ctx.tp.unroll_union_members(real_effect.a);
        let voided_effect = find_first_strict_effect(ctx.tp, &members);
        if voided_effect.is_some() {
            let type_string = ctx.tp.checker.type_to_string_exported(voided_effect);
            let diag = ctx.new_diagnostic(
                ctx.source_file,
                ctx.get_error_range(entry.node),
                diag::There_is_a_nested_0_in_the_void_success_channel_beware_that_this_could_lead_to_nested_Effect_Effect_that_won_t_be_executed_effect_effectInVoidSuccess,
                Vec::new(),
                vec![type_string],
            );
            diags.push(diag);
        }
    }

    diags
}

// Go: rules.findFirstStrictEffect
/// findFirstStrictEffect returns the first type in the slice that is strictly an Effect type,
/// or nil if none are found. This mirrors the Nano.firstSuccessOf pattern in the TS reference.
pub fn find_first_strict_effect(tp: &mut TypeParser<'_>, types: &[TypeId]) -> TypeId {
    for &t in types {
        if tp.strict_is_effect_type(t) {
            return t;
        }
    }
    TypeId::NIL
}
