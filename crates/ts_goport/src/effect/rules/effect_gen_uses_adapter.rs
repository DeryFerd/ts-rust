//! Port of Effect-TS/tsgo `internal/rules/effect_gen_uses_adapter.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// EffectGenUsesAdapter warns when using the deprecated adapter parameter in Effect.gen.
pub static EFFECT_GEN_USES_ADAPTER: Rule = Rule {
    name: "effectGenUsesAdapter",
    group: "antipattern",
    description: "Warns when using the deprecated adapter parameter in Effect.gen",
    default_severity: Severity::Warning,
    supported_effect: &["v3", "v4"],
    codes: &[377027],
    run: run_effect_gen_uses_adapter,
};

fn run_effect_gen_uses_adapter(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diags = Vec::new();

    fn walk(ctx: &mut RuleContext<'_, '_>, n: Node, diags: &mut Vec<Diagnostic>) -> bool {
        if n.is_nil() {
            return false;
        }

        if n.kind() == SyntaxKind::CallExpression
            && let Some(diag) = check_effect_gen_uses_adapter(ctx, n)
        {
            diags.push(diag);
        }

        n.for_each_child(|child| walk(ctx, child, diags));
        false
    }

    let sf = ctx.source_file;
    walk(ctx, sf, &mut diags);

    diags
}

// Go: rules/effect_gen_uses_adapter.go checkEffectGenUsesAdapter
fn check_effect_gen_uses_adapter(ctx: &mut RuleContext<'_, '_>, n: Node) -> Option<Diagnostic> {
    let gen_result = ctx.tp.effect_gen_call(n)?;

    if gen_result.generator_function.parameter_list().is_nil()
        || gen_result.generator_function.parameters().is_empty()
    {
        return None;
    }

    let adapter_param = gen_result.generator_function.parameters().get(0);
    Some(ctx.new_diagnostic(
        ctx.source_file,
        ctx.get_error_range(adapter_param),
        diag::The_adapter_of_Effect_gen_is_not_required_anymore_it_is_now_just_an_alias_of_pipe_effect_effectGenUsesAdapter,
        Vec::new(),
        Vec::new(),
    ))
}
