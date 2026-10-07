//! Port of Effect-TS/tsgo `internal/rules/global_random.go`.

use crate::diagnostics::Message;
use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules/global_random.go GlobalRandom
pub static GLOBAL_RANDOM: Rule = Rule {
    name: "globalRandom",
    group: "effectNative",
    description: "Warns when using Math.random() outside Effect generators instead of the Random service",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377070],
    run: run_global_random_rule,
};

fn run_global_random_rule(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    run_global_random(ctx, false)
}

// Go: rules/global_random.go GlobalRandomInEffect
pub static GLOBAL_RANDOM_IN_EFFECT: Rule = Rule {
    name: "globalRandomInEffect",
    group: "effectNative",
    description: "Warns when using Math.random() inside Effect generators instead of the Random service",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377071],
    run: run_global_random_in_effect,
};

fn run_global_random_in_effect(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    run_global_random(ctx, true)
}

// Go: rules/global_random.go runGlobalRandom
fn run_global_random(ctx: &mut RuleContext<'_, '_>, check_in_effect: bool) -> Vec<Diagnostic> {
    let mut message = diag::This_code_uses_Math_random_randomness_is_represented_through_the_Effect_Random_service_effect_globalRandom;
    if check_in_effect {
        message = diag::This_Effect_code_uses_Math_random_randomness_is_represented_through_the_Effect_Random_service_effect_globalRandomInEffect;
    }

    let mut diags: Vec<Diagnostic> = Vec::new();
    fn walk(
        ctx: &mut RuleContext<'_, '_>,
        diags: &mut Vec<Diagnostic>,
        message: &'static Message,
        check_in_effect: bool,
        node: Node,
    ) -> bool {
        if node.is_nil() {
            return false;
        }
        if node.kind() == SyntaxKind::CallExpression {
            let in_effect = ctx
                .tp
                .get_effect_context_flags(node)
                .intersects(EffectContextFlags::IN_EFFECT);
            if in_effect == check_in_effect
                && ctx
                    .tp
                    .is_node_reference_to_global_member(node.expression(), "Math", "random")
            {
                diags.push(ctx.new_diagnostic(
                    ctx.source_file,
                    get_error_range_for_node(ctx.source_file, node),
                    message,
                    Vec::new(),
                    vec![],
                ));
            }
        }

        node.for_each_child(|child| walk(ctx, diags, message, check_in_effect, child));
        false
    }

    let sf = ctx.source_file;
    walk(ctx, &mut diags, message, check_in_effect, sf);

    diags
}
