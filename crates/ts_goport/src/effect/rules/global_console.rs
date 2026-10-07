//! Port of Effect-TS/tsgo `internal/rules/global_console.go`.

use crate::diagnostics::Message;
use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// PORT: Go keeps a `map[string]string` and ranges over it in random order.
// A call expression matches at most one `console.<method>`, and the loop
// breaks on the first match, so the order does not change the output.
// Go: rules/global_console.go globalConsoleMethodAlternatives
static GLOBAL_CONSOLE_METHOD_ALTERNATIVES: &[(&str, &str)] = &[
    ("log", "Effect.log or Logger"),
    ("warn", "Effect.logWarning or Logger"),
    ("error", "Effect.logError or Logger"),
    ("info", "Effect.logInfo or Logger"),
    ("debug", "Effect.logDebug or Logger"),
    ("trace", "Effect.logTrace or Logger"),
];

// Go: rules/global_console.go GlobalConsole
pub static GLOBAL_CONSOLE: Rule = Rule {
    name: "globalConsole",
    group: "effectNative",
    description: "Warns when using console methods outside Effect generators instead of Effect.log/Logger",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377064],
    run: run_global_console_rule,
};

fn run_global_console_rule(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    run_global_console(ctx, false)
}

// Go: rules/global_console.go GlobalConsoleInEffect
pub static GLOBAL_CONSOLE_IN_EFFECT: Rule = Rule {
    name: "globalConsoleInEffect",
    group: "effectNative",
    description: "Warns when using console methods inside Effect generators instead of Effect.log/Logger",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377065],
    run: run_global_console_in_effect,
};

fn run_global_console_in_effect(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    run_global_console(ctx, true)
}

// Go: rules/global_console.go runGlobalConsole
fn run_global_console(ctx: &mut RuleContext<'_, '_>, check_in_effect: bool) -> Vec<Diagnostic> {
    let mut message = diag::This_code_uses_console_1_the_corresponding_Effect_logging_API_is_0_effect_globalConsole;
    if check_in_effect {
        message = diag::This_Effect_code_uses_console_1_logging_in_Effect_code_is_represented_through_0_effect_globalConsoleInEffect;
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
            if in_effect == check_in_effect {
                for &(method, alternative) in GLOBAL_CONSOLE_METHOD_ALTERNATIVES {
                    if !ctx.tp.is_node_reference_to_global_member(
                        node.expression(),
                        "console",
                        method,
                    ) {
                        continue;
                    }
                    diags.push(ctx.new_diagnostic(
                        ctx.source_file,
                        get_error_range_for_node(ctx.source_file, node),
                        message,
                        Vec::new(),
                        vec![alternative.to_string(), method.to_string()],
                    ));
                    break;
                }
            }
        }

        node.for_each_child(|child| walk(ctx, diags, message, check_in_effect, child));
        false
    }

    let sf = ctx.source_file;
    walk(ctx, &mut diags, message, check_in_effect, sf);

    diags
}
