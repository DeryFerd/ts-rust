//! Port of Effect-TS/tsgo `internal/rules/process_env.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

pub static PROCESS_ENV: Rule = Rule {
    name: "processEnv",
    group: "effectNative",
    description: "Warns when reading process.env outside Effect generators instead of using Effect Config",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377076],
    run: run_process_env_rule,
};

fn run_process_env_rule(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    run_process_env(ctx, false)
}

pub static PROCESS_ENV_IN_EFFECT: Rule = Rule {
    name: "processEnvInEffect",
    group: "effectNative",
    description: "Warns when reading process.env inside Effect generators instead of using Effect Config",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377077],
    run: run_process_env_in_effect,
};

fn run_process_env_in_effect(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    run_process_env(ctx, true)
}

fn run_process_env(ctx: &mut RuleContext<'_, '_>, check_in_effect: bool) -> Vec<Diagnostic> {
    let process_symbol =
        ctx.tp
            .checker
            .resolve_name_exported("process", Node::NIL, SymbolFlags::VALUE, false);
    if process_symbol.is_nil() {
        return Vec::new();
    }

    let mut message = diag::This_code_reads_from_process_env_environment_configuration_is_represented_through_Config_from_Effect_effect_processEnv;
    if check_in_effect {
        message = diag::This_Effect_code_reads_from_process_env_environment_configuration_in_Effect_code_is_represented_through_Config_from_Effect_effect_processEnvInEffect;
    }

    fn walk(
        ctx: &mut RuleContext<'_, '_>,
        diags: &mut Vec<Diagnostic>,
        check_in_effect: bool,
        process_symbol: SymbolId,
        message: &'static crate::diagnostics::Message,
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
            let process_node = process_env_root(node);
            if process_node.is_some() {
                let sym = ctx.tp.get_symbol_at_location(process_node);
                if ctx.tp.resolve_to_global_symbol(sym) == process_symbol {
                    diags.push(ctx.new_diagnostic(
                        ctx.source_file,
                        get_error_range_for_node(ctx.source_file, node),
                        message,
                        Vec::new(),
                        Vec::new(),
                    ));
                }
            }
        }

        node.for_each_child(|child| {
            walk(ctx, diags, check_in_effect, process_symbol, message, child)
        });
        false
    }

    let mut diags = Vec::new();
    let sf = ctx.source_file;
    walk(
        ctx,
        &mut diags,
        check_in_effect,
        process_symbol,
        message,
        sf,
    );

    diags
}

fn process_env_root(node: Node) -> Node {
    if node.is_nil() {
        return Node::NIL;
    }
    if node.kind() != SyntaxKind::PropertyAccessExpression
        && node.kind() != SyntaxKind::ElementAccessExpression
    {
        return Node::NIL;
    }
    let access = node.expression();
    if !is_env_property_access(access) {
        return Node::NIL;
    }
    access.expression()
}

fn is_env_property_access(node: Node) -> bool {
    if node.is_nil() || node.kind() != SyntaxKind::PropertyAccessExpression {
        return false;
    }
    node.name().text() == "env"
}
