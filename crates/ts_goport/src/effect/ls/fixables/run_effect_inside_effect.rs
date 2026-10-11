//! Port of Effect-TS/tsgo `internal/fixables/run_effect_inside_effect.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::rewriter::Tracker;
use crate::effect::rules::run_effect_inside_effect::analyze_run_effect_inside_effect;
use crate::effect::typeparser::{EffectMajorVersion, TypeParser, find_module_identifier, member};
use crate::ls::CodeAction;
use crate::ls::change::NodeOptions;
use crate::prelude::*;
use crate::scanner_util::{get_text_of_node, get_token_pos_of_node};

// Go: fixables/run_effect_inside_effect.go:17 RunEffectInsideEffectFix
pub static RUN_EFFECT_INSIDE_EFFECT_FIX: Fixable = Fixable {
    name: "runEffectInsideEffect",
    description: "Use the current services or a runtime to run the Effect",
    error_codes: &[
        // Go: tsdiag.X_0_is_called_inside_an_Effect_with_a_separate_runtime_invocation_In_this_context_run_child_Effects_with_the_surrounding_runtime_which_can_be_accessed_through_Effect_runtime_and_Runtime_1_effect_runEffectInsideEffect
        377025,
        // Go: tsdiag.X_0_is_called_inside_an_Effect_with_a_separate_services_invocation_In_this_context_child_Effects_run_with_the_surrounding_services_which_can_be_accessed_through_Effect_context_and_Effect_1_With_effect_runEffectInsideEffect
        377074,
    ],
    fix_ids: &["runEffectInsideEffect_fix"],
    run: run_run_effect_inside_effect_fix,
};

// Go: fixables/run_effect_inside_effect.go:28 runRunEffectInsideEffectFix
// PORT: Go reads the `yield*` declarations of the generator body inside the
// edit closure. The scan uses the type parser (`&mut`), which the closure
// cannot borrow while `new_fix_action` holds the context, so it runs just
// before the action. It reads the checker only, so the edits are the same.
fn run_run_effect_inside_effect_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;
    let supported_effect = ctx.tp.supported_effect_version();

    let matches = analyze_run_effect_inside_effect(ctx.tp, sf);
    for m in matches {
        if !m.is_nested_scope {
            continue;
        }
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }

        // Go: run_effect_inside_effect.go:50-52 (in the closure)
        let block = m.generator_function.body();
        let (mut runtime_identifier, mut services_identifier) =
            yielded_runtime_and_services_identifiers(ctx.tp, block);

        let first_arg_pos = m.call_node.arguments().get(0).pos();
        let insert_at = ctx.byte_pos_to_lsp_position(first_arg_pos);
        if let Some(action) = ctx.new_fix_action(
            run_effect_inside_effect_fix_description(supported_effect).to_string(),
            |tracker| {
                let effect_module_identifier = find_module_identifier(sf, "Effect");
                if supported_effect == EffectMajorVersion::V4 {
                    if services_identifier.is_empty() {
                        services_identifier = "effectContext".to_string();
                        insert_yielded_effect_module_call(
                            tracker,
                            sf,
                            block,
                            &effect_module_identifier,
                            "context",
                            &services_identifier,
                        );
                    }
                } else if runtime_identifier.is_empty() {
                    runtime_identifier = "effectRuntime".to_string();
                    insert_yielded_effect_module_call(
                        tracker,
                        sf,
                        block,
                        &effect_module_identifier,
                        "runtime",
                        &runtime_identifier,
                    );
                }

                let runtime_module_identifier = find_module_identifier(sf, "Runtime");
                let callee_token_pos = get_token_pos_of_node(m.callee_node, sf, false);
                tracker.delete_range(sf, TextRange::new(callee_token_pos, first_arg_pos));

                let replacement_text = run_effect_inside_effect_replacement_text(
                    supported_effect,
                    &effect_module_identifier,
                    &runtime_module_identifier,
                    &m.method_name,
                    &runtime_identifier,
                    &services_identifier,
                );
                tracker.insert_text(sf, insert_at, &replacement_text);
            },
        ) {
            return vec![action];
        }
        return Vec::new();
    }

    Vec::new()
}

// Go: fixables/run_effect_inside_effect.go:53-84 (the statement scan of the
// closure)
/// The names of `const x = yield* Effect.runtime(..)` and
/// `const x = yield* Effect.context(..)` in the block; "" when none. A later
/// declaration wins.
fn yielded_runtime_and_services_identifiers(
    tp: &mut TypeParser<'_>,
    block: Node,
) -> (String, String) {
    let mut runtime_identifier = String::new();
    let mut services_identifier = String::new();
    for stmt in block.statements().iter() {
        if stmt.kind() != SyntaxKind::VariableStatement {
            continue;
        }
        let decl_list = stmt.declaration_list();
        if decl_list.is_nil() {
            continue;
        }
        let declarations = decl_list.declarations();
        if declarations.is_nil() || declarations.nodes().len() != 1 {
            continue;
        }
        let decl = declarations.nodes().get(0);
        if decl.initializer().is_nil() || decl.initializer().kind() != SyntaxKind::YieldExpression {
            continue;
        }
        let yield_expr = decl.initializer();
        if yield_expr.asterisk_token().is_nil()
            || yield_expr.expression().is_nil()
            || yield_expr.expression().kind() != SyntaxKind::CallExpression
        {
            continue;
        }
        let yielded_call = yield_expr.expression();
        if decl.name().is_nil() || decl.name().kind() != SyntaxKind::Identifier {
            continue;
        }
        let identifier = get_text_of_node(decl.name());
        if tp.is_node_reference_to_effect_module_api(yielded_call.expression(), member!("runtime"))
        {
            runtime_identifier.clone_from(&identifier);
        }
        if tp.is_node_reference_to_effect_module_api(yielded_call.expression(), member!("context"))
        {
            services_identifier = identifier;
        }
    }
    (runtime_identifier, services_identifier)
}

// Go: fixables/run_effect_inside_effect.go:122 runEffectInsideEffectFixDescription
fn run_effect_inside_effect_fix_description(supported_effect: EffectMajorVersion) -> &'static str {
    if supported_effect == EffectMajorVersion::V4 {
        return "Use the current services to run the Effect";
    }
    "Use a runtime to run the Effect"
}

// Go: fixables/run_effect_inside_effect.go:129 runEffectInsideEffectReplacementText
fn run_effect_inside_effect_replacement_text(
    supported_effect: EffectMajorVersion,
    effect_module_identifier: &str,
    runtime_module_identifier: &str,
    method_name: &str,
    runtime_identifier: &str,
    services_identifier: &str,
) -> String {
    if supported_effect == EffectMajorVersion::V4 {
        return format!("{effect_module_identifier}.{method_name}With({services_identifier})(");
    }
    format!("{runtime_module_identifier}.{method_name}({runtime_identifier}, ")
}

// Go: fixables/run_effect_inside_effect.go:143 insertYieldedEffectModuleCall
/// Inserts `const <variableName> = yield* <Effect>.<methodName><never>()` before
/// the first statement of the block (a formatted node edit of the base tracker).
fn insert_yielded_effect_module_call(
    tracker: &mut Tracker,
    sf: Node,
    block: Node,
    effect_module_identifier: &str,
    method_name: &str,
    variable_name: &str,
) {
    let f = tracker.node_factory();
    let effect_id = f.new_identifier(effect_module_identifier);
    let method_access = f.new_property_access_expression(
        effect_id,
        Node::NIL,
        f.new_identifier(method_name),
        NodeFlags::NONE,
    );
    let method_call = f.new_call_expression(
        method_access,
        Node::NIL,
        f.new_node_list(&[f.new_keyword_type_node(SyntaxKind::NeverKeyword)]),
        f.new_node_list(&[]),
        NodeFlags::NONE,
    );
    let yield_expr = f.new_yield_expression(f.new_token(SyntaxKind::AsteriskToken), method_call);
    let var_decl = f.new_variable_declaration(
        f.new_identifier(variable_name),
        Node::NIL,
        Node::NIL,
        yield_expr,
    );
    let var_decl_list =
        f.new_variable_declaration_list(f.new_node_list(&[var_decl]), NodeFlags::CONST);
    let var_stmt = f.new_variable_statement(ModifierList::NIL, var_decl_list);
    set_parent_in_children(var_stmt);

    let insert_pos = block.statements().get(0).pos();
    tracker.insert_node_at(
        sf,
        insert_pos,
        var_stmt,
        NodeOptions {
            prefix: "\n".to_string(),
            suffix: "\n".to_string(),
            ..NodeOptions::default()
        },
    );
}
