//! Port of Effect-TS/tsgo `internal/fixables/timeout_catch_tag_to_timeout_or_else.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::rewriter::PipingFlowTransformationReplacement;
use crate::effect::rules::timeout_catch_tag_to_timeout_or_else::analyze_timeout_catch_tag_to_timeout_or_else;
use crate::effect::typeparser::find_effect_module_identifier;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/timeout_catch_tag_to_timeout_or_else.go:13 TimeoutCatchTagToTimeoutOrElseFix
pub static TIMEOUT_CATCH_TAG_TO_TIMEOUT_OR_ELSE_FIX: Fixable = Fixable {
    name: "timeoutCatchTagToTimeoutOrElse",
    description: "Replace with a dedicated timeout combinator",
    // Go: tsdiag.Use_Effect_0_to_handle_this_timeout_directly_effect_timeoutCatchTagToTimeoutOrElse
    error_codes: &[377127],
    fix_ids: &["timeoutCatchTagToTimeoutOrElse_fix"],
    run: run_timeout_catch_tag_to_timeout_or_else_fix,
};

// Go: fixables/timeout_catch_tag_to_timeout_or_else.go:18 TimeoutCatchTagToTimeoutOrElseFix.Run
fn run_timeout_catch_tag_to_timeout_or_else_fix(
    ctx: &mut FixableContext<'_, '_>,
) -> Vec<CodeAction> {
    for m in analyze_timeout_catch_tag_to_timeout_or_else(ctx.tp, ctx.source_file) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        let sf = ctx.source_file;
        let action =
            ctx.new_fix_action(format!("Replace with Effect.{}", m.replacement_name), |t| {
                let f = t.node_factory();
                let effect_module = if m.effect_module.is_some() {
                    f.deep_clone_node(m.effect_module)
                } else {
                    f.new_identifier(find_effect_module_identifier(sf))
                };
                let callee = f.new_property_access_expression(
                    effect_module,
                    Node::NIL,
                    f.new_identifier(m.replacement_name.as_str()),
                    NodeFlags::NONE,
                );
                let mut argument = f.deep_clone_node(m.duration);
                if m.replacement_name == "timeoutOrElse" {
                    let mut handler = f.deep_clone_node(m.handler);
                    // Go: fixables/timeout_catch_tag_to_timeout_or_else.go:36
                    // `SkipParentheses(Handler).AsArrowFunction()` panics on
                    // another kind; the analyzer only matches arrow handlers.
                    let arrow = skip_parentheses(m.handler);
                    if arrow.kind() != SyntaxKind::ArrowFunction {
                        go_node_as_panic(arrow, "ArrowFunction");
                    }
                    if arrow.parameter_list().is_some() && !arrow.parameters().is_empty() {
                        handler = f.new_arrow_function(
                            ModifierList::NIL,
                            NodeList::NIL,
                            f.new_node_list(&[]),
                            f.deep_clone_node(arrow.type_()),
                            Node::NIL,
                            f.new_token(SyntaxKind::EqualsGreaterThanToken),
                            f.deep_clone_node(arrow.body()),
                        );
                    }
                    argument = f.new_object_literal_expression(
                        f.new_node_list(&[
                            f.new_property_assignment(
                                ModifierList::NIL,
                                f.new_identifier("duration"),
                                Node::NIL,
                                Node::NIL,
                                argument,
                            ),
                            f.new_property_assignment(
                                ModifierList::NIL,
                                f.new_identifier("orElse"),
                                Node::NIL,
                                Node::NIL,
                                handler,
                            ),
                        ]),
                        true,
                    );
                }
                let arguments = f.new_node_list(&[argument]);
                t.collapse_piping_flow_transformations(
                    sf,
                    &m.flow,
                    m.start,
                    m.end,
                    PipingFlowTransformationReplacement {
                        callee,
                        type_arguments: NodeList::NIL,
                        arguments,
                    },
                );
            });
        if let Some(action) = action {
            return vec![action];
        }
    }
    Vec::new()
}
