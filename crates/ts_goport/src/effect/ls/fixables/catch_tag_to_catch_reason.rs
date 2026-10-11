//! Port of Effect-TS/tsgo `internal/fixables/catch_tag_to_catch_reason.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::effect_module_method;
use crate::effect::ls::rewriter::{PipingFlowTransformationReplacement, Tracker};
use crate::effect::rules::catch_tag_to_catch_reason::{
    CatchTagToCatchReasonBranch, CatchTagToCatchReasonMatch, analyze_catch_tag_to_catch_reason,
};
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/catch_tag_to_catch_reason.go:12 CatchTagToCatchReasonFix
pub static CATCH_TAG_TO_CATCH_REASON_FIX: Fixable = Fixable {
    name: "catchTagToCatchReason",
    description: "Replace hand-rolled reason dispatch with Effect.catchReason or Effect.catchReasons",
    // Go: tsdiag.Branching_on_0_reason_tag_inside_Effect_1_hand_rolls_reason_dispatch_use_Effect_catchReason_or_Effect_catchReasons_which_re_fail_unmatched_reasons_automatically_effect_catchTagToCatchReason
    error_codes: &[377110],
    fix_ids: &["catchTagToCatchReason_fix"],
    run: run_catch_tag_to_catch_reason_fix,
};

// Go: fixables/catch_tag_to_catch_reason.go:22 runCatchTagToCatchReasonFix
// PORT: Go skips a match with a nil `Transformation`; the Rust match always
// has one.
fn run_catch_tag_to_catch_reason_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;
    let matches = analyze_catch_tag_to_catch_reason(ctx.tp, sf);
    for m in matches {
        if !m.can_fix || (!m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location)) {
            continue;
        }
        if m.callee.is_nil() {
            continue;
        }

        if let Some(action) = ctx.new_fix_action(
            "Replace with Effect.catchReason or Effect.catchReasons".to_string(),
            |tracker| {
                let Some((callee, arguments)) =
                    build_catch_tag_to_catch_reason_replacement(tracker, sf, &m)
                else {
                    return;
                };
                tracker.replace_piping_flow_transformation(
                    sf,
                    &m.transformation,
                    PipingFlowTransformationReplacement {
                        callee,
                        type_arguments: NodeList::NIL,
                        arguments,
                    },
                );
            },
        ) {
            return vec![action];
        }
    }

    Vec::new()
}

// Go: fixables/catch_tag_to_catch_reason.go:52 buildCatchTagToCatchReasonReplacement
// PORT: Go returns `(nil, nil)` for no replacement; Rust returns None. Go's
// nil tracker check is gone (Rust references are never nil).
fn build_catch_tag_to_catch_reason_replacement(
    tracker: &Tracker,
    sf: Node,
    m: &CatchTagToCatchReasonMatch,
) -> Option<(Node, NodeList)> {
    if m.callee.is_nil() || m.outer_tag.is_nil() || m.branches.is_empty() {
        return None;
    }
    let receiver = if m.callee.kind() == SyntaxKind::PropertyAccessExpression {
        m.callee.expression()
    } else {
        Node::NIL
    };

    let method_name = if m.branches.len() > 1 {
        "catchReasons"
    } else {
        "catchReason"
    };
    let method = effect_module_method(tracker, sf, receiver, method_name);
    let f = tracker.node_factory();
    let mut arguments = vec![f.deep_clone_node(m.outer_tag)];
    if m.branches.len() == 1 {
        let branch = &m.branches[0];
        arguments.push(f.new_string_literal(branch.reason_tag.as_str(), TokenFlags::NONE));
        arguments.push(new_catch_reason_handler(tracker, &m.parameter_name, branch));
    } else {
        let mut properties = Vec::with_capacity(m.branches.len());
        for branch in &m.branches {
            properties.push(f.new_property_assignment(
                ModifierList::NIL,
                f.new_string_literal(branch.reason_tag.as_str(), TokenFlags::NONE),
                Node::NIL,
                Node::NIL,
                new_catch_reason_handler(tracker, &m.parameter_name, branch),
            ));
        }
        arguments.push(f.new_object_literal_expression(f.new_node_list(&properties), false));
    }

    Some((method, f.new_node_list(&arguments)))
}

// Go: fixables/catch_tag_to_catch_reason.go:87 newCatchReasonHandler
fn new_catch_reason_handler(
    tracker: &Tracker,
    parameter_name: &str,
    branch: &CatchTagToCatchReasonBranch,
) -> Node {
    let f = tracker.node_factory();
    let mut parameters = Vec::new();
    if branch.uses_parameter {
        parameters.push(f.new_parameter_declaration(
            ModifierList::NIL,
            Node::NIL,
            f.new_identifier(branch.reason_parameter_name.as_str()),
            Node::NIL,
            Node::NIL,
            Node::NIL,
        ));
        parameters.push(f.new_parameter_declaration(
            ModifierList::NIL,
            Node::NIL,
            f.new_identifier(parameter_name),
            Node::NIL,
            Node::NIL,
            Node::NIL,
        ));
    }
    f.new_arrow_function(
        ModifierList::NIL,
        NodeList::NIL,
        f.new_node_list(&parameters),
        Node::NIL,
        Node::NIL,
        f.new_token(SyntaxKind::EqualsGreaterThanToken),
        f.deep_clone_node(branch.result),
    )
}
