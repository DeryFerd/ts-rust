//! Port of Effect-TS/tsgo `internal/fixables/catch_all_tag_dispatch_to_catch_tag.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::effect_module_method;
use crate::effect::ls::rewriter::{PipingFlowTransformationReplacement, Tracker};
use crate::effect::rules::catch_all_tag_dispatch_to_catch_tag::{
    CatchAllTagDispatchBranch, CatchAllTagDispatchMatch,
    analyze_catch_all_tag_dispatch_to_catch_tag,
};
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/catch_all_tag_dispatch_to_catch_tag.go:14 CatchAllTagDispatchToCatchTagFix
pub static CATCH_ALL_TAG_DISPATCH_TO_CATCH_TAG_FIX: Fixable = Fixable {
    name: "catchAllTagDispatchToCatchTag",
    description: "Replace hand-rolled tagged error dispatch with Effect.catchTag or Effect.catchTags",
    // Go: tsdiag.Branching_on_0_tag_inside_Effect_1_hand_rolls_tagged_error_dispatch_use_Effect_catchTag_or_Effect_catchTags_which_re_fail_unmatched_errors_automatically_effect_catchAllTagDispatchToCatchTag
    error_codes: &[377122],
    fix_ids: &["catchAllTagDispatchToCatchTag_fix"],
    run: run_catch_all_tag_dispatch_to_catch_tag_fix,
};

// Go: fixables/catch_all_tag_dispatch_to_catch_tag.go:20 runCatchAllTagDispatchToCatchTagFix
fn run_catch_all_tag_dispatch_to_catch_tag_fix(
    ctx: &mut FixableContext<'_, '_>,
) -> Vec<CodeAction> {
    let sf = ctx.source_file;
    for m in analyze_catch_all_tag_dispatch_to_catch_tag(ctx.tp, sf) {
        if !m.can_fix || (!m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location)) {
            continue;
        }
        let action = ctx.new_fix_action(
            "Replace with Effect.catchTag or Effect.catchTags".to_string(),
            |tracker| {
                if let Some((callee, arguments)) =
                    build_catch_all_tag_dispatch_replacement(tracker, sf, &m)
                {
                    tracker.replace_piping_flow_transformation(
                        sf,
                        &m.transformation,
                        PipingFlowTransformationReplacement {
                            callee,
                            type_arguments: NodeList::NIL,
                            arguments,
                        },
                    );
                }
            },
        );
        if let Some(action) = action {
            return vec![action];
        }
    }
    Vec::new()
}

// Go: fixables/catch_all_tag_dispatch_to_catch_tag.go:38 buildCatchAllTagDispatchReplacement
// PORT: Go returns `(nil, nil)` for no replacement; Rust returns None. Go's
// nil tracker check is gone (Rust references are never nil).
fn build_catch_all_tag_dispatch_replacement(
    tracker: &Tracker,
    sf: Node,
    m: &CatchAllTagDispatchMatch,
) -> Option<(Node, NodeList)> {
    if m.callee.is_nil() || m.branches.is_empty() {
        return None;
    }
    let receiver = if m.callee.kind() == SyntaxKind::PropertyAccessExpression {
        m.callee.expression()
    } else {
        Node::NIL
    };
    let method_name = if m.branches.len() > 1 {
        "catchTags"
    } else {
        "catchTag"
    };
    let callee = effect_module_method(tracker, sf, receiver, method_name);
    let f = tracker.node_factory();
    if m.branches.len() == 1 {
        let branch = &m.branches[0];
        return Some((
            callee,
            f.new_node_list(&[
                f.new_string_literal(branch.tag.as_str(), TokenFlags::NONE),
                new_catch_tag_handler(tracker, &m.parameter_name, branch),
            ]),
        ));
    }
    let mut properties = Vec::with_capacity(m.branches.len());
    for branch in &m.branches {
        let name = if is_identifier_text(&branch.tag, LanguageVariant::STANDARD) {
            f.new_identifier(branch.tag.as_str())
        } else {
            f.new_string_literal(branch.tag.as_str(), TokenFlags::NONE)
        };
        properties.push(f.new_property_assignment(
            ModifierList::NIL,
            name,
            Node::NIL,
            Node::NIL,
            new_catch_tag_handler(tracker, &m.parameter_name, branch),
        ));
    }
    Some((
        callee,
        f.new_node_list(&[f.new_object_literal_expression(f.new_node_list(&properties), false)]),
    ))
}

// Go: fixables/catch_all_tag_dispatch_to_catch_tag.go:66 newCatchTagHandler
fn new_catch_tag_handler(
    tracker: &Tracker,
    parameter_name: &str,
    branch: &CatchAllTagDispatchBranch,
) -> Node {
    let f = tracker.node_factory();
    let mut parameters = Vec::new();
    if branch.uses_parameter {
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
