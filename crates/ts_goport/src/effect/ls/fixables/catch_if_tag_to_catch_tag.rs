//! Port of Effect-TS/tsgo `internal/fixables/catch_if_tag_to_catch_tag.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::effect_module_method;
use crate::effect::ls::rewriter::PipingFlowTransformationReplacement;
use crate::effect::rules::catch_if_tag_to_catch_tag::analyze_catch_if_tag_to_catch_tag;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/catch_if_tag_to_catch_tag.go:12 CatchIfTagToCatchTagFix
pub static CATCH_IF_TAG_TO_CATCH_TAG_FIX: Fixable = Fixable {
    name: "catchIfTagToCatchTag",
    description: "Replace Effect.catchIf with Effect.catchTag",
    // Go: tsdiag.Effect_catchTag_expresses_tagged_error_recovery_more_directly_than_Effect_catchIf_with_a_tag_equality_predicate_effect_catchIfTagToCatchTag
    error_codes: &[377131],
    fix_ids: &["catchIfTagToCatchTag_fix"],
    run: run_catch_if_tag_to_catch_tag_fix,
};

// Go: fixables/catch_if_tag_to_catch_tag.go:18 runCatchIfTagToCatchTagFix
fn run_catch_if_tag_to_catch_tag_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;
    for m in analyze_catch_if_tag_to_catch_tag(ctx.tp, sf) {
        if !m.can_fix {
            continue;
        }
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        let action = ctx.new_fix_action("Replace with Effect.catchTag".to_string(), |tracker| {
            let transformation_callee = m.transformation.callee;
            let receiver = if transformation_callee.kind() == SyntaxKind::PropertyAccessExpression {
                transformation_callee.expression()
            } else {
                Node::NIL
            };
            let callee = effect_module_method(tracker, sf, receiver, "catchTag");
            let f = tracker.node_factory();
            let arguments = f.new_node_list(&[
                f.new_string_literal(m.tag.as_str(), TokenFlags::NONE),
                f.deep_clone_node(m.handler),
            ]);
            tracker.replace_piping_flow_transformation(
                sf,
                &m.transformation,
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
