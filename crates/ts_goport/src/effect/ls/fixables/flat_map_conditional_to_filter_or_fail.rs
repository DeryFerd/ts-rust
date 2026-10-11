//! Port of Effect-TS/tsgo `internal/fixables/flat_map_conditional_to_filter_or_fail.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::effect_module_method;
use crate::effect::ls::rewriter::{PipingFlowTransformationReplacement, Tracker};
use crate::effect::rules::flat_map_conditional_to_filter_or_fail::{
    FlatMapConditionalToFilterOrFailMatch, analyze_flat_map_conditional_to_filter_or_fail,
};
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/flat_map_conditional_to_filter_or_fail.go:12 FlatMapConditionalToFilterOrFailFix
pub static FLAT_MAP_CONDITIONAL_TO_FILTER_OR_FAIL_FIX: Fixable = Fixable {
    name: "flatMapConditionalToFilterOrFail",
    description: "Replace a conditional Effect.flatMap identity filter with Effect.filterOrFail or Effect.filterOrElse",
    // Go: tsdiag.Effect_0_expresses_this_conditional_validation_more_directly_than_Effect_flatMap_with_an_identity_Effect_succeed_branch_effect_flatMapConditionalToFilterOrFail
    error_codes: &[377120],
    fix_ids: &["flatMapConditionalToFilterOrFail_fix"],
    run: run_flat_map_conditional_to_filter_or_fail_fix,
};

// Go: fixables/flat_map_conditional_to_filter_or_fail.go:22 runFlatMapConditionalToFilterOrFailFix
// PORT: Go also skips a match with a nil `Transformation`; the Rust match
// always has one.
fn run_flat_map_conditional_to_filter_or_fail_fix(
    ctx: &mut FixableContext<'_, '_>,
) -> Vec<CodeAction> {
    for m in analyze_flat_map_conditional_to_filter_or_fail(ctx.tp, ctx.source_file) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        if !m.can_fix
            || m.parameter_node.is_nil()
            || m.predicate_node.is_nil()
            || m.fallback_node.is_nil()
        {
            continue;
        }

        let sf = ctx.source_file;
        if let Some(action) = ctx.new_fix_action(
            format!("Replace with Effect.{}", m.preferred_method_name),
            |tracker| {
                let (callee, arguments) =
                    build_flat_map_conditional_filter_replacement(tracker, sf, &m);
                if callee.is_nil() || arguments.is_nil() {
                    return;
                }
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

// Go: fixables/flat_map_conditional_to_filter_or_fail.go:55 buildFlatMapConditionalFilterReplacement
fn build_flat_map_conditional_filter_replacement(
    tracker: &Tracker,
    sf: Node,
    m: &FlatMapConditionalToFilterOrFailMatch,
) -> (Node, NodeList) {
    let callee = effect_module_method(tracker, sf, m.effect_module_node, &m.preferred_method_name);
    let f = tracker.node_factory();
    let mut predicate_body = f.deep_clone_node(m.predicate_node);
    if m.negate_predicate {
        predicate_body =
            f.new_prefix_unary_expression(SyntaxKind::ExclamationToken, predicate_body);
    }
    let parameter = f.deep_clone_node(m.parameter_node);
    let predicate = f.new_arrow_function(
        ModifierList::NIL,
        NodeList::NIL,
        f.new_node_list(&[parameter]),
        Node::NIL,
        Node::NIL,
        f.new_token(SyntaxKind::EqualsGreaterThanToken),
        predicate_body,
    );
    let fallback = f.new_arrow_function(
        ModifierList::NIL,
        NodeList::NIL,
        f.new_node_list(&[f.deep_clone_node(m.parameter_node)]),
        Node::NIL,
        Node::NIL,
        f.new_token(SyntaxKind::EqualsGreaterThanToken),
        f.deep_clone_node(m.fallback_node),
    );
    (callee, f.new_node_list(&[predicate, fallback]))
}
