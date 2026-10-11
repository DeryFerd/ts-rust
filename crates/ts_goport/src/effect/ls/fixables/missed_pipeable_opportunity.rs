//! Port of Effect-TS/tsgo `internal/fixables/missed_pipeable_opportunity.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::rewriter::Tracker;
use crate::effect::rules::missed_pipeable_opportunity::{
    MissedPipeableOpportunityMatch, analyze_missed_pipeable_opportunity,
};
use crate::effect::typeparser::{PipingFlow, PipingFlowTransformation, TransformationKind};
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/missed_pipeable_opportunity.go:13 MissedPipeableOpportunityFix
pub static MISSED_PIPEABLE_OPPORTUNITY_FIX: Fixable = Fixable {
    name: "missedPipeableOpportunity",
    description: "Convert to pipe style",
    // Go: tsdiag.This_nested_call_structure_has_a_pipeable_form_0_pipe_represents_the_same_call_sequence_in_pipe_style_and_may_be_easier_to_read_effect_missedPipeableOpportunity
    error_codes: &[377050],
    fix_ids: &["missedPipeableOpportunity_fix"],
    run: run_missed_pipeable_opportunity_fix,
};

// Go: fixables/missed_pipeable_opportunity.go:21 runMissedPipeableOpportunityFix
// PORT: Go falls back to 2 when the options are nil; the Rust context
// always has them.
fn run_missed_pipeable_opportunity_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let min_arg_count = ctx.options.get_pipeable_min_arg_count();

    let matches = analyze_missed_pipeable_opportunity(ctx.tp, sf, min_arg_count);

    let Some(m) = matches
        .iter()
        .find(|m| m.location.intersects(ctx.span) || ctx.span.contained_by(m.location))
    else {
        return Vec::new();
    };

    if let Some(action) = ctx.new_fix_action("Convert to pipe style".to_string(), |tracker| {
        build_missed_pipeable_replacement(tracker, sf, m);
    }) {
        return vec![action];
    }
    Vec::new()
}

// Go: fixables/missed_pipeable_opportunity.go:58 buildMissedPipeableReplacement
/// buildMissedPipeableReplacement builds the .pipe() replacement and applies it via tracker.ReplaceNode.
fn build_missed_pipeable_replacement(
    tracker: &mut Tracker,
    sf: Node,
    m: &MissedPipeableOpportunityMatch,
) {
    let flow = &m.flow;

    // Build the subject node for the pipe call
    let subject_node = if m.pipeable_start_index == 0 {
        tracker.node_factory().deep_clone_node(flow.subject.node)
    } else {
        // Need to find the original subject node at the right depth in the AST
        let subject_node = find_subject_node_at_depth(tracker, flow, m.pipeable_start_index);
        if subject_node.is_nil() {
            return;
        }
        subject_node
    };

    let f = tracker.node_factory();
    // Build pipe arguments from transformations
    let mut pipe_args = Vec::with_capacity(m.pipeable_transformations.len());
    for t in &m.pipeable_transformations {
        let arg = if !t.args.is_empty() {
            // It's a function call like Effect.map((x) => x + 1) -> create callee(args...)
            let cloned_callee = f.deep_clone_node(t.callee);
            let cloned_args: Vec<Node> = t.args.iter().map(|&a| f.deep_clone_node(a)).collect();
            f.new_call_expression(
                cloned_callee,
                Node::NIL,
                NodeList::NIL,
                f.new_node_list(&cloned_args),
                NodeFlags::NONE,
            )
        } else {
            // It's a constant like Effect.asVoid
            f.deep_clone_node(t.callee)
        };
        pipe_args.push(arg);
    }

    // Create subject.pipe(arg1, arg2, ...)
    let pipe_access = f.new_property_access_expression(
        subject_node,
        Node::NIL,
        f.new_identifier("pipe"),
        NodeFlags::NONE,
    );
    let pipe_call = f.new_call_expression(
        pipe_access,
        Node::NIL,
        NodeList::NIL,
        f.new_node_list(&pipe_args),
        NodeFlags::NONE,
    );

    // Wrap with "after" transformations if any
    let replacement_node = if !m.after_transformations.is_empty() {
        wrap_with_after_transformations(tracker, pipe_call, &m.after_transformations)
    } else {
        pipe_call
    };

    set_parent_in_children(replacement_node);
    tracker.replace_node(sf, flow.node, replacement_node, None);
}

// Go: fixables/missed_pipeable_opportunity.go:110 findSubjectNodeAtDepth
/// findSubjectNodeAtDepth traverses the flow node into arguments to find the subject at the right depth,
/// then deep-clones it.
fn find_subject_node_at_depth(
    tracker: &Tracker,
    flow: &PipingFlow,
    first_pipeable_index: i32,
) -> Node {
    let mut current = flow.node;
    let mut i = flow.transformations.len() as i32;
    while i > first_pipeable_index {
        let t = &flow.transformations[(i - 1) as usize];
        if t.kind == TransformationKind::Call && is_call_expression(current) {
            if current.argument_list().is_some() && !current.arguments().is_empty() {
                current = current.arguments().get(0);
            } else {
                return Node::NIL;
            }
        } else {
            return Node::NIL;
        }
        i -= 1;
    }
    tracker.node_factory().deep_clone_node(current)
}

// Go: fixables/missed_pipeable_opportunity.go:132 wrapWithAfterTransformations
/// wrapWithAfterTransformations wraps an inner node with the "after" transformations.
/// For "call" kind: callee(innerNode)
/// For "pipe"/"pipeable" kind with args: callee(args...)(innerNode) (curried)
/// For "pipe"/"pipeable" kind without args: callee(innerNode)
fn wrap_with_after_transformations(
    tracker: &Tracker,
    inner: Node,
    transformations: &[PipingFlowTransformation],
) -> Node {
    let f = tracker.node_factory();
    let mut result = inner;
    for t in transformations {
        if t.kind == TransformationKind::EffectFn || t.kind == TransformationKind::EffectFnUntraced
        {
            continue;
        }

        let cloned_callee = f.deep_clone_node(t.callee);

        if t.kind == TransformationKind::Call {
            // Single-arg call: callee(result)
            result = f.new_call_expression(
                cloned_callee,
                Node::NIL,
                NodeList::NIL,
                f.new_node_list(&[result]),
                NodeFlags::NONE,
            );
        } else if !t.args.is_empty() {
            // Pipe or pipeable transformation
            // Curried form: callee(args...)(result)
            let cloned_args: Vec<Node> = t.args.iter().map(|&a| f.deep_clone_node(a)).collect();
            let curried_call = f.new_call_expression(
                cloned_callee,
                Node::NIL,
                NodeList::NIL,
                f.new_node_list(&cloned_args),
                NodeFlags::NONE,
            );
            result = f.new_call_expression(
                curried_call,
                Node::NIL,
                NodeList::NIL,
                f.new_node_list(&[result]),
                NodeFlags::NONE,
            );
        } else {
            // Constant: callee(result)
            result = f.new_call_expression(
                cloned_callee,
                Node::NIL,
                NodeList::NIL,
                f.new_node_list(&[result]),
                NodeFlags::NONE,
            );
        }
    }
    result
}
