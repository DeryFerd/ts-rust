//! Port of Effect-TS/tsgo `internal/fixables/unnecessary_pipe_chain.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::unnecessary_pipe_chain::analyze_unnecessary_pipe_chain;
use crate::effect::typeparser::TransformationKind;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/unnecessary_pipe_chain.go:13 UnnecessaryPipeChainFix
pub static UNNECESSARY_PIPE_CHAIN_FIX: Fixable = Fixable {
    name: "unnecessaryPipeChain",
    description: "Rewrite as single pipe call",
    // Go: tsdiag.This_expression_contains_chained_pipe_calls_that_can_be_simplified_to_a_single_pipe_call_effect_unnecessaryPipeChain
    error_codes: &[377015],
    fix_ids: &["unnecessaryPipeChain_fix"],
    run: run_unnecessary_pipe_chain_fix,
};

// Go: fixables/unnecessary_pipe_chain.go:21 runUnnecessaryPipeChainFix
fn run_unnecessary_pipe_chain_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_unnecessary_pipe_chain(ctx.tp, sf);

    let Some(m) = matches
        .iter()
        .find(|m| m.location.intersects(ctx.span) || ctx.span.contained_by(m.location))
    else {
        return Vec::new();
    };

    let outer = &m.outer;
    let inner = &m.inner;

    if let Some(action) = ctx.new_fix_action("Rewrite as single pipe call".to_string(), |tracker| {
        let f = tracker.node_factory();
        // Collect all arguments: deep-clone inner args then outer args
        let mut all_args = Vec::with_capacity(inner.args.len() + outer.args.len());
        for &arg in &inner.args {
            all_args.push(f.deep_clone_node(arg));
        }
        for &arg in &outer.args {
            all_args.push(f.deep_clone_node(arg));
        }

        let replacement_node = match inner.kind {
            TransformationKind::Pipe => {
                // pipe(subject, f1, f2) + pipe(..., f3) => pipe(subject, f1, f2, f3)
                // Deep-clone the original callee (bare `pipe` or `Function.pipe`)
                let cloned_callee = f.deep_clone_node(inner.node.expression());
                // Build args: subject first, then all pipe args
                let mut call_args = Vec::with_capacity(1 + all_args.len());
                call_args.push(f.deep_clone_node(inner.subject));
                call_args.extend(all_args);
                f.new_call_expression(
                    cloned_callee,
                    Node::NIL,
                    NodeList::NIL,
                    f.new_node_list(&call_args),
                    NodeFlags::NONE,
                )
            }
            TransformationKind::Pipeable => {
                // subject.pipe(f1, f2).pipe(f3) => subject.pipe(f1, f2, f3)
                let cloned_subject = f.deep_clone_node(inner.subject);
                let pipe_access = f.new_property_access_expression(
                    cloned_subject,
                    Node::NIL,
                    f.new_identifier("pipe"),
                    NodeFlags::NONE,
                );
                f.new_call_expression(
                    pipe_access,
                    Node::NIL,
                    NodeList::NIL,
                    f.new_node_list(&all_args),
                    NodeFlags::NONE,
                )
            }
            _ => return,
        };

        set_parent_in_children(replacement_node);
        tracker.replace_node(sf, outer.node, replacement_node, None);
    }) {
        return vec![action];
    }
    Vec::new()
}
