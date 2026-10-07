//! Port of Effect-TS/tsgo `internal/rules/effect_in_failure.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// EffectInFailure detects when an Effect type appears in the failure (E) channel
/// of another Effect. Putting Effect computations in the failure channel is not
/// intended; only failure types should appear there.
// Go: rules/effect_in_failure.go EffectInFailure
pub static EFFECT_IN_FAILURE: Rule = Rule {
    name: "effectInFailure",
    group: "antipattern",
    description: "Warns when an Effect is used inside an Effect failure channel",
    default_severity: Severity::Warning,
    supported_effect: &["v3", "v4"],
    codes: &[377054],
    run: run_effect_in_failure,
};

// Go: rules/effect_in_failure.go stackEntry (local type of the Run closure)
struct StackEntry {
    node: Node,
    visited: bool,
}

fn run_effect_in_failure(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diags = Vec::new();

    // Post-order AST walk using a stack with a visited set.
    // Children are processed before parents so that the
    // shouldSkipBecauseChildMatched mechanism can suppress
    // redundant diagnostics on parent nodes.
    let mut stack = vec![StackEntry {
        node: ctx.source_file,
        visited: false,
    }];
    let mut should_skip: FxHashMap<Node, bool> = FxHashMap::default();

    while let Some(entry) = stack.pop() {
        let node = entry.node;

        // First visit: push self again (marked visited) then push children
        if !entry.visited {
            stack.push(StackEntry {
                node,
                visited: true,
            });
            node.for_each_child(|child| {
                stack.push(StackEntry {
                    node: child,
                    visited: false,
                });
                false
            });
            continue;
        }

        // Second visit (post-order): check the node

        // If a child already matched, propagate skip to parent and continue
        if should_skip.get(&node).copied().unwrap_or(false) {
            if node.parent().is_some() {
                should_skip.insert(node.parent(), true);
            }
            continue;
        }

        // Declared-type prefilter: skip the expensive flow-analysis query
        // for reference nodes that conclusively cannot have a strict
        // Effect flow type. Skipped nodes can never match, so no
        // shouldSkip bookkeeping is needed.
        if !ctx.tp.node_could_be_strict_effect(node) {
            continue;
        }

        let node_type = ctx.tp.get_type_at_location(node);
        if node_type.is_nil() {
            continue;
        }

        let effect = ctx.tp.strict_effect_type(node_type);
        let Some(effect) = effect else {
            continue;
        };

        // Check if any union member of the failure channel (E) is a strict Effect type
        let failure_members = ctx.tp.unroll_union_members(effect.e);
        let member_with_effect =
            super::effect_in_void_success::find_first_strict_effect(ctx.tp, &failure_members);
        if member_with_effect.is_nil() {
            continue;
        }

        let member_text = ctx.tp.checker.type_to_string_exported(member_with_effect);
        let d = ctx.new_diagnostic(
            ctx.source_file,
            ctx.get_error_range(node),
            diag::The_error_channel_contains_an_Effect_0_Putting_Effect_computations_in_the_failure_channel_is_not_intended_keep_only_failure_types_there_effect_effectInFailure,
            Vec::new(),
            args![member_text],
        );
        diags.push(d);

        // Mark parent to skip redundant reporting
        if node.parent().is_some() {
            should_skip.insert(node.parent(), true);
        }
    }

    diags
}
