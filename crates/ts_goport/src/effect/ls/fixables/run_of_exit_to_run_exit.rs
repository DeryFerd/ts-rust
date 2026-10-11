//! Port of Effect-TS/tsgo `internal/fixables/run_of_exit_to_run_exit.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::replace_effect_method_callee;
use crate::effect::ls::rewriter::Tracker;
use crate::effect::rules::run_of_exit_to_run_exit::analyze_run_of_exit_to_run_exit;
use crate::effect::typeparser::{PipingFlowTransformation, TransformationKind};
use crate::ls::CodeAction;
use crate::prelude::*;
use crate::scanner_util::get_token_pos_of_node;

// Go: fixables/run_of_exit_to_run_exit.go:15 RunOfExitToRunExitFix
pub static RUN_OF_EXIT_TO_RUN_EXIT_FIX: Fixable = Fixable {
    name: "runOfExitToRunExit",
    description: "Replace with the dedicated Effect Exit runner",
    // Go: tsdiag.Effect_0_of_Effect_exit_re_implements_Effect_1_Use_the_dedicated_Exit_runner_directly_effect_runOfExitToRunExit
    error_codes: &[377123],
    fix_ids: &["runOfExitToRunExit_fix"],
    run: run_run_of_exit_to_run_exit_fix,
};

// Go: fixables/run_of_exit_to_run_exit.go:25 runRunOfExitToRunExitFix
// PORT: Go also skips a match with a nil `ExitTransformation`; the Rust
// match always has one.
fn run_run_of_exit_to_run_exit_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;
    for m in analyze_run_of_exit_to_run_exit(ctx.tp, sf) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        if m.runner_callee.is_nil() {
            continue;
        }

        let description = format!("Replace with Effect.{}", m.replacement_name);
        if let Some(action) = ctx.new_fix_action(description, |tracker| {
            if !remove_exit_transformation(tracker, sf, &m.exit_transformation) {
                return;
            }
            replace_effect_method_callee(
                tracker,
                sf,
                m.runner_callee,
                m.runner_name_node,
                &m.replacement_name,
            );
        }) {
            return vec![action];
        }
    }

    Vec::new()
}

// Go: fixables/run_of_exit_to_run_exit.go:52 removeExitTransformation
// PORT: Go's nil tracker, file and transformation checks are gone: Rust
// references are never nil.
fn remove_exit_transformation(
    tracker: &mut Tracker,
    sf: Node,
    transformation: &PipingFlowTransformation,
) -> bool {
    if sf.is_nil() || transformation.callee.is_nil() {
        return false;
    }

    match transformation.kind {
        TransformationKind::DataFirst | TransformationKind::DataLast | TransformationKind::Call => {
            let call_node = direct_call_for_callee(transformation.callee);
            if call_node.is_nil()
                || call_node.argument_list().is_nil()
                || call_node.arguments().len() != 1
            {
                return false;
            }
            let replacement = tracker
                .node_factory()
                .deep_clone_node(call_node.arguments().get(0));
            tracker.replace_node(sf, call_node, replacement, None);
            true
        }
        TransformationKind::Pipe | TransformationKind::Pipeable => {
            let (call_node, argument_index) =
                containing_call_argument_for_exit(transformation.callee);
            if call_node.is_nil() || call_node.argument_list().is_nil() || argument_index < 0 {
                return false;
            }
            let arguments = call_node.arguments();
            let argument_index = argument_index as usize;
            let minimum_arguments = if transformation.kind == TransformationKind::Pipe {
                2 // Function.pipe also contains its subject.
            } else {
                1
            };
            if arguments.len() == minimum_arguments {
                let mut subject = Node::NIL;
                if transformation.kind == TransformationKind::Pipe {
                    subject = arguments.get(0);
                } else if call_node.expression().is_some()
                    && call_node.expression().kind() == SyntaxKind::PropertyAccessExpression
                {
                    subject = call_node.expression().expression();
                }
                if subject.is_nil() {
                    return false;
                }
                let replacement = tracker.node_factory().deep_clone_node(subject);
                tracker.replace_node(sf, call_node, replacement, None);
                return true;
            }

            if argument_index < arguments.len() - 1 {
                let start = get_token_pos_of_node(arguments.get(argument_index), sf, false);
                let end = get_token_pos_of_node(arguments.get(argument_index + 1), sf, false);
                tracker.delete_range(sf, TextRange::new(start, end));
                return true;
            }
            if argument_index > 0 {
                tracker.delete_range(
                    sf,
                    TextRange::new(
                        arguments.get(argument_index - 1).end(),
                        arguments.get(argument_index).end(),
                    ),
                );
                return true;
            }
            false
        }
        _ => false,
    }
}

// Go: fixables/run_of_exit_to_run_exit.go:105 directCallForCallee
// PORT: Go also returns the `*ast.CallExpression` view of the call node.
fn direct_call_for_callee(callee: Node) -> Node {
    if callee.is_nil()
        || callee.parent().is_nil()
        || callee.parent().kind() != SyntaxKind::CallExpression
    {
        return Node::NIL;
    }
    let call = callee.parent();
    if call.expression() != callee {
        return Node::NIL;
    }
    call
}

// Go: fixables/run_of_exit_to_run_exit.go:116 containingCallArgumentForExit
// PORT: Go also returns the `*ast.CallExpression` view of the call node.
fn containing_call_argument_for_exit(node: Node) -> (Node, i32) {
    let mut child = node;
    while child.is_some() && child.parent().is_some() {
        let parent = child.parent();
        if parent.kind() == SyntaxKind::CallExpression && parent.argument_list().is_some() {
            for (index, argument) in parent.arguments().iter().enumerate() {
                if argument == child {
                    return (parent, index as i32);
                }
            }
        }
        child = parent;
    }
    (Node::NIL, -1)
}
