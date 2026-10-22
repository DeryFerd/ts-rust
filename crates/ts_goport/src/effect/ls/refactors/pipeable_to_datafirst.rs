//! Port of Effect-TS/tsgo `internal/refactors/pipeable_to_datafirst.go`.

use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::with_kind;
use crate::effect::typeparser::{ParsedPipeCallResult, TransformationKind};
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: refactors/pipeable_to_datafirst.go:13 PipeableToDatafirst
pub static PIPEABLE_TO_DATAFIRST: Refactor = Refactor {
    name: "pipeableToDatafirst",
    description: "Rewrite to datafirst",
    kind: "rewrite.effect.pipeableToDatafirst",
    run: run_pipeable_to_datafirst,
};

// Go: refactors/pipeable_to_datafirst.go:20 runPipeableToDatafirst
fn run_pipeable_to_datafirst(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let token = astnav::get_token_at_position(ctx.source_file, ctx.span.pos());
    if token.is_nil() {
        return Vec::new();
    }

    // Walk up the ancestor chain looking for a pipe(...) call
    let mut node = token;
    while node.is_some() {
        let current = node;
        node = node.parent();
        if current.kind() != SyntaxKind::CallExpression {
            continue;
        }

        let Some(pipe_call) = ctx.tp.parse_pipe_call(current) else {
            continue;
        };

        // Only applies to pipe() calls (not .pipe())
        if pipe_call.kind != TransformationKind::Pipe {
            continue;
        }

        // The pipe identifier must be within the selection range
        // PORT: Go's `callExpr == nil` cannot happen for a call expression.
        let callee = current.expression();
        if callee.is_nil() {
            continue;
        }
        let expr_pos = callee.pos();
        let expr_end = callee.end();
        if expr_pos > ctx.span.end() || expr_end < ctx.span.pos() {
            continue;
        }

        // Need at least one argument after the subject
        if pipe_call.args.is_empty() {
            continue;
        }

        // Try converting pipe args to data-first style
        let result = try_convert_to_datafirst(&pipe_call, ctx, current);
        if result.is_empty() {
            continue;
        }

        return result;
    }

    Vec::new()
}

// Go: refactors/pipeable_to_datafirst.go:75 conversionStep
struct ConversionStep {
    is_data_first: bool,
    /// original arg node
    arg: Node,
}

// Go: refactors/pipeable_to_datafirst.go:72 tryConvertToDatafirst
// PORT: Go returns nil for "not applicable" and when the action has no
// edits; both are an empty list here, and the caller goes on to the parent
// in both cases, as Go does.
fn try_convert_to_datafirst(
    pipe_call: &ParsedPipeCallResult,
    ctx: &mut RefactorContext<'_, '_>,
    node: Node,
) -> Vec<CodeAction> {
    // Accumulate: start with the subject, then process each pipe argument
    // Track whether we successfully converted at least one step
    let mut steps = Vec::with_capacity(pipe_call.args.len());
    let mut did_something = false;

    for &arg in &pipe_call.args {
        let mut is_data_first = false;
        if arg.kind() == SyntaxKind::CallExpression && arg.expression().is_some() {
            let expr_type = ctx.tp.get_type_at_location(arg.expression());
            if expr_type.is_some() {
                let c = &mut *ctx.tp.checker;
                let call_sigs = c.get_signatures_of_type(expr_type, SignatureKind::CALL);
                let arg_count = arg.arguments().len();
                for &sig in call_sigs.iter() {
                    if c.sig(sig).parameters().len() == arg_count + 1 {
                        is_data_first = true;
                        did_something = true;
                        break;
                    }
                }
            }
        }
        steps.push(ConversionStep { is_data_first, arg });
    }

    if !did_something {
        return Vec::new();
    }

    let sf = ctx.source_file;
    let action = ctx.new_refactor_action("Rewrite to datafirst", |tracker| {
        let f = tracker.node_factory();
        // Build the replacement node by accumulating from the subject
        let mut new_node = f.deep_clone_node(pipe_call.subject);

        for step in &steps {
            if step.is_data_first {
                // Convert: callee(args...) + self -> callee(self, args...)
                let arg_call = step.arg;
                let cloned_callee = f.deep_clone_node(arg_call.expression());

                let mut all_args = Vec::with_capacity(1 + arg_call.arguments().len());
                all_args.push(new_node);
                for a in arg_call.arguments().iter() {
                    all_args.push(f.deep_clone_node(a));
                }

                let call_expr = f.new_call_expression(
                    cloned_callee,
                    Node::NIL,
                    NodeList::NIL,
                    f.new_node_list(&all_args),
                    NodeFlags::NONE,
                );
                set_parent_in_children(call_expr);
                new_node = call_expr;
            } else if is_pipe_call_node(new_node) {
                // Not data-first: keep in pipe form
                // If newNode is already a pipe call, extend it
                let mut existing_args = new_node.arguments().to_vec();
                existing_args.push(f.deep_clone_node(step.arg));

                let pipe_id = f.new_identifier("pipe");
                let call_expr = f.new_call_expression(
                    pipe_id,
                    Node::NIL,
                    NodeList::NIL,
                    f.new_node_list(&existing_args),
                    NodeFlags::NONE,
                );
                set_parent_in_children(call_expr);
                new_node = call_expr;
            } else {
                // Wrap in pipe(self, arg)
                let pipe_id = f.new_identifier("pipe");
                let pipe_args = [new_node, f.deep_clone_node(step.arg)];
                let call_expr = f.new_call_expression(
                    pipe_id,
                    Node::NIL,
                    NodeList::NIL,
                    f.new_node_list(&pipe_args),
                    NodeFlags::NONE,
                );
                set_parent_in_children(call_expr);
                new_node = call_expr;
            }
        }

        tracker.replace_node(sf, node, new_node, None);
    });

    with_kind(action, "refactor.rewrite.effect.pipeableToDatafirst")
}

// Go: refactors/pipeable_to_datafirst.go:177 isPipeCallNode
// isPipeCallNode checks if a synthesized node is a pipe(...) call by checking if the
// expression is an identifier named "pipe".
fn is_pipe_call_node(node: Node) -> bool {
    if node.is_nil() || node.kind() != SyntaxKind::CallExpression {
        return false;
    }
    let callee = node.expression();
    if callee.is_nil() || callee.kind() != SyntaxKind::Identifier {
        return false;
    }
    callee.text() == "pipe"
}
