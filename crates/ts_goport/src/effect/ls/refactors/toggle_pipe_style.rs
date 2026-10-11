//! Port of Effect-TS/tsgo `internal/refactors/toggle_pipe_style.go`.

use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::with_kind;
use crate::effect::typeparser::TransformationKind;
use crate::ls::CodeAction;
use crate::lsp::lsproto;
use crate::prelude::*;

// Go: refactors/toggle_pipe_style.go:16 TogglePipeStyle
pub static TOGGLE_PIPE_STYLE: Refactor = Refactor {
    name: "togglePipeStyle",
    description: "Toggle pipe style",
    kind: "rewrite.effect.togglePipeStyle",
    run: run_toggle_pipe_style,
};

// Go: refactors/toggle_pipe_style.go:23 runTogglePipeStyle
fn run_toggle_pipe_style(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let token = astnav::get_token_at_position(ctx.source_file, ctx.span.pos());
    if token.is_nil() {
        return Vec::new();
    }

    // Walk up the ancestor chain looking for a pipe call
    let sf = ctx.source_file;
    let mut node = token;
    while node.is_some() {
        if node.kind() != SyntaxKind::CallExpression {
            node = node.parent();
            continue;
        }

        let Some(pipe_call) = ctx.tp.parse_pipe_call(node) else {
            node = node.parent();
            continue;
        };

        let (description, rewritten) = match pipe_call.kind {
            TransformationKind::Pipe => {
                // pipe(subject, f1, f2) -> subject.pipe(f1, f2)
                // Check that the subject's type is pipeable
                let subject_type = ctx.tp.get_type_at_location(pipe_call.subject);
                if !ctx.tp.is_pipeable_type(subject_type) {
                    node = node.parent();
                    continue;
                }
                (
                    "Rewrite as X.pipe(Y, Z, ...)",
                    toggle_pipe_to_method_text(sf, pipe_call.subject, &pipe_call.args),
                )
            }
            TransformationKind::Pipeable => {
                // subject.pipe(f1, f2) -> pipe(subject, f1, f2)
                (
                    "Rewrite as pipe(X, Y, Z, ...)",
                    toggle_pipe_to_function_text(sf, pipe_call.subject, &pipe_call.args),
                )
            }
            // PORT: Go's switch has no case for the other kinds, so it
            // goes on to the parent.
            _ => {
                node = node.parent();
                continue;
            }
        };

        let start = astnav::get_start_of_node(node, sf, false);
        let range = lsproto::Range {
            start: ctx.byte_pos_to_lsp_position(start),
            end: ctx.byte_pos_to_lsp_position(node.end()),
        };
        let action = ctx.new_refactor_action(description, |tracker| {
            tracker.replace_range_with_text(sf, range, &rewritten);
        });
        return with_kind(action, "refactor.rewrite.effect.togglePipeStyle");
    }

    Vec::new()
}

// Go: refactors/toggle_pipe_style.go:90 togglePipeToMethodText
fn toggle_pipe_to_method_text(sf: Node, subject: Node, args: &[Node]) -> String {
    let parts: Vec<String> = args
        .iter()
        .map(|&arg| get_source_text_of_node_from_source_file(sf, arg, false))
        .collect();
    get_source_text_of_node_from_source_file(sf, subject, false)
        + ".pipe("
        + &parts.join(", ")
        + ")"
}

// Go: refactors/toggle_pipe_style.go:98 togglePipeToFunctionText
fn toggle_pipe_to_function_text(sf: Node, subject: Node, args: &[Node]) -> String {
    let mut parts = Vec::with_capacity(args.len() + 1);
    parts.push(get_source_text_of_node_from_source_file(sf, subject, false));
    for &arg in args {
        parts.push(get_source_text_of_node_from_source_file(sf, arg, false));
    }
    "pipe(".to_string() + &parts.join(", ") + ")"
}
