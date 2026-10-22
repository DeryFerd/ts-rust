//! Port of Effect-TS/tsgo `internal/fixables/unnecessary_pipe.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::unnecessary_pipe::analyze_unnecessary_pipe;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/unnecessary_pipe.go:12 UnnecessaryPipeFix
pub static UNNECESSARY_PIPE_FIX: Fixable = Fixable {
    name: "unnecessaryPipe",
    description: "Remove the pipe call",
    // Go: tsdiag.This_pipe_call_contains_no_arguments_effect_unnecessaryPipe
    error_codes: &[377013],
    fix_ids: &["unnecessaryPipe_fix"],
    run: run_unnecessary_pipe_fix,
};

// Go: fixables/unnecessary_pipe.go:20 runUnnecessaryPipeFix
fn run_unnecessary_pipe_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_unnecessary_pipe(ctx.tp, sf);

    let Some(m) = matches
        .iter()
        .find(|m| m.location.intersects(ctx.span) || ctx.span.contained_by(m.location))
    else {
        return Vec::new();
    };

    let result = &m.result;
    let call_node = result.node;

    // Unwrap "pipe(subject)" or "subject.pipe()" to just "subject" by deleting the prefix and suffix around the subject.
    if let Some(action) = ctx.new_fix_action("Remove the pipe call".to_string(), |tracker| {
        tracker.delete_range(sf, TextRange::new(call_node.pos(), result.subject.pos()));
        tracker.delete_range(sf, TextRange::new(result.subject.end(), call_node.end()));
    }) {
        return vec![action];
    }
    Vec::new()
}
