//! Port of Effect-TS/tsgo `internal/refactors/wrap_with_pipe.go`.

use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::with_kind;
use crate::ls::CodeAction;

// Go: refactors/wrap_with_pipe.go:9 WrapWithPipe
pub static WRAP_WITH_PIPE: Refactor = Refactor {
    name: "wrapWithPipe",
    description: "Wrap with pipe",
    kind: "rewrite.effect.wrapWithPipe",
    run: run_wrap_with_pipe,
};

// Go: refactors/wrap_with_pipe.go:16 runWrapWithPipe
fn run_wrap_with_pipe(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    // Only applicable when the selection is non-empty.
    if ctx.span.pos() == ctx.span.end() {
        return Vec::new();
    }

    let start_pos = ctx.byte_pos_to_lsp_position(ctx.span.pos());
    let end_pos = ctx.byte_pos_to_lsp_position(ctx.span.end());

    let sf = ctx.source_file;
    let action = ctx.new_refactor_action("Wrap with pipe", |tracker| {
        tracker.insert_text(sf, start_pos, "pipe(");
        tracker.insert_text(sf, end_pos, ")");
    });
    with_kind(action, "refactor.rewrite.effect.wrapWithPipe")
}
