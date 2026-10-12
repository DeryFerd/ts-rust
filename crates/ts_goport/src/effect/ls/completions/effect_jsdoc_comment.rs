//! Port of Effect-TS/tsgo `internal/completions/effect_jsdoc_comment.go`
//! (effect-tsgo 0.51.1).

use super::effect_diagnostics_comment::find_comment_at;
use super::effect_schema_self_in_classes::{byte_span_to_range, make_completion_item};
use crate::effect::ls::completion::{Completion, CompletionContext};
use crate::ls::prelude::*;

// Go: completions/effect_jsdoc_comment.go:10 effectJsdocComment
/// effectJsdocComment provides completion for @effect-identifier
/// when typing @ inside a comment.
pub static EFFECT_JSDOC_COMMENT: Completion = Completion {
    name: "effectJsdocComment",
    description: "Provides @effect-identifier completion inside comments",
    run: run_effect_jsdoc_comment,
};

// Go: completions/effect_jsdoc_comment.go:16 runEffectJsdocComment
fn run_effect_jsdoc_comment(ctx: &mut CompletionContext<'_, '_>) -> Vec<lsproto::CompletionItem> {
    let Some(at_start) = find_comment_at(ctx) else {
        return Vec::new();
    };

    // loc[4] and loc[5] are the start/end byte offsets of the `@` capture group
    let span_length = (ctx.position - at_start).max(0);

    let replacement_range = byte_span_to_range(ctx, at_start, span_length);

    let sort_text = "11";

    vec![make_completion_item(
        "@effect-identifier".to_string(),
        "@effect-identifier".to_string(),
        sort_text,
        replacement_range,
        lsproto::CompletionItemKind::CONSTANT,
    )]
}
