//! Port of Effect-TS/tsgo `internal/completions/duration_input.go`
//! (effect-tsgo 0.51.1).

use super::effect_schema_self_in_classes::{byte_span_to_range, make_completion_item};
use crate::effect::ls::completion::{Completion, CompletionContext};
use crate::ls::prelude::*;

// Go: completions/duration_input.go:18 durationInput
/// durationInput provides completion items for Duration string literals.
/// When the cursor is inside a string literal whose contextual type is a Duration union
/// (containing template literals with "nanos" text), it offers snippet completions
/// for all 8 duration units.
pub static DURATION_INPUT: Completion = Completion {
    name: "durationInput",
    description: "Provides duration unit completions inside Duration string literals",
    run: run_duration_input,
};

// Go: completions/duration_input.go:24 durationUnits
const DURATION_UNITS: [&str; 8] = [
    "nanos", "micros", "millis", "seconds", "minutes", "hours", "days", "weeks",
];

// Go: completions/duration_input.go:26 runDurationInput
fn run_duration_input(ctx: &mut CompletionContext<'_, '_>) -> Vec<lsproto::CompletionItem> {
    let previous_token = astnav::find_preceding_token(ctx.source_file, ctx.position);
    if previous_token.is_nil() || !is_string_text_containing_node(previous_token) {
        return Vec::new();
    }

    let start = get_token_pos_of_node(previous_token, ctx.source_file, false);
    let end = previous_token.end();

    // The cursor must be strictly inside the string literal content,
    // or at the end position of an unterminated literal.
    let mut is_in_string = start < ctx.position && ctx.position < end;
    if ctx.position == end {
        is_in_string = is_unterminated_literal(previous_token);
    }

    if !is_in_string || !is_expression(previous_token) {
        return Vec::new();
    }

    let ch = &mut *ctx.tp.checker;

    let contextual_type = ch.get_contextual_type_exported(previous_token, ContextFlags::NONE);
    if contextual_type.is_nil() || !ch.ty(contextual_type).flags().intersects(TypeFlags::UNION) {
        return Vec::new();
    }

    // PORT: Go returns the items from inside the loop. The loop reads the
    // checker's types, so the port finds the member first and builds the
    // items after the loop (the same result).
    let is_duration = ch.ty(contextual_type).types().iter().any(|&member| {
        if !ch
            .ty(member)
            .flags()
            .intersects(TypeFlags::TEMPLATE_LITERAL)
        {
            return false;
        }
        let texts = &ch.ty(member).as_template_literal_type().texts;
        // PORT: Go `strings.TrimSpace` trims Unicode White_Space, as `str::trim` does.
        texts.len() == 2 && texts[1].trim() == "nanos"
    });
    if is_duration {
        return build_duration_items(ctx, previous_token);
    }

    Vec::new()
}

// Go: completions/duration_input.go:66 buildDurationItems
fn build_duration_items(
    ctx: &CompletionContext<'_, '_>,
    node: Node,
) -> Vec<lsproto::CompletionItem> {
    // Replacement range covers the string content (between the quotes)
    let start = get_token_pos_of_node(node, ctx.source_file, false) + 1; // after opening quote
    let mut end = node.end() - 1; // before closing quote
    end = end.max(start);
    let replacement_range = byte_span_to_range(ctx, start, end - start);
    let sort_text = "11";

    DURATION_UNITS
        .iter()
        .map(|unit| {
            make_completion_item(
                (*unit).to_string(),
                format!("${{0}} {unit}"),
                sort_text,
                replacement_range,
                lsproto::CompletionItemKind::CONSTANT,
            )
        })
        .collect()
}
