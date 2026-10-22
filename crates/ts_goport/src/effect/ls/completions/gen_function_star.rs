//! Port of Effect-TS/tsgo `internal/completions/gen_function_star.go`
//! (effect-tsgo 0.51.1).

use super::effect_schema_self_in_classes::{byte_span_to_range, make_completion_item};
use crate::effect::ls::completion::{
    Completion, CompletionContext, parse_accessed_expression_for_completion,
};
use crate::ls::prelude::*;

// Go: completions/gen_function_star.go:11 genFunctionStar
/// genFunctionStar provides a completion for `gen(function*(){})` when dot-accessing
/// an object that has a callable `gen` property (e.g., `Effect.gen`, `Micro.gen`).
pub static GEN_FUNCTION_STAR: Completion = Completion {
    name: "genFunctionStar",
    description: "Provides gen(function*(){}) completion when accessing an object with a callable gen property",
    run: run_gen_function_star,
};

// Go: completions/gen_function_star.go:17 runGenFunctionStar
fn run_gen_function_star(ctx: &mut CompletionContext<'_, '_>) -> Vec<lsproto::CompletionItem> {
    let Some(result) = parse_accessed_expression_for_completion(ctx.source_file, ctx.position)
    else {
        return Vec::new();
    };

    let t = ctx.tp.get_type_at_location(result.accessed_object);
    if t.is_nil() {
        return Vec::new();
    }

    let ch = &mut *ctx.tp.checker;
    let gen_symbol = ch.get_property_of_type_exported(t, "gen");
    if gen_symbol.is_nil() {
        return Vec::new();
    }

    let gen_type = ch.get_type_of_symbol_at_location(gen_symbol, result.accessed_object);
    let call_sigs = ch.get_signatures_of_type_exported(gen_type, SignatureKind::CALL);
    if call_sigs.is_empty() {
        return Vec::new();
    }

    // Replacement span: from after the dot to the cursor position
    // This matches the reference: span starts at accessedObject.end + 1 (after the dot)
    let accessed_end = result.accessed_object.end();
    let span_start = accessed_end + 1;
    let span_length = (ctx.position - span_start).max(0);

    let replacement_range = byte_span_to_range(ctx, span_start, span_length);
    let sort_text = "11";

    vec![make_completion_item(
        "gen(function*(){})".to_string(),
        "gen(function*(){${0}})".to_string(),
        sort_text,
        replacement_range,
        lsproto::CompletionItemKind::VARIABLE,
    )]
}
