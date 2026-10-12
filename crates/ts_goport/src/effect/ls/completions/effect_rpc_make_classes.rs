//! Port of Effect-TS/tsgo `internal/completions/effect_rpc_make_classes.go`
//! (effect-tsgo 0.51.1).

use super::effect_schema_self_in_classes::{byte_span_to_range, make_extends_completion_item};
use crate::effect::ls::completion::{
    Completion, CompletionContext, parse_data_for_extends_class_completion,
};
use crate::effect::typeparser::{EffectMajorVersion, find_module_identifier_for_package};
use crate::ls::prelude::*;

// Go: completions/effect_rpc_make_classes.go:14 rpcMakeClasses
/// rpcMakeClasses provides completion items for @effect/rpc Rpc.make
/// when the cursor is in the extends clause of a class declaration.
/// This is a V3-only completion.
pub static RPC_MAKE_CLASSES: Completion = Completion {
    name: "rpcMakeClasses",
    description: "Provides @effect/rpc Rpc.make completions in extends clauses",
    run: run_rpc_make_classes,
};

// Go: completions/effect_rpc_make_classes.go:20 runRpcMakeClasses
fn run_rpc_make_classes(ctx: &mut CompletionContext<'_, '_>) -> Vec<lsproto::CompletionItem> {
    let Some(data) = parse_data_for_extends_class_completion(ctx.source_file, ctx.position) else {
        return Vec::new();
    };

    // V3 only
    let version = ctx.tp.supported_effect_version();
    if version != EffectMajorVersion::V3 {
        return Vec::new();
    }

    let rpc_identifier = find_module_identifier_for_package(ctx.source_file, "@effect/rpc", "Rpc");
    let accessed_text = data.accessed_object_text();

    // Only fully-qualified case (e.g., Rpc.make)
    if rpc_identifier != accessed_text {
        return Vec::new();
    }

    let class_name = data.class_name_text();

    // Build replacement range from byte offsets
    let replacement_range =
        byte_span_to_range(ctx, data.replacement_start, data.replacement_length);

    let sort_text = "11";
    let insert_text = format!(r#"{rpc_identifier}.make("{class_name}", {{${{0}}}}) {{}}"#);

    vec![make_extends_completion_item(
        &accessed_text,
        format!(r#"make("{class_name}")"#),
        insert_text,
        sort_text,
        replacement_range,
    )]
}
