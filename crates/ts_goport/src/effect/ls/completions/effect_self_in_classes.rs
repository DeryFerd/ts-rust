//! Port of Effect-TS/tsgo `internal/completions/effect_self_in_classes.go`
//! (effect-tsgo 0.51.1).

use super::context_self_in_classes::compute_service_tag_key;
use super::effect_schema_self_in_classes::{byte_span_to_range, make_extends_completion_item};
use crate::effect::ls::completion::{
    Completion, CompletionContext, parse_data_for_extends_class_completion,
};
use crate::effect::typeparser::{EffectMajorVersion, find_module_identifier, member};
use crate::ls::prelude::*;

// Go: completions/effect_self_in_classes.go:14 effectSelfInClasses
/// effectSelfInClasses provides completion items for Effect.Service and Effect.Tag class constructors
/// when the cursor is in the extends clause of a class declaration.
/// This is a V3-only completion.
pub static EFFECT_SELF_IN_CLASSES: Completion = Completion {
    name: "effectSelfInClasses",
    description: "Provides Effect.Service/Effect.Tag completions in extends clauses",
    run: run_effect_self_in_classes,
};

// Go: completions/effect_self_in_classes.go:20 runEffectSelfInClasses
fn run_effect_self_in_classes(ctx: &mut CompletionContext<'_, '_>) -> Vec<lsproto::CompletionItem> {
    let Some(data) = parse_data_for_extends_class_completion(ctx.source_file, ctx.position) else {
        return Vec::new();
    };

    // V3 only
    let version = ctx.tp.supported_effect_version();
    if version != EffectMajorVersion::V3 {
        return Vec::new();
    }

    let effect_identifier = find_module_identifier(ctx.source_file, "Effect");
    let accessed_text = data.accessed_object_text();
    let is_fully_qualified = effect_identifier == accessed_text;
    let class_name = data.class_name_text();

    // Compute deterministic tag key
    let tag_key = compute_service_tag_key(ctx.program, ctx.tp, ctx.source_file, &class_name);

    // Build replacement range from byte offsets
    let replacement_range =
        byte_span_to_range(ctx, data.replacement_start, data.replacement_length);

    let sort_text = "11";
    let mut items = Vec::new();

    // Service: Effect.Service<ClassName>()("tagKey", {}){}
    if is_fully_qualified
        || ctx
            .tp
            .is_node_reference_to_effect_module_api(data.accessed_object, member!("Service"))
    {
        let insert_text = if is_fully_qualified {
            format!(r#"{effect_identifier}.Service<{class_name}>()("{tag_key}", {{${{0}}}}){{}}"#)
        } else {
            format!(r#"Service<{class_name}>()("{tag_key}", {{${{0}}}}){{}}"#)
        };
        items.push(make_extends_completion_item(
            &accessed_text,
            format!("Service<{class_name}>"),
            insert_text,
            sort_text,
            replacement_range,
        ));
    }

    // Tag: Effect.Tag("tagKey")<ClassName, {}>(){}
    if is_fully_qualified
        || ctx
            .tp
            .is_node_reference_to_effect_module_api(data.accessed_object, member!("Tag"))
    {
        let insert_text = if is_fully_qualified {
            format!(r#"{effect_identifier}.Tag("{tag_key}")<{class_name}, {{${{0}}}}>(){{}}"#)
        } else {
            format!(r#"Tag("{tag_key}")<{class_name}, {{${{0}}}}>(){{}}"#)
        };
        items.push(make_extends_completion_item(
            &accessed_text,
            format!(r#"Tag("{class_name}")"#),
            insert_text,
            sort_text,
            replacement_range,
        ));
    }

    items
}
