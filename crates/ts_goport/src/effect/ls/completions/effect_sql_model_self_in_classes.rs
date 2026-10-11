//! Port of Effect-TS/tsgo `internal/completions/effect_sql_model_self_in_classes.go`
//! (effect-tsgo 0.51.1).

use super::effect_schema_self_in_classes::{byte_span_to_range, make_extends_completion_item};
use crate::effect::ls::completion::{
    Completion, CompletionContext, parse_data_for_extends_class_completion,
};
use crate::effect::typeparser::{EffectMajorVersion, find_module_identifier_for_package, member};
use crate::ls::prelude::*;

// Go: completions/effect_sql_model_self_in_classes.go:14 effectSqlModelSelfInClasses
/// effectSqlModelSelfInClasses provides completion items for @effect/sql Model.Class
/// when the cursor is in the extends clause of a class declaration.
/// This is a V3-only completion.
pub static EFFECT_SQL_MODEL_SELF_IN_CLASSES: Completion = Completion {
    name: "effectSqlModelSelfInClasses",
    description: "Provides @effect/sql Model.Class completions in extends clauses",
    run: run_effect_sql_model_self_in_classes,
};

// Go: completions/effect_sql_model_self_in_classes.go:20 runEffectSqlModelSelfInClasses
fn run_effect_sql_model_self_in_classes(
    ctx: &mut CompletionContext<'_, '_>,
) -> Vec<lsproto::CompletionItem> {
    let Some(data) = parse_data_for_extends_class_completion(ctx.source_file, ctx.position) else {
        return Vec::new();
    };

    // V3 only
    let version = ctx.tp.supported_effect_version();
    if version != EffectMajorVersion::V3 {
        return Vec::new();
    }

    let model_identifier =
        find_module_identifier_for_package(ctx.source_file, "@effect/sql", "Model");
    let accessed_text = data.accessed_object_text();
    let is_fully_qualified = model_identifier == accessed_text;
    let class_name = data.class_name_text();

    // For non-fully-qualified: validate with IsNodeReferenceToEffectSqlModelModuleApi
    if !is_fully_qualified
        && !ctx.tp.is_node_reference_to_effect_sql_model_module_api(
            data.accessed_object,
            member!("Class"),
        )
    {
        return Vec::new();
    }

    // Build replacement range from byte offsets
    let replacement_range =
        byte_span_to_range(ctx, data.replacement_start, data.replacement_length);

    let sort_text = "11";

    let insert_text = if is_fully_qualified {
        format!(r#"{model_identifier}.Class<{class_name}>("{class_name}")({{${{0}}}}){{}}"#)
    } else {
        format!(r#"Class<{class_name}>("{class_name}")({{${{0}}}}){{}}"#)
    };

    vec![make_extends_completion_item(
        &accessed_text,
        format!("Class<{class_name}>"),
        insert_text,
        sort_text,
        replacement_range,
    )]
}
