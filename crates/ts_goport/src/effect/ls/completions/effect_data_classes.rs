//! Port of Effect-TS/tsgo `internal/completions/effect_data_classes.go`
//! (effect-tsgo 0.51.1).

use super::effect_schema_self_in_classes::{byte_span_to_range, make_extends_completion_item};
use crate::effect::ls::completion::{
    Completion, CompletionContext, parse_data_for_extends_class_completion,
};
use crate::effect::typeparser::{find_module_identifier, member};
use crate::ls::prelude::*;

// Go: completions/effect_data_classes.go:14 effectDataClasses
/// effectDataClasses provides completion items for Data.TaggedError and Data.TaggedClass
/// when the cursor is in the extends clause of a class declaration.
/// For example, typing `class Foo extends Data.|` will suggest `TaggedError("Foo")` and `TaggedClass("Foo")`.
pub static EFFECT_DATA_CLASSES: Completion = Completion {
    name: "effectDataClasses",
    description: "Provides Data.TaggedError and Data.TaggedClass completions in extends clauses",
    run: run_effect_data_classes,
};

// Go: completions/effect_data_classes.go:20 runEffectDataClasses
fn run_effect_data_classes(ctx: &mut CompletionContext<'_, '_>) -> Vec<lsproto::CompletionItem> {
    let Some(data) = parse_data_for_extends_class_completion(ctx.source_file, ctx.position) else {
        return Vec::new();
    };

    let data_identifier = find_module_identifier(ctx.source_file, "Data");
    let accessed_text = data.accessed_object_text();
    let is_fully_qualified = data_identifier == accessed_text;
    let class_name = data.class_name_text();

    // Build replacement range from byte offsets
    let replacement_range =
        byte_span_to_range(ctx, data.replacement_start, data.replacement_length);

    let sort_text = "11";
    let mut items = Vec::new();

    // Data.TaggedError
    if is_fully_qualified
        || ctx.tp.is_node_reference_to_effect_data_module_api(
            data.accessed_object,
            member!("TaggedError"),
        )
    {
        let insert_text = if is_fully_qualified {
            format!(r#"{data_identifier}.TaggedError("{class_name}")<{{${{0}}}}>{{}}"#)
        } else {
            format!(r#"TaggedError("{class_name}")<{{${{0}}}}>{{}}"#)
        };
        items.push(make_extends_completion_item(
            &accessed_text,
            format!(r#"TaggedError("{class_name}")"#),
            insert_text,
            sort_text,
            replacement_range,
        ));
    }

    // Data.TaggedClass
    if is_fully_qualified
        || ctx.tp.is_node_reference_to_effect_data_module_api(
            data.accessed_object,
            member!("TaggedClass"),
        )
    {
        let insert_text = if is_fully_qualified {
            format!(r#"{data_identifier}.TaggedClass("{class_name}")<{{${{0}}}}>{{}}"#)
        } else {
            format!(r#"TaggedClass("{class_name}")<{{${{0}}}}>{{}}"#)
        };
        items.push(make_extends_completion_item(
            &accessed_text,
            format!(r#"TaggedClass("{class_name}")"#),
            insert_text,
            sort_text,
            replacement_range,
        ));
    }

    items
}
