//! Port of Effect-TS/tsgo `internal/completions/schema_brand.go`
//! (effect-tsgo 0.51.1).

use super::effect_schema_self_in_classes::{byte_span_to_range, make_completion_item};
use super::fn_function_star::find_enclosing_variable_name;
use crate::effect::ls::completion::{
    Completion, CompletionContext, parse_accessed_expression_for_completion,
};
use crate::effect::typeparser::{EffectMajorVersion, find_module_identifier};
use crate::ls::prelude::*;

// Go: completions/schema_brand.go:15 schemaBrand
/// schemaBrand provides a `brand("varName")` completion when dot-accessing the
/// Schema identifier inside a variable declaration. V3-only.
pub static SCHEMA_BRAND: Completion = Completion {
    name: "schemaBrand",
    description: "Provides brand(\"varName\") completion when dot-accessing Schema in variable declarations",
    run: run_schema_brand,
};

// Go: completions/schema_brand.go:21 runSchemaBrand
fn run_schema_brand(ctx: &mut CompletionContext<'_, '_>) -> Vec<lsproto::CompletionItem> {
    let Some(result) = parse_accessed_expression_for_completion(ctx.source_file, ctx.position)
    else {
        return Vec::new();
    };

    if !is_identifier(result.accessed_object) {
        return Vec::new();
    }

    // V3 only
    let version = ctx.tp.supported_effect_version();
    if version != EffectMajorVersion::V3 {
        return Vec::new();
    }

    // Resolve the Schema module identifier and compare
    let schema_identifier = find_module_identifier(ctx.source_file, "Schema");
    let accessed_text = get_text_of_node(result.accessed_object);
    if accessed_text != schema_identifier {
        return Vec::new();
    }

    // Replacement span: from after the dot to the cursor position
    let span_start = result.accessed_object.end() + 1;
    let span_length = (ctx.position - span_start).max(0);

    // Find enclosing variable name
    let var_name = find_enclosing_variable_name(result.outer_node);
    if var_name.is_empty() {
        return Vec::new();
    }

    let replacement_range = byte_span_to_range(ctx, span_start, span_length);
    let sort_text = "11";

    let label = format!(r#"brand("{var_name}")"#);

    vec![make_completion_item(
        label.clone(),
        label,
        sort_text,
        replacement_range,
        lsproto::CompletionItemKind::VARIABLE,
    )]
}
