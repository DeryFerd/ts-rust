//! Port of Go `transformers/estransforms/definitions.go`.
//!
//! PORT: Go builds the chained factories as package-level `var`s with
//! `transformers.Chain`. Here each one is a named factory fn that calls
//! `chain` with its components.

use super::async_::new_async_transformer;
use super::class_fields::new_class_fields_transformer;
use super::contract::{TransformOptions, TransformerBox, chain};
use super::es_decorator::new_es_decorator_transformer;
use super::exponentiation::new_exponentiation_transformer;
use super::for_await::new_forawait_transformer;
use super::logical_assignment::new_logical_assignment_transformer;
use super::nullish_coalescing::new_nullish_coalescing_transformer;
use super::object_rest_spread::new_object_rest_spread_transformer;
use super::optional_catch::new_optional_catch_transformer;
use super::optional_chain::new_optional_chain_transformer;
use super::tagged_template::new_tagged_template_lift_restriction_transformer;
use super::using::new_using_declaration_transformer;
use crate::prelude::*;

// Go: transformers/estransforms/definitions.go:9 esDecoratorAndClassFields
fn es_decorator_and_class_fields(opts: &TransformOptions) -> Option<TransformerBox> {
    chain(
        opts,
        &[&new_es_decorator_transformer, &new_class_fields_transformer],
    )
}

// Go: transformers/estransforms/definitions.go:10 NewESNextTransformer
pub fn new_es_next_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    chain(
        opts,
        &[
            &new_using_declaration_transformer,
            &es_decorator_and_class_fields,
        ],
    )
}

// 2025: only module system syntax (import attributes, json modules), untransformed regex modifiers
// 2024: no new downlevel syntax
// 2023: no new downlevel syntax
// 2022: class static blocks and class fields are handled by newClassFieldsTransformer

// Go: transformers/estransforms/definitions.go:15 NewES2021Transformer
pub fn new_es2021_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    chain(
        opts,
        &[
            &new_es_next_transformer,
            &new_logical_assignment_transformer,
        ],
    )
}

// Go: transformers/estransforms/definitions.go:16 NewES2020Transformer
pub fn new_es2020_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    chain(
        opts,
        &[
            &new_es2021_transformer,
            &new_nullish_coalescing_transformer,
            &new_optional_chain_transformer,
        ],
    )
}

// Go: transformers/estransforms/definitions.go:17 NewES2019Transformer
pub fn new_es2019_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    chain(
        opts,
        &[&new_es2020_transformer, &new_optional_catch_transformer],
    )
}

// Go: transformers/estransforms/definitions.go:18 NewES2018Transformer
pub fn new_es2018_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    chain(
        opts,
        &[
            &new_es2019_transformer,
            &new_object_rest_spread_transformer,
            &new_forawait_transformer,
            &new_tagged_template_lift_restriction_transformer,
        ],
    )
}

// Go: transformers/estransforms/definitions.go:19 NewES2017Transformer
pub fn new_es2017_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    chain(opts, &[&new_es2018_transformer, &new_async_transformer])
}

// Go: transformers/estransforms/definitions.go:20 NewES2016Transformer
pub fn new_es2016_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    chain(
        opts,
        &[&new_es2017_transformer, &new_exponentiation_transformer],
    )
}

// Go: transformers/estransforms/definitions.go:23 GetESTransformer
pub fn get_es_transformer(opts: &TransformOptions) -> Option<TransformerBox> {
    let options = opts.compiler_options;
    match options.get_emit_script_target() {
        ScriptTarget::ES_NEXT => es_decorator_and_class_fields(opts),
        ScriptTarget::ES2025
        | ScriptTarget::ES2024
        | ScriptTarget::ES2023
        | ScriptTarget::ES2022
        | ScriptTarget::ES2021 => new_es_next_transformer(opts),
        ScriptTarget::ES2020 => new_es2021_transformer(opts),
        ScriptTarget::ES2019 => new_es2020_transformer(opts),
        ScriptTarget::ES2018 => new_es2019_transformer(opts),
        ScriptTarget::ES2017 => new_es2018_transformer(opts),
        ScriptTarget::ES2016 => new_es2017_transformer(opts),
        // other, older, option, transform maximally
        _ => new_es2016_transformer(opts),
    }
}
