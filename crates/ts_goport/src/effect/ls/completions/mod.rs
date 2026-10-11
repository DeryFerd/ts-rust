//! Port of Effect-TS/tsgo `internal/completions` (effect-tsgo 0.51.1,
//! `47cb1ed7`): all completion implementations and the registry. One Rust
//! file per Go file; the shared helpers stay in the Go file that has them
//! (`effect_schema_self_in_classes.rs`: the item makers and
//! `byte_span_to_range`; `context_self_in_classes.rs`: the service tag key;
//! `fn_function_star.rs`: the enclosing variable name;
//! `effect_diagnostics_comment.rs`: the comment `@` match).

use crate::effect::ls::completion::Completion;

pub mod context_self_in_classes;
pub mod duration_input;
pub mod effect_codegens_comment;
pub mod effect_data_classes;
pub mod effect_diagnostics_comment;
pub mod effect_jsdoc_comment;
pub mod effect_rpc_make_classes;
pub mod effect_schema_self_in_classes;
pub mod effect_self_in_classes;
pub mod effect_sql_model_self_in_classes;
pub mod fn_function_star;
pub mod gen_function_star;
pub mod schema_brand;

// Go: completions/completions.go:9 All
/// All is the list of all completion providers.
/// Add new completions here explicitly - no init() magic.
pub static ALL: &[&Completion] = &[
    &effect_schema_self_in_classes::EFFECT_SCHEMA_SELF_IN_CLASSES,
    &effect_data_classes::EFFECT_DATA_CLASSES,
    &context_self_in_classes::CONTEXT_SELF_IN_CLASSES,
    &gen_function_star::GEN_FUNCTION_STAR,
    &fn_function_star::FN_FUNCTION_STAR,
    &effect_diagnostics_comment::EFFECT_DIAGNOSTICS_COMMENT,
    &effect_codegens_comment::EFFECT_CODEGENS_COMMENT,
    &effect_jsdoc_comment::EFFECT_JSDOC_COMMENT,
    &duration_input::DURATION_INPUT,
    &effect_self_in_classes::EFFECT_SELF_IN_CLASSES,
    &effect_sql_model_self_in_classes::EFFECT_SQL_MODEL_SELF_IN_CLASSES,
    &effect_rpc_make_classes::RPC_MAKE_CLASSES,
    &schema_brand::SCHEMA_BRAND,
];
