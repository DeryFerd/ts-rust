//! Port of Effect-TS/tsgo `internal/fixables` (effect-tsgo 0.51.1,
//! `47cb1ed7`): all code fix implementations and the registry. One Go file
//! per Rust file.
//!
//! Lane E4 ports the disable actions and the 12 fixes that T3 Code hits,
//! lanes E5a, E5b and E5c the other 43. [`ALL`] has all 56 entries in the
//! Go order.

use std::sync::LazyLock;

use crate::effect::ls::fixable::Fixable;

pub mod acquire_release_disposable;
pub mod all_of_map_to_for_each;
pub mod catch_all_tag_dispatch_to_catch_tag;
pub mod catch_all_to_map_error;
pub mod catch_die_to_or_die;
pub mod catch_if_tag_to_catch_tag;
pub mod catch_tag_to_catch_reason;
pub mod catch_to_ignore;
pub mod catch_to_or_else_succeed;
pub mod class_self_mismatch;
pub mod deterministic_keys;
pub mod disable;
pub mod effect_fn_iife;
pub mod effect_fn_opportunity;
pub mod effect_map_void;
mod effect_module;
pub mod effect_succeed_with_void;
pub mod flat_map_conditional_to_filter_or_fail;
pub mod flat_map_ignored_param_to_and_then;
pub mod flat_map_to_map;
pub mod floating_effect_yield;
pub mod instance_of_schema;
pub mod layer_merge_all_with_dependencies;
pub mod map_some_to_as_some;
pub mod match_effect_to_map_both;
pub mod match_effect_to_match;
pub mod missed_pipeable_opportunity;
pub mod missing_effect_error_catch;
pub mod missing_return_yield_star;
pub mod missing_star_in_yield_effect_gen;
pub mod multiple_effect_provide;
pub mod new_schema_class;
pub mod option_match_to_from_option;
pub mod overridden_schema_constructor;
pub mod prefer_schema_type_property;
pub mod prefer_succeed_some_or_none;
pub mod prefer_typed_schema_decoder;
pub mod prefer_unsafe_constructor;
pub mod provide_layer_succeed_to_provide_service;
pub mod redundant_schema_tag_identifier;
pub mod return_effect_in_gen;
pub mod run_effect_inside_effect;
pub mod run_of_exit_to_run_exit;
pub mod schema_number;
pub mod schema_struct_with_tag;
pub mod schema_union_of_literals;
pub mod scope_in_layer_effect;
pub mod service_not_as_class;
pub mod sync_to_succeed;
pub mod timeout_catch_tag_to_timeout_or_else;
pub mod unnecessary_arrow_block;
pub mod unnecessary_effect_gen;
pub mod unnecessary_fail_yieldable_error;
pub mod unnecessary_pipe;
pub mod unnecessary_pipe_chain;
pub mod unnecessary_typeof_type;
pub mod unsafe_effect_type_assertion;

// Go: fixables/fixables.go:9 All
/// All is the list of all code fix providers.
/// Add new fixables here explicitly - no init() magic.
// PORT: a `LazyLock` because the disable fix takes its codes from
// `rules::ALL` (Go evaluates it at package init).
pub static ALL: LazyLock<Vec<&'static Fixable>> = LazyLock::new(|| {
    vec![
        // Disable actions (handles all Effect diagnostic codes)
        &*disable::EFFECT_DISABLE,
        // Add future fixables here:
        // POCRuleFix,
        &floating_effect_yield::FLOATING_EFFECT_YIELD_FIX,
        &missing_return_yield_star::MISSING_RETURN_YIELD_STAR_FIX,
        &missing_star_in_yield_effect_gen::MISSING_STAR_IN_YIELD_EFFECT_GEN_FIX,
        &catch_die_to_or_die::CATCH_DIE_TO_OR_DIE_FIX,
        &timeout_catch_tag_to_timeout_or_else::TIMEOUT_CATCH_TAG_TO_TIMEOUT_OR_ELSE_FIX,
        &catch_all_to_map_error::CATCH_ALL_TO_MAP_ERROR_FIX,
        &catch_all_tag_dispatch_to_catch_tag::CATCH_ALL_TAG_DISPATCH_TO_CATCH_TAG_FIX,
        &catch_if_tag_to_catch_tag::CATCH_IF_TAG_TO_CATCH_TAG_FIX,
        &catch_tag_to_catch_reason::CATCH_TAG_TO_CATCH_REASON_FIX,
        &all_of_map_to_for_each::ALL_OF_MAP_TO_FOR_EACH_FIX,
        &flat_map_to_map::FLAT_MAP_TO_MAP_FIX,
        &flat_map_ignored_param_to_and_then::FLAT_MAP_IGNORED_PARAM_TO_AND_THEN_FIX,
        &match_effect_to_match::MATCH_EFFECT_TO_MATCH_FIX,
        &match_effect_to_map_both::MATCH_EFFECT_TO_MAP_BOTH_FIX,
        &flat_map_conditional_to_filter_or_fail::FLAT_MAP_CONDITIONAL_TO_FILTER_OR_FAIL_FIX,
        &map_some_to_as_some::MAP_SOME_TO_AS_SOME_FIX,
        &option_match_to_from_option::OPTION_MATCH_TO_FROM_OPTION_FIX,
        &sync_to_succeed::SYNC_TO_SUCCEED_FIX,
        &catch_to_or_else_succeed::CATCH_TO_OR_ELSE_SUCCEED_FIX,
        &catch_to_ignore::CATCH_TO_IGNORE_FIX,
        &effect_fn_iife::EFFECT_FN_IIFE_FIX,
        &unnecessary_pipe::UNNECESSARY_PIPE_FIX,
        &unnecessary_pipe_chain::UNNECESSARY_PIPE_CHAIN_FIX,
        &return_effect_in_gen::RETURN_EFFECT_IN_GEN_FIX,
        &effect_succeed_with_void::EFFECT_SUCCEED_WITH_VOID_FIX,
        &prefer_succeed_some_or_none::PREFER_SUCCEED_SOME_OR_NONE_FIX,
        &unnecessary_effect_gen::UNNECESSARY_EFFECT_GEN_FIX,
        &unnecessary_arrow_block::UNNECESSARY_ARROW_BLOCK_FIX,
        &unnecessary_typeof_type::UNNECESSARY_TYPEOF_TYPE_FIX,
        &prefer_schema_type_property::PREFER_SCHEMA_TYPE_PROPERTY_FIX,
        &effect_map_void::EFFECT_MAP_VOID_FIX,
        &unnecessary_fail_yieldable_error::UNNECESSARY_FAIL_YIELDABLE_ERROR_FIX,
        &class_self_mismatch::CLASS_SELF_MISMATCH_FIX,
        &effect_fn_opportunity::EFFECT_FN_OPPORTUNITY_FIX,
        &deterministic_keys::DETERMINISTIC_KEYS_FIX,
        &scope_in_layer_effect::SCOPE_IN_LAYER_EFFECT_SCOPED_FIX,
        &overridden_schema_constructor::OVERRIDDEN_SCHEMA_CONSTRUCTOR_FIX,
        &instance_of_schema::INSTANCE_OF_SCHEMA_FIX,
        &layer_merge_all_with_dependencies::LAYER_MERGE_ALL_WITH_DEPENDENCIES_FIX,
        &unsafe_effect_type_assertion::UNSAFE_EFFECT_TYPE_ASSERTION_FIX,
        &missing_effect_error_catch::MISSING_EFFECT_ERROR_CATCH_FIX,
        &multiple_effect_provide::MULTIPLE_EFFECT_PROVIDE_FIX,
        &provide_layer_succeed_to_provide_service::PROVIDE_LAYER_SUCCEED_TO_PROVIDE_SERVICE_FIX,
        &schema_struct_with_tag::SCHEMA_STRUCT_WITH_TAG_FIX,
        &schema_number::SCHEMA_NUMBER_FIX,
        &redundant_schema_tag_identifier::REDUNDANT_SCHEMA_TAG_IDENTIFIER_REMOVE_IDENTIFIER_FIX,
        &run_effect_inside_effect::RUN_EFFECT_INSIDE_EFFECT_FIX,
        &schema_union_of_literals::SCHEMA_UNION_OF_LITERALS_FIX,
        &missed_pipeable_opportunity::MISSED_PIPEABLE_OPPORTUNITY_FIX,
        &new_schema_class::NEW_SCHEMA_CLASS_FIX,
        &service_not_as_class::SERVICE_NOT_AS_CLASS_FIX,
        &prefer_unsafe_constructor::PREFER_UNSAFE_CONSTRUCTOR_FIX,
        &prefer_typed_schema_decoder::PREFER_TYPED_SCHEMA_DECODER_FIX,
        &acquire_release_disposable::ACQUIRE_RELEASE_DISPOSABLE_FIX,
        &run_of_exit_to_run_exit::RUN_OF_EXIT_TO_RUN_EXIT_FIX,
    ]
});

// Go: fixables/fixables.go:72 ByErrorCode
/// ByErrorCode finds all fixables that handle a given error code.
#[must_use]
pub fn by_error_code(code: i32) -> Vec<&'static Fixable> {
    ALL.iter()
        .copied()
        .filter(|fixable| fixable.handles_code(code))
        .collect()
}

// Go: fixables/fixables.go:83 AllErrorCodes
/// AllErrorCodes returns all unique error codes handled by any fixable.
#[must_use]
pub fn all_error_codes() -> Vec<i32> {
    let mut codes = Vec::new();
    for fixable in ALL.iter() {
        for &code in fixable.error_codes {
            if !codes.contains(&code) {
                codes.push(code);
            }
        }
    }
    codes
}

// Go: fixables/fixables.go:98 AllFixIDs
/// AllFixIDs returns all unique fix IDs from all fixables.
#[must_use]
pub fn all_fix_ids() -> Vec<String> {
    let mut ids: Vec<String> = Vec::new();
    for fixable in ALL.iter() {
        for &id in fixable.fix_ids {
            if !ids.iter().any(|seen| seen == id) {
                ids.push(id.to_string());
            }
        }
    }
    ids
}
