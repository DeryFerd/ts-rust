//! Port of Effect-TS/tsgo `internal/fixables` (effect-tsgo 0.51.1,
//! `47cb1ed7`): all code fix implementations and the registry. One Go file
//! per Rust file.
//!
//! Lane E4 ports the disable actions and the 12 fixes that T3 Code hits.
//! The other 43 fixes (lane E5) are comments in [`ALL`] at their Go place.

use std::sync::LazyLock;

use crate::effect::ls::fixable::Fixable;

pub mod acquire_release_disposable;
pub mod all_of_map_to_for_each;
pub mod catch_to_ignore;
pub mod disable;
pub mod effect_fn_iife;
pub mod effect_fn_opportunity;
pub mod effect_map_void;
mod effect_module;
pub mod flat_map_conditional_to_filter_or_fail;
pub mod flat_map_ignored_param_to_and_then;
pub mod flat_map_to_map;
pub mod map_some_to_as_some;
pub mod missed_pipeable_opportunity;
pub mod option_match_to_from_option;
pub mod prefer_succeed_some_or_none;
pub mod provide_layer_succeed_to_provide_service;
pub mod run_effect_inside_effect;
pub mod run_of_exit_to_run_exit;
pub mod schema_number;
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
        // E5: FloatingEffectYieldFix,
        // E5: MissingReturnYieldStarFix,
        // E5: MissingStarInYieldEffectGenFix,
        // E5: CatchDieToOrDieFix,
        &timeout_catch_tag_to_timeout_or_else::TIMEOUT_CATCH_TAG_TO_TIMEOUT_OR_ELSE_FIX,
        // E5: CatchAllToMapErrorFix,
        // E5: CatchAllTagDispatchToCatchTagFix,
        // E5: CatchIfTagToCatchTagFix,
        // E5: CatchTagToCatchReasonFix,
        &all_of_map_to_for_each::ALL_OF_MAP_TO_FOR_EACH_FIX,
        &flat_map_to_map::FLAT_MAP_TO_MAP_FIX,
        &flat_map_ignored_param_to_and_then::FLAT_MAP_IGNORED_PARAM_TO_AND_THEN_FIX,
        // E5: MatchEffectToMatchFix,
        // E5: MatchEffectToMapBothFix,
        &flat_map_conditional_to_filter_or_fail::FLAT_MAP_CONDITIONAL_TO_FILTER_OR_FAIL_FIX,
        &map_some_to_as_some::MAP_SOME_TO_AS_SOME_FIX,
        &option_match_to_from_option::OPTION_MATCH_TO_FROM_OPTION_FIX,
        &sync_to_succeed::SYNC_TO_SUCCEED_FIX,
        // E5: CatchToOrElseSucceedFix,
        &catch_to_ignore::CATCH_TO_IGNORE_FIX,
        &effect_fn_iife::EFFECT_FN_IIFE_FIX,
        &unnecessary_pipe::UNNECESSARY_PIPE_FIX,
        &unnecessary_pipe_chain::UNNECESSARY_PIPE_CHAIN_FIX,
        // E5: ReturnEffectInGenFix,
        // E5: EffectSucceedWithVoidFix,
        &prefer_succeed_some_or_none::PREFER_SUCCEED_SOME_OR_NONE_FIX,
        &unnecessary_effect_gen::UNNECESSARY_EFFECT_GEN_FIX,
        &unnecessary_arrow_block::UNNECESSARY_ARROW_BLOCK_FIX,
        &unnecessary_typeof_type::UNNECESSARY_TYPEOF_TYPE_FIX,
        // E5: PreferSchemaTypePropertyFix,
        &effect_map_void::EFFECT_MAP_VOID_FIX,
        &unnecessary_fail_yieldable_error::UNNECESSARY_FAIL_YIELDABLE_ERROR_FIX,
        // E5: ClassSelfMismatchFix,
        &effect_fn_opportunity::EFFECT_FN_OPPORTUNITY_FIX,
        // E5: DeterministicKeysFix,
        // E5: ScopeInLayerEffectScopedFix,
        // E5: OverriddenSchemaConstructorFix,
        // E5: InstanceOfSchemaFix,
        // E5: LayerMergeAllWithDependenciesFix,
        &unsafe_effect_type_assertion::UNSAFE_EFFECT_TYPE_ASSERTION_FIX,
        // E5: MissingEffectErrorCatchFix,
        // E5: MultipleEffectProvideFix,
        &provide_layer_succeed_to_provide_service::PROVIDE_LAYER_SUCCEED_TO_PROVIDE_SERVICE_FIX,
        // E5: SchemaStructWithTagFix,
        &schema_number::SCHEMA_NUMBER_FIX,
        // E5: RedundantSchemaTagIdentifierRemoveIdentifierFix,
        &run_effect_inside_effect::RUN_EFFECT_INSIDE_EFFECT_FIX,
        // E5: SchemaUnionOfLiteralsFix,
        &missed_pipeable_opportunity::MISSED_PIPEABLE_OPPORTUNITY_FIX,
        // E5: NewSchemaClassFix,
        // E5: ServiceNotAsClassFix,
        // E5: PreferUnsafeConstructorFix,
        // E5: PreferTypedSchemaDecoderFix,
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
