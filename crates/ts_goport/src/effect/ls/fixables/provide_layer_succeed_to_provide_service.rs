//! Port of Effect-TS/tsgo `internal/fixables/provide_layer_succeed_to_provide_service.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::ls::fixables::effect_module::effect_module_method;
use crate::effect::ls::rewriter::PipingFlowTransformationReplacement;
use crate::effect::rules::provide_layer_succeed_to_provide_service::analyze_provide_layer_succeed_to_provide_service;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/provide_layer_succeed_to_provide_service.go:12 ProvideLayerSucceedToProvideServiceFix
pub static PROVIDE_LAYER_SUCCEED_TO_PROVIDE_SERVICE_FIX: Fixable = Fixable {
    name: "provideLayerSucceedToProvideService",
    description: "Replace an inline single-service layer with direct service provision",
    // Go: tsdiag.Effect_0_provides_this_inline_single_service_layer_directly_effect_provideLayerSucceedToProvideService
    error_codes: &[377124],
    fix_ids: &["provideLayerSucceedToProvideService_fix"],
    run: run_provide_layer_succeed_to_provide_service_fix,
};

// Go: fixables/provide_layer_succeed_to_provide_service.go:22 runProvideLayerSucceedToProvideServiceFix
// PORT: Go skips a match with a nil `ProvideTransformation`; the Rust match
// always has one.
fn run_provide_layer_succeed_to_provide_service_fix(
    ctx: &mut FixableContext<'_, '_>,
) -> Vec<CodeAction> {
    for m in analyze_provide_layer_succeed_to_provide_service(ctx.tp, ctx.source_file) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        let sf = ctx.source_file;
        if let Some(action) = ctx.new_fix_action(
            format!("Replace with Effect.{}", m.replacement_method_name),
            |tracker| {
                let callee = effect_module_method(
                    tracker,
                    sf,
                    m.effect_module_node,
                    &m.replacement_method_name,
                );
                let f = tracker.node_factory();
                let arguments = f.new_node_list(&[
                    f.deep_clone_node(m.service_node),
                    f.deep_clone_node(m.implementation_node),
                ]);
                tracker.replace_piping_flow_transformation(
                    sf,
                    &m.provide_transformation,
                    PipingFlowTransformationReplacement {
                        callee,
                        type_arguments: NodeList::NIL,
                        arguments,
                    },
                );
            },
        ) {
            return vec![action];
        }
    }
    Vec::new()
}
