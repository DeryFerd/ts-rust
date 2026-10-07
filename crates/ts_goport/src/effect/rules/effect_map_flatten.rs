//! Port of Effect-TS/tsgo `internal/rules/effect_map_flatten.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// EffectMapFlatten suggests using Effect.flatMap instead of Effect.map followed
/// by Effect.flatten in piping flows.
pub static EFFECT_MAP_FLATTEN: Rule = Rule {
    name: "effectMapFlatten",
    group: "style",
    description: "Suggests using Effect.flatMap instead of Effect.map followed by Effect.flatten in piping flows",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377086],
    run: run_effect_map_flatten,
};

fn run_effect_map_flatten(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_effect_map_flatten(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_map_Effect_flatten_is_the_same_as_Effect_flatMap_that_expresses_the_same_steps_more_directly_effect_effectMapFlatten,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

#[derive(Clone, Debug)]
pub struct EffectMapFlattenMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub node: Node,
}

/// AnalyzeEffectMapFlatten finds adjacent Effect.map(...), Effect.flatten pairs
/// in pipe/pipeable flows.
pub fn analyze_effect_map_flatten(tp: &mut TypeParser<'_>, sf: Node) -> Vec<EffectMapFlattenMatch> {
    let mut matches = Vec::new();

    let flows = tp.piping_flows(sf, false);
    for flow in flows.iter() {
        let is_map: &mut PipingFlowTransformationPredicate<'_> = &mut |tp, transformation| {
            !transformation.args.is_empty()
                && tp.is_node_reference_to_effect_module_api(transformation.callee, "map")
        };
        let is_flatten: &mut PipingFlowTransformationPredicate<'_> = &mut |tp, transformation| {
            transformation.args.is_empty()
                && tp.is_node_reference_to_effect_module_api(transformation.callee, "flatten")
        };
        let sequences = flow.find_transformation_sequences(tp, &mut [is_map, is_flatten]);
        for sequence in sequences {
            let map_transformation = &flow.transformations[sequence.start as usize];
            let flatten_transformation = &flow.transformations[sequence.start as usize + 1];
            if (map_transformation.kind != TransformationKind::Pipe
                && map_transformation.kind != TransformationKind::Pipeable)
                || flatten_transformation.kind != map_transformation.kind
            {
                continue;
            }

            matches.push(EffectMapFlattenMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, flatten_transformation.callee),
                node: flatten_transformation.callee,
            });
        }
    }

    matches
}
