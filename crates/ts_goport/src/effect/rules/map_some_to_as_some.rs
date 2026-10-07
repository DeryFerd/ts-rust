//! Port of Effect-TS/tsgo `internal/rules/map_some_to_as_some.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// MapSomeToAsSome suggests Effect.asSome when Effect.map only wraps the
/// success value with Option.some.
// Go: rules/map_some_to_as_some.go MapSomeToAsSome
pub static MAP_SOME_TO_AS_SOME: Rule = Rule {
    name: "mapSomeToAsSome",
    group: "style",
    description: "Suggests using Effect.asSome instead of Effect.map when the mapper only wraps the success value with Option.some",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377114],
    run: run_map_some_to_as_some,
};

fn run_map_some_to_as_some(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_map_some_to_as_some(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_asSome_expresses_wrapping_the_success_value_in_Option_some_directly_effect_mapSomeToAsSome,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

/// MapSomeToAsSomeMatch holds the nodes needed by the diagnostic and quick fix.
// Go: rules/map_some_to_as_some.go MapSomeToAsSomeMatch
// PORT: Go keeps a pointer into the flow's transformations; the port keeps a copy.
#[derive(Clone)]
pub struct MapSomeToAsSomeMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub transformation: PipingFlowTransformation,
    pub effect_module_node: Node,
}

/// AnalyzeMapSomeToAsSome finds data-last and data-first Effect.map calls whose
/// mapper is Option.some or an identity forwarder such as value => Option.some(value).
// Go: rules/map_some_to_as_some.go AnalyzeMapSomeToAsSome
pub fn analyze_map_some_to_as_some(tp: &mut TypeParser<'_>, sf: Node) -> Vec<MapSomeToAsSomeMatch> {
    let mut matches = Vec::new();
    for flow in tp.piping_flows(sf, true).iter() {
        for transformation in &flow.transformations {
            if transformation.args.len() != 1
                || transformation.callee.is_nil()
                || !tp.is_node_reference_to_effect_module_api(transformation.callee, "map")
            {
                continue;
            }

            if transformation.type_arguments.is_some()
                && !transformation.type_arguments.nodes().is_empty()
                || !is_option_some_mapper(tp, transformation.args[0])
            {
                continue;
            }
            let mut effect_module_node = Node::NIL;
            if transformation.callee.kind() == SyntaxKind::PropertyAccessExpression {
                effect_module_node = transformation.callee.expression();
            }
            matches.push(MapSomeToAsSomeMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, transformation.callee),
                transformation: transformation.clone(),
                effect_module_node,
            });
        }
    }
    matches
}

// Go: rules/map_some_to_as_some.go isOptionSomeMapper
fn is_option_some_mapper(tp: &mut TypeParser<'_>, node: Node) -> bool {
    let (mapper, type_arguments, parameter) = tp.unwrap_identity_forwarder(node);
    if type_arguments.is_some() && !type_arguments.nodes().is_empty() {
        return false;
    }
    if parameter.is_some() {
        let parameter_declaration = parameter;
        if parameter_declaration.is_nil()
            || parameter_declaration.question_token().is_some()
            || parameter_declaration.type_().is_some()
        {
            return false;
        }
    }
    tp.is_node_reference_to_effect_option_module_api(mapper, "some")
}
