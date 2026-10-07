//! Port of Effect-TS/tsgo `internal/rules/provide_layer_succeed_to_provide_service.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

pub static PROVIDE_LAYER_SUCCEED_TO_PROVIDE_SERVICE: Rule = Rule {
    name: "provideLayerSucceedToProvideService",
    group: "style",
    description: "Suggests providing inline Layer.succeed and Layer.effect services directly",
    default_severity: Severity::Suggestion,
    supported_effect: &["v4"],
    codes: &[377124],
    run: run_provide_layer_succeed_to_provide_service,
};

fn run_provide_layer_succeed_to_provide_service(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_provide_layer_succeed_to_provide_service(ctx.tp, ctx.source_file);
    let mut diagnostics = Vec::with_capacity(matches.len());
    for m in &matches {
        diagnostics.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Effect_0_provides_this_inline_single_service_layer_directly_effect_provideLayerSucceedToProvideService,
            Vec::new(),
            vec![m.replacement_method_name.clone()],
        ));
    }
    diagnostics
}

#[derive(Clone, Debug)]
pub struct ProvideLayerSucceedToProvideServiceMatch {
    pub source_file: Node,
    pub location: TextRange,
    // PORT: Go keeps a pointer into the flow's transformations; the port
    // keeps a copy.
    pub provide_transformation: PipingFlowTransformation,
    pub effect_module_node: Node,
    pub service_node: Node,
    pub implementation_node: Node,
    pub replacement_method_name: String,
}

pub fn analyze_provide_layer_succeed_to_provide_service(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<ProvideLayerSucceedToProvideServiceMatch> {
    if sf.is_nil() || tp.supported_effect_version() != EffectMajorVersion::V4 {
        return Vec::new();
    }

    let mut matches = Vec::new();
    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        for provide in &flow.transformations {
            if provide.callee.is_nil()
                || !tp.is_node_reference_to_effect_module_api(provide.callee, "provide")
                || provide.args.len() != 1
            {
                continue;
            }

            let Some((service, implementation, replacement)) =
                inline_single_service_layer(tp, provide.args[0])
            else {
                continue;
            };
            let service_type = tp.get_type_at_location(service);
            if service_type.is_nil()
                || (!tp.is_service_type(service_type) && !tp.is_context_tag(service_type))
            {
                continue;
            }

            let mut effect_module_node = Node::NIL;
            if provide.callee.kind() == SyntaxKind::PropertyAccessExpression {
                effect_module_node = provide.callee.expression();
            }
            matches.push(ProvideLayerSucceedToProvideServiceMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, provide.callee),
                provide_transformation: provide.clone(),
                effect_module_node,
                service_node: service,
                implementation_node: implementation,
                replacement_method_name: replacement,
            });
        }
    }
    matches
}

// PORT: Go returns (service, implementation, replacement, ok); the port
// returns `None` for `ok == false`.
fn inline_single_service_layer(
    tp: &mut TypeParser<'_>,
    node: Node,
) -> Option<(Node, Node, String)> {
    let node = skip_parentheses(node);
    let flow = tp.longest_piping_flow_at(node, false)?;
    let mut subject_pred =
        |_: &mut TypeParser<'_>, subject: &PipingFlowSubject| -> bool { subject.node.is_some() };
    let mut transformation_pred =
        |_: &mut TypeParser<'_>, transformation: &PipingFlowTransformation| -> bool {
            transformation.callee.is_some()
                && transformation.args.len() == 1
                && (transformation.type_arguments.is_nil()
                    || transformation.type_arguments.nodes().is_empty())
        };
    if flow.node != node
        || !flow.matches_exactly(tp, &mut subject_pred, &mut [&mut transformation_pred])
    {
        return None;
    }
    let transformation = &flow.transformations[0];
    let replacement;
    if tp.is_node_reference_to_effect_layer_module_api(transformation.callee, "succeed") {
        replacement = "provideService".to_string();
    } else if tp.is_node_reference_to_effect_layer_module_api(transformation.callee, "effect") {
        replacement = "provideServiceEffect".to_string();
    } else {
        return None;
    }
    Some((transformation.args[0], flow.subject.node, replacement))
}
