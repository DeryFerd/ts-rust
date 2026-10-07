//! Port of Effect-TS/tsgo `internal/rules/multiple_effect_provide.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// MultipleEffectProvide detects consecutive Effect.provide calls with Layer-typed
/// arguments within piping flows and warns that they should be merged into a single
/// provide call to avoid service lifecycle issues.
// Go: rules/multiple_effect_provide.go MultipleEffectProvide
pub static MULTIPLE_EFFECT_PROVIDE: Rule = Rule {
    name: "multipleEffectProvide",
    group: "antipattern",
    description: "Warns against chaining Effect.provide calls which can cause service lifecycle issues",
    default_severity: Severity::Warning,
    supported_effect: &["v3", "v4"],
    codes: &[377033],
    run: run_multiple_effect_provide,
};

fn run_multiple_effect_provide(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let sf = ctx.source_file;
    let matches = analyze_multiple_effect_provide(ctx.tp, sf);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_expression_chains_multiple_Effect_provide_calls_Providing_Layers_in_multiple_calls_in_a_chain_can_break_service_lifecycle_behavior_compared_with_a_single_combined_provide_with_merged_layers_effect_multipleEffectProvide,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

/// MultipleEffectProvideMatch holds the AST nodes needed by both the
/// diagnostic rule and the quick-fix for the multipleEffectProvide pattern.
// Go: rules/multiple_effect_provide.go MultipleEffectProvideMatch
#[derive(Clone, Debug)]
pub struct MultipleEffectProvideMatch {
    /// The source file where the diagnostic should be reported
    pub source_file: Node,
    /// The diagnostic span (error range on the first call in the chunk)
    pub location: TextRange,
    /// The list of call expression nodes in the consecutive provide chain (2+ elements)
    pub chunk: Vec<Node>,
    /// The layer argument nodes from each Effect.provide(layer) call
    pub layer_args: Vec<Node>,
    /// The Effect module identifier node from the first chunk callee
    pub effect_module_node: Node,
}

/// AnalyzeMultipleEffectProvide finds all consecutive Effect.provide call chains
/// with Layer-typed arguments within piping flows.
// Go: rules/multiple_effect_provide.go AnalyzeMultipleEffectProvide
pub fn analyze_multiple_effect_provide(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<MultipleEffectProvideMatch> {
    let mut matches = Vec::new();
    let is_effect_v4 = tp.supported_effect_version() == EffectMajorVersion::V4;

    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        // Track chunks of consecutive Effect.provide calls with Layer arguments.
        let mut current_chunk: Vec<Node> = Vec::new();
        let mut current_layer_args: Vec<Node> = Vec::new();
        let mut current_effect_module_node = Node::NIL;

        // PORT: Go `finalizeChunk` closure over the three chunk variables.
        let finalize_chunk = |matches: &mut Vec<MultipleEffectProvideMatch>,
                              current_chunk: &mut Vec<Node>,
                              current_layer_args: &mut Vec<Node>,
                              current_effect_module_node: &mut Node| {
            if current_chunk.len() >= 2 {
                matches.push(MultipleEffectProvideMatch {
                    source_file: sf,
                    location: get_error_range_for_node(sf, current_chunk[0]),
                    chunk: std::mem::take(current_chunk),
                    layer_args: std::mem::take(current_layer_args),
                    effect_module_node: *current_effect_module_node,
                });
            }
            current_chunk.clear();
            current_layer_args.clear();
            *current_effect_module_node = Node::NIL;
        };

        for transformation in &flow.transformations {
            // Check if this is an Effect.provide call
            if !tp.is_node_reference_to_effect_module_api(transformation.callee, "provide") {
                finalize_chunk(
                    &mut matches,
                    &mut current_chunk,
                    &mut current_layer_args,
                    &mut current_effect_module_node,
                );
                continue;
            }

            // Must have arguments
            if transformation.args.is_empty() {
                finalize_chunk(
                    &mut matches,
                    &mut current_chunk,
                    &mut current_layer_args,
                    &mut current_effect_module_node,
                );
                continue;
            }

            let mut is_local_provide = false;
            if is_effect_v4 && transformation.args.len() > 1 {
                let options = transformation.args[1];
                if options.is_some() && options.kind() == SyntaxKind::ObjectLiteralExpression {
                    for property in options.properties().iter() {
                        if property.is_nil() || property.kind() != SyntaxKind::PropertyAssignment {
                            continue;
                        }
                        let assignment = property;
                        let name = assignment.name();
                        if name.is_some()
                            && name.kind() == SyntaxKind::Identifier
                            && name.text() == "local"
                            && assignment.initializer().kind() == SyntaxKind::TrueKeyword
                        {
                            is_local_provide = true;
                            break;
                        }
                    }
                }
            }
            if is_local_provide {
                finalize_chunk(
                    &mut matches,
                    &mut current_chunk,
                    &mut current_layer_args,
                    &mut current_effect_module_node,
                );
                continue;
            }

            // Check if the first argument is a Layer type
            let arg = transformation.args[0];
            let arg_type = tp.get_type_at_location(arg);
            if arg_type.is_nil() {
                finalize_chunk(
                    &mut matches,
                    &mut current_chunk,
                    &mut current_layer_args,
                    &mut current_effect_module_node,
                );
                continue;
            }

            if tp.layer_type(arg_type).is_none() {
                // provide call but not with a Layer argument — breaks the chain
                finalize_chunk(
                    &mut matches,
                    &mut current_chunk,
                    &mut current_layer_args,
                    &mut current_effect_module_node,
                );
                continue;
            }

            // Find the enclosing call expression for this provide
            let call_node = find_ancestor_kind(transformation.callee, SyntaxKind::CallExpression);
            if call_node.is_nil() {
                finalize_chunk(
                    &mut matches,
                    &mut current_chunk,
                    &mut current_layer_args,
                    &mut current_effect_module_node,
                );
                continue;
            }

            // Capture Effect module node from the callee's property access expression
            if current_chunk.is_empty()
                && transformation.callee.kind() == SyntaxKind::PropertyAccessExpression
            {
                current_effect_module_node = transformation.callee.expression();
            }

            current_chunk.push(call_node);
            current_layer_args.push(arg);
        }

        // Finalize the last chunk after the loop
        finalize_chunk(
            &mut matches,
            &mut current_chunk,
            &mut current_layer_args,
            &mut current_effect_module_node,
        );
    }

    matches
}
