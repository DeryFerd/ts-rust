//! Port of Effect-TS/tsgo `internal/rules/layer_merge_all_with_dependencies.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// LayerMergeAllWithDependencies detects interdependencies in Layer.mergeAll calls
/// where one layer provides a service that another layer requires. Since mergeAll
/// creates layers in parallel, these dependencies will not be satisfied.
pub static LAYER_MERGE_ALL_WITH_DEPENDENCIES: Rule = Rule {
    name: "layerMergeAllWithDependencies",
    group: "antipattern",
    description: "Detects interdependencies in Layer.mergeAll calls where one layer provides a service that another layer requires",
    default_severity: Severity::Warning,
    supported_effect: &["v3", "v4"],
    codes: &[377035],
    run: run_layer_merge_all_with_dependencies,
};

fn run_layer_merge_all_with_dependencies(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_layer_merge_all_with_dependencies(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_layer_provides_0_which_is_required_by_another_layer_in_the_same_Layer_mergeAll_call_Layer_mergeAll_creates_layers_in_parallel_so_dependencies_between_layers_will_not_be_satisfied_Consider_moving_this_layer_into_a_Layer_provideMerge_after_the_Layer_mergeAll_effect_layerMergeAllWithDependencies,
            Vec::new(),
            vec![m.provided_types],
        ));
    }
    diags
}

/// LayerMergeAllWithDependenciesMatch holds the AST nodes needed by both the
/// diagnostic rule and the quick-fix for the layerMergeAllWithDependencies pattern.
#[derive(Clone, Debug)]
pub struct LayerMergeAllWithDependenciesMatch {
    pub source_file: Node,
    /// The error range on the provider argument
    pub location: TextRange,
    /// The full Layer.mergeAll(...) call expression node
    pub call_node: Node,
    /// The specific argument node that is the dependency provider
    pub provider_arg: Node,
    /// Index of the provider argument in the call's argument list
    pub provider_index: i32,
    /// All arguments of the mergeAll call
    pub all_args: Vec<Node>,
    /// Formatted string of provided type names
    pub provided_types: String,
}

/// AnalyzeLayerMergeAllWithDependencies finds all Layer.mergeAll calls with
/// interdependencies where one layer provides a service required by another.
pub fn analyze_layer_merge_all_with_dependencies(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<LayerMergeAllWithDependenciesMatch> {
    let mut matches = Vec::new();

    // Stack-based traversal
    let mut node_to_visit: Vec<Node> = Vec::new();
    sf.for_each_child(|child| {
        node_to_visit.push(child);
        false
    });

    while let Some(node) = node_to_visit.pop() {
        if node.kind() == SyntaxKind::CallExpression {
            let result = analyze_layer_merge_all_call(tp, sf, node);
            if !result.is_empty() {
                matches.extend(result);
            }
        }

        // Enqueue children
        node.for_each_child(|child| {
            node_to_visit.push(child);
            false
        });
    }

    matches
}

/// layerInfo holds parsed layer information for a mergeAll argument.
struct LayerInfo {
    arg: Node,
    requirements_type: TypeId,
}

/// analyzeLayerMergeAllCall checks a call expression for Layer.mergeAll interdependencies.
fn analyze_layer_merge_all_call(
    tp: &mut TypeParser<'_>,
    sf: Node,
    node: Node,
) -> Vec<LayerMergeAllWithDependenciesMatch> {
    if node.kind() != SyntaxKind::CallExpression {
        return Vec::new();
    }
    let call = node;

    // Check if this is Layer.mergeAll
    if !tp.is_node_reference_to_effect_layer_module_api(call.expression(), "mergeAll") {
        return Vec::new();
    }

    if call.argument_list().is_nil() || call.arguments().len() < 2 {
        return Vec::new();
    }
    let args = call.arguments().to_vec();

    // Parse all layer arguments
    let mut layer_infos: Vec<LayerInfo> = Vec::new();
    // Map of actually provided types -> argument node that provides them
    // PORT: Go ranges over this map below in random order, which decides the
    // order of the type names in the message. The port keeps insertion order.
    let mut actually_provided_map: IndexMap<TypeId, Node> = IndexMap::new();

    for &arg in &args {
        let arg_type = tp.get_type_at_location(arg);
        if arg_type.is_nil() {
            continue;
        }

        let Some(layer) = tp.layer_type(arg_type) else {
            continue;
        };

        // Unroll union members for provided types (ROut)
        let provided_members = tp.unroll_union_members(layer.r_out);

        // Filter out never types and pass-through types
        for provided_type in provided_members {
            if tp
                .checker
                .ty(provided_type)
                .flags()
                .intersects(TypeFlags::NEVER)
            {
                continue;
            }
            // A pass-through type is both provided (ROut) and required (RIn) by the same layer
            if tp.checker.is_type_assignable_to(provided_type, layer.r_in) {
                continue;
            }
            actually_provided_map.insert(provided_type, arg);
        }

        layer_infos.push(LayerInfo {
            arg,
            requirements_type: layer.r_in,
        });
    }

    // Check for interdependencies: build a map of provider -> consumed types
    struct ProviderConsumer {
        provided_type: TypeId,
    }
    let mut provider_to_consumers: FxHashMap<Node, Vec<ProviderConsumer>> = FxHashMap::default();

    for li in &layer_infos {
        for (&provided_type, &provider_arg) in &actually_provided_map {
            // Skip self-references
            if provider_arg == li.arg {
                continue;
            }
            // Check if this provided type satisfies the layer's requirements
            if tp
                .checker
                .is_type_assignable_to(provided_type, li.requirements_type)
            {
                provider_to_consumers
                    .entry(provider_arg)
                    .or_default()
                    .push(ProviderConsumer { provided_type });
            }
        }
    }

    // Build matches for providers, iterating in argument order for determinism
    let mut matches = Vec::new();
    for (arg_index, &arg) in args.iter().enumerate() {
        let Some(consumers) = provider_to_consumers.get(&arg) else {
            continue;
        };
        if consumers.is_empty() {
            continue;
        }

        // Collect unique type names
        let mut seen: FxHashSet<String> = FxHashSet::default();
        let mut type_names: Vec<String> = Vec::new();
        for consumer in consumers {
            let name = tp.checker.type_to_string_exported(consumer.provided_type);
            if !seen.contains(&name) {
                seen.insert(name.clone());
                type_names.push(name);
            }
        }

        matches.push(LayerMergeAllWithDependenciesMatch {
            source_file: sf,
            location: get_error_range_for_node(sf, arg),
            call_node: node,
            provider_arg: arg,
            provider_index: arg_index as i32,
            all_args: args.clone(),
            provided_types: type_names.join(", "),
        });
    }

    matches
}
