//! Port of Effect-TS/tsgo `internal/rules/missing_effect_context.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::layergraph;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// Go `MissingEffectContext`: detects when an Effect has context
/// requirements that are not handled by the expected type. This happens when
/// assigning an Effect with requirements to a variable/parameter expecting an
/// Effect with fewer or no requirements.
pub static MISSING_EFFECT_CONTEXT: Rule = Rule {
    name: "missingEffectContext",
    group: "correctness",
    description: "Detects Effect values with unhandled context requirements",
    default_severity: Severity::Error,
    supported_effect: &["v3", "v4"],
    codes: &[377004],
    run: run_missing_effect_context,
};

// Go: MissingEffectContext.Run
fn run_missing_effect_context(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diags = Vec::new();

    let source_file = ctx.source_file;
    for re in ctx.tp.checker.get_relation_errors(source_file) {
        // Parse both types as Effects
        let src_effect = ctx.tp.effect_type(re.source);
        let tgt_effect = ctx.tp.effect_type(re.target);

        // Both must be Effect types
        let (Some(src_effect), Some(tgt_effect)) = (src_effect, tgt_effect) else {
            continue;
        };

        // Find unhandled context types by checking each source requirement member
        // against the target requirement type
        let unhandled_contexts = find_unhandled_contexts(ctx.tp, src_effect.r, tgt_effect.r);
        if !unhandled_contexts.is_empty() {
            let context_type_str = format_context_types(ctx.tp.checker, &unhandled_contexts);
            let related =
                missing_effect_context_related_information(ctx, re.error_node, &unhandled_contexts);
            let diag = ctx.new_diagnostic(
                source_file,
                ctx.get_error_range(re.error_node),
                diag::This_Effect_requires_a_service_that_is_missing_from_the_expected_Effect_context_Colon_0_effect_missingEffectContext,
                related,
                vec![context_type_str],
            );
            diags.push(diag);
        }
    }

    diags
}

// Go: findUnhandledContexts
/// Returns the source context types that are not assignable to the target
/// context type.
fn find_unhandled_contexts(tp: &mut TypeParser<'_>, src_r: TypeId, tgt_r: TypeId) -> Vec<TypeId> {
    // Unroll source context union into individual members
    let src_members = tp.unroll_union_members(src_r);

    let mut unhandled = Vec::new();
    for member in src_members {
        // Check if this specific member is assignable to target
        if !tp.checker.is_type_assignable_to(member, tgt_r) {
            unhandled.push(member);
        }
    }
    unhandled
}

// Go: formatContextTypes
/// Formats a slice of context types as a union string (e.g., "EnvA | EnvB").
fn format_context_types(c: &mut Checker, types: &[TypeId]) -> String {
    if types.is_empty() {
        return String::new();
    }
    if types.len() == 1 {
        return c.type_to_string_exported(types[0]);
    }
    let mut result = String::new();
    result.push_str(&c.type_to_string_exported(types[0]));
    for &t in &types[1..] {
        result.push_str(" | ");
        result.push_str(&c.type_to_string_exported(t));
    }
    result
}

// Go: missingEffectContextRelatedInformation
// PORT: Go also takes `c`; the port uses `ctx.tp.checker`.
fn missing_effect_context_related_information(
    ctx: &mut RuleContext<'_, '_>,
    error_node: Node,
    missing_types: &[TypeId],
) -> Vec<Diagnostic> {
    let source_file = ctx.source_file;
    let provide_location = find_related_provide_location(ctx.tp, source_file, error_node);
    if provide_location.layer_node.is_nil() {
        return Vec::new();
    }
    let layer_diagnostics =
        find_related_layer_provider_diagnostics(ctx, provide_location.layer_node, missing_types);
    if layer_diagnostics.is_empty() {
        return Vec::new();
    }
    let provide_diagnostic = ctx.new_diagnostic(
        source_file,
        provide_location.location,
        diag::Adjusting_this_layer_composition_could_provide_the_missing_service_effect_missingEffectContext,
        Vec::new(),
        Vec::new(),
    );
    let mut related_information = Vec::with_capacity(1 + layer_diagnostics.len());
    related_information.push(provide_diagnostic);
    related_information.extend(layer_diagnostics);
    related_information
}

/// Go `provideLocation`.
#[derive(Clone, Copy, Debug, Default)]
pub struct ProvideLocation {
    pub layer_node: Node,
    pub location: TextRange,
}

// Go: findRelatedProvideLocation
// PORT: Go returns the zero value when `c` is nil; the port's checker is
// never nil.
fn find_related_provide_location(
    tp: &mut TypeParser<'_>,
    sf: Node,
    error_node: Node,
) -> ProvideLocation {
    if sf.is_nil() || error_node.is_nil() {
        return ProvideLocation::default();
    }
    let flows = tp.piping_flows(sf, true);
    for flow in flows.iter() {
        if flow.node.is_nil() {
            continue;
        }
        if !node_contains(flow.node, error_node) {
            continue;
        }
        let error_transformation_index =
            find_transformation_index_containing_node(flow, error_node);
        if error_transformation_index < 0 {
            continue;
        }
        let mut i = error_transformation_index - 1;
        while i >= 0 {
            let transformation = &flow.transformations[i as usize];
            if !tp.is_node_reference_to_effect_module_api(transformation.callee, "provide") {
                i -= 1;
                continue;
            }
            return ProvideLocation {
                layer_node: first_node(&transformation.args),
                location: get_error_range_for_node(sf, transformation.callee),
            };
        }
    }
    ProvideLocation::default()
}

// Go: findRelatedLayerProviderDiagnostics
// PORT: Go also takes `c`, and returns nil when `c` or `ctx` is nil; the
// port uses `ctx.tp.checker`, and neither can be nil.
fn find_related_layer_provider_diagnostics(
    ctx: &mut RuleContext<'_, '_>,
    layer_node: Node,
    missing_types: &[TypeId],
) -> Vec<Diagnostic> {
    if layer_node.is_nil() || missing_types.is_empty() {
        return Vec::new();
    }
    let source_file = ctx.source_file;
    let root_layer_provides = root_layer_provides_types(ctx.tp, layer_node);
    let full_graph = layergraph::extract_layer_graph(
        ctx.tp,
        &[layer_node],
        source_file,
        layergraph::ExtractLayerGraphOptions {
            follow_symbols_depth: 2,
            ..Default::default()
        },
    );
    // PORT: Go checks the outline graph for nil; ExtractOutlineGraph never
    // returns nil.
    let outline_graph = layergraph::extract_outline_graph(ctx.tp, &full_graph);
    let outline_nodes: Vec<layergraph::LayerOutlineGraphNodeInfo> =
        outline_graph.nodes().map(|(_, n)| n.clone()).collect();
    let mut related = Vec::new();
    let mut seen: FxHashSet<String> = FxHashSet::default();
    for &missing_type in missing_types {
        if missing_type.is_nil() {
            continue;
        }
        if root_provides_type(ctx.tp.checker, &root_layer_provides, missing_type) {
            continue;
        }
        let missing_type_text = ctx.tp.checker.type_to_string_exported(missing_type);
        for node_info in &outline_nodes {
            let mut display_node = node_info.display_node;
            if display_node.is_nil() {
                display_node = node_info.node;
            }
            if display_node.is_nil()
                || !outline_node_provides_type(ctx.tp.checker, node_info, missing_type)
            {
                continue;
            }
            let mut key = missing_type_text.clone();
            if display_node.pos() >= 0 {
                key += &format!(":{}", display_node.pos());
            }
            if seen.contains(&key) {
                continue;
            }
            seen.insert(key);
            let display_source_file = get_source_file_of_node(display_node);
            related.push(ctx.new_diagnostic(
                display_source_file,
                get_error_range_for_node(display_source_file, display_node),
                diag::This_layer_provides_the_missing_service_0_effect_missingEffectContext,
                Vec::new(),
                vec![missing_type_text.clone()],
            ));
        }
    }
    related
}

// Go: rootLayerProvidesTypes
fn root_layer_provides_types(tp: &mut TypeParser<'_>, layer_node: Node) -> Vec<TypeId> {
    if layer_node.is_nil() {
        return Vec::new();
    }
    let layer_type_at_location = tp.get_type_at_location(layer_node);
    let Some(layer_type) = tp.layer_type(layer_type_at_location) else {
        return Vec::new();
    };
    tp.unroll_union_members(layer_type.r_out)
}

// Go: rootProvidesType
fn root_provides_type(c: &mut Checker, provided_types: &[TypeId], target: TypeId) -> bool {
    for &provided_type in provided_types {
        if provided_type == target {
            return true;
        }
        if c.is_type_assignable_to(provided_type, target)
            && c.is_type_assignable_to(target, provided_type)
        {
            return true;
        }
    }
    false
}

// Go: outlineNodeProvidesType
fn outline_node_provides_type(
    c: &mut Checker,
    node: &layergraph::LayerOutlineGraphNodeInfo,
    target: TypeId,
) -> bool {
    for &provided_type in &node.actual_provides {
        if provided_type == target {
            return true;
        }
        if c.is_type_assignable_to(provided_type, target)
            && c.is_type_assignable_to(target, provided_type)
        {
            return true;
        }
    }
    false
}

// Go: firstNode
fn first_node(nodes: &[Node]) -> Node {
    if nodes.is_empty() {
        return Node::NIL;
    }
    nodes[0]
}

// Go: findTransformationIndexContainingNode
// PORT: Go returns -1 for a nil flow; the port's flow is never nil.
fn find_transformation_index_containing_node(flow: &PipingFlow, target: Node) -> i32 {
    if target.is_nil() {
        return -1;
    }
    let target = skip_parentheses(target);
    for (i, transformation) in flow.transformations.iter().enumerate() {
        let callee = skip_parentheses(transformation.callee);
        if callee == target
            || callee.is_some() && callee.pos() == target.pos() && target.end() >= callee.end()
        {
            return i as i32;
        }
    }
    -1
}

// Go: nodeContains
fn node_contains(ancestor: Node, target: Node) -> bool {
    if ancestor.is_nil() || target.is_nil() {
        return false;
    }
    ancestor.pos() <= target.pos() && target.end() <= ancestor.end()
}
