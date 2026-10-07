//! Port of Effect-TS/tsgo `internal/rules/scope_in_layer_effect.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// ScopeInLayerEffect suggests using Layer.scoped instead of Layer.effect when
/// Scope is detected in the layer's requirements.
pub static SCOPE_IN_LAYER_EFFECT: Rule = Rule {
    name: "scopeInLayerEffect",
    group: "antipattern",
    description: "Suggests using Layer.scoped instead of Layer.effect when Scope is in requirements",
    default_severity: Severity::Warning,
    supported_effect: &["v3"],
    codes: &[377031],
    run: run_scope_in_layer_effect,
};

fn run_scope_in_layer_effect(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_scope_in_layer_effect(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_layer_construction_leaves_Scope_in_the_requirement_set_The_scoped_API_removes_Scope_from_the_resulting_requirements_effect_scopeInLayerEffect,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

/// ScopeInLayerEffectMatch holds the AST nodes needed by both the diagnostic rule
/// and the quick-fix for the scopeInLayerEffect pattern.
pub struct ScopeInLayerEffectMatch {
    pub source_file: Node,
    /// The pre-computed error range for this match
    pub location: TextRange,
    /// The Layer constructor callee; nil for class declaration matches
    pub callee: Node,
    /// The replaceable property name (e.g., "effect" in Layer.effect); nil for classes, named imports, and local aliases
    pub method_identifier: Node,
}

/// AnalyzeScopeInLayerEffect finds all Layer.effect*() calls and class declarations
/// with Default layer properties where Scope is in the layer's requirements.
// Go: rules/scope_in_layer_effect.go AnalyzeScopeInLayerEffect
pub fn analyze_scope_in_layer_effect(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<ScopeInLayerEffectMatch> {
    // V3-only rule
    if tp.supported_effect_version() != EffectMajorVersion::V3 {
        return Vec::new();
    }

    let mut matches = Vec::new();

    // Stack-based traversal
    let mut node_to_visit: Vec<Node> = Vec::new();
    sf.for_each_child(|child| {
        node_to_visit.push(child);
        false
    });

    while let Some(node) = node_to_visit.pop() {
        // Pattern 1: Layer.effect*() calls
        if node.kind() == SyntaxKind::CallExpression
            && let Some(m) = match_layer_effect_call(tp, sf, node)
        {
            matches.push(m);
            continue; // skip children
        }

        // Pattern 2: Class declarations with Default layer property
        if node.kind() == SyntaxKind::ClassDeclaration
            && let Some(m) = match_class_with_default_layer(tp, sf, node)
        {
            matches.push(m);
            continue; // skip children
        }

        // Enqueue children
        node.for_each_child(|child| {
            node_to_visit.push(child);
            false
        });
    }

    matches
}

/// matchLayerEffectCall checks if a call expression is Layer.effect*() with Scope in RIn.
// Go: rules/scope_in_layer_effect.go matchLayerEffectCall
fn match_layer_effect_call(
    tp: &mut TypeParser<'_>,
    sf: Node,
    node: Node,
) -> Option<ScopeInLayerEffectMatch> {
    if node.kind() != SyntaxKind::CallExpression {
        return None;
    }
    let call = node;
    if call.expression().is_nil() {
        return None;
    }

    // Verify this references one of the Layer.effect* constructors from the
    // "effect" package. Symbol resolution also recognizes named imports and
    // stable local aliases whose source spelling does not reveal the API name.
    let mut method_name = "";
    for candidate in ["effect", "effectDiscard", "effectContext"] {
        if tp.is_node_reference_to_effect_layer_module_api(call.expression(), candidate) {
            method_name = candidate;
            break;
        }
    }
    if method_name.is_empty() {
        return None;
    }

    // Get the return type of the call
    let t = tp.get_type_at_location(node);
    if t.is_nil() {
        return None;
    }

    // Parse as Layer type
    let layer = tp.layer_type(t)?;

    // Check if RIn contains a Scope type
    if !has_scope(tp, layer.r_in) {
        return None;
    }

    let mut method_identifier = Node::NIL;
    if call.expression().kind() == SyntaxKind::PropertyAccessExpression {
        method_identifier = call.expression().name();
    }
    Some(ScopeInLayerEffectMatch {
        source_file: sf,
        location: get_error_range_for_node(sf, node),
        callee: call.expression(),
        method_identifier,
    })
}

/// matchClassWithDefaultLayer checks if a class declaration has a Default layer property with Scope in RIn.
// Go: rules/scope_in_layer_effect.go matchClassWithDefaultLayer
fn match_class_with_default_layer(
    tp: &mut TypeParser<'_>,
    sf: Node,
    node: Node,
) -> Option<ScopeInLayerEffectMatch> {
    if node.kind() != SyntaxKind::ClassDeclaration {
        return None;
    }
    let class_decl = node;

    // Must have a name and heritage clauses
    if node.name().is_nil() || class_decl.heritage_clauses().is_nil() {
        return None;
    }

    // Get the class symbol
    let class_sym = tp.get_symbol_at_location(node.name());
    if class_sym.is_nil() {
        return None;
    }

    // Get the class type
    let class_type = tp.checker.get_type_of_symbol_at_location(class_sym, node);
    if class_type.is_nil() {
        return None;
    }

    // Check for a "Default" property
    let default_prop = tp
        .checker
        .get_property_of_type_exported(class_type, "Default");
    if default_prop.is_nil() {
        return None;
    }

    // Get the Default property's type
    let default_type = tp
        .checker
        .get_type_of_symbol_at_location(default_prop, node);
    if default_type.is_nil() {
        return None;
    }

    // Parse as Layer type
    let layer = tp.layer_type(default_type)?;

    // Check if RIn contains a Scope type
    if !has_scope(tp, layer.r_in) {
        return None;
    }

    Some(ScopeInLayerEffectMatch {
        source_file: sf,
        location: get_error_range_for_node(sf, node),
        callee: Node::NIL,
        method_identifier: Node::NIL,
    })
}

/// hasScope checks if any union member of the given type is a Scope type.
// Go: rules/scope_in_layer_effect.go hasScope
fn has_scope(tp: &mut TypeParser<'_>, t: TypeId) -> bool {
    let members = tp.unroll_union_members(t);
    members.into_iter().any(|member| tp.is_scope_type(member))
}
