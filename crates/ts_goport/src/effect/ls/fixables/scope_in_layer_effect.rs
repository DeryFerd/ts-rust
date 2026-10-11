//! Port of Effect-TS/tsgo `internal/fixables/scope_in_layer_effect.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::scope_in_layer_effect::analyze_scope_in_layer_effect;
use crate::effect::typeparser::find_module_identifier;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/scope_in_layer_effect.go:13 ScopeInLayerEffectScopedFix
pub static SCOPE_IN_LAYER_EFFECT_SCOPED_FIX: Fixable = Fixable {
    name: "scopeInLayerEffectScoped",
    description: "Use scoped for Layer creation",
    // Go: tsdiag.This_layer_construction_leaves_Scope_in_the_requirement_set_The_scoped_API_removes_Scope_from_the_resulting_requirements_effect_scopeInLayerEffect
    error_codes: &[377031],
    fix_ids: &["scopeInLayerEffect_scoped"],
    run: run_scope_in_layer_effect_scoped_fix,
};

// Go: fixables/scope_in_layer_effect.go:21 runScopeInLayerEffectScopedFix
fn run_scope_in_layer_effect_scoped_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let matches = analyze_scope_in_layer_effect(ctx.tp, ctx.source_file);
    for m in matches {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }

        // Class declaration matches don't have a constructor callee to replace.
        if m.callee.is_nil() {
            continue;
        }

        let sf = ctx.source_file;

        if let Some(action) =
            ctx.new_fix_action("Use scoped for Layer creation".to_string(), |tracker| {
                if m.method_identifier.is_some() {
                    let scoped = tracker.node_factory().new_identifier("scoped");
                    tracker.replace_node(sf, m.method_identifier, scoped, None);
                } else {
                    let f = tracker.node_factory();
                    let layer_module = f.new_identifier(find_module_identifier(sf, "Layer"));
                    let scoped = f.new_property_access_expression(
                        layer_module,
                        Node::NIL,
                        f.new_identifier("scoped"),
                        NodeFlags::NONE,
                    );
                    tracker.replace_node(sf, m.callee, scoped, None);
                }
            })
        {
            return vec![action];
        }
        return Vec::new();
    }

    Vec::new()
}
