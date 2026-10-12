//! Port of Effect-TS/tsgo `internal/fixables/prefer_schema_type_property.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::prefer_schema_type_property::analyze_prefer_schema_type_property;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/prefer_schema_type_property.go:11 PreferSchemaTypePropertyFix
pub static PREFER_SCHEMA_TYPE_PROPERTY_FIX: Fixable = Fixable {
    name: "preferSchemaTypeProperty",
    description: "Replace with typeof X.Type",
    // Go: tsdiag.Do_not_use_Schema_Schema_Type_typeof_X_to_extract_a_schema_s_type_Use_typeof_X_Type_instead_effect_preferSchemaTypeProperty
    error_codes: &[377104],
    fix_ids: &["preferSchemaTypeProperty_fix"],
    run: run_prefer_schema_type_property_fix,
};

// Go: fixables/prefer_schema_type_property.go:19 runPreferSchemaTypePropertyFix
fn run_prefer_schema_type_property_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;
    let matches = analyze_prefer_schema_type_property(ctx.tp, sf);
    for m in matches {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }

        if let Some(action) = ctx.new_fix_action(
            format!("Replace with 'typeof {}.Type'", m.schema_name_text),
            |tracker| {
                let f = tracker.node_factory();
                let schema_type = f
                    .new_qualified_name(f.deep_clone_node(m.schema_name), f.new_identifier("Type"));
                let replacement = f.new_type_query_node(schema_type, NodeList::NIL);
                tracker.replace_node(sf, m.type_reference, replacement, None);
            },
        ) {
            return vec![action];
        }
        return Vec::new();
    }

    Vec::new()
}
