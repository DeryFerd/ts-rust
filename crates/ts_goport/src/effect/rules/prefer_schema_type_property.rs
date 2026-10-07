//! Port of Effect-TS/tsgo `internal/rules/prefer_schema_type_property.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

pub static PREFER_SCHEMA_TYPE_PROPERTY: Rule = Rule {
    name: "preferSchemaTypeProperty",
    group: "style",
    description: "Disallows Schema.Schema.Type<typeof X> in favor of typeof X.Type",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377104],
    run: run_prefer_schema_type_property,
};

fn run_prefer_schema_type_property(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_prefer_schema_type_property(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::Do_not_use_Schema_Schema_Type_typeof_X_to_extract_a_schema_s_type_Use_typeof_X_Type_instead_effect_preferSchemaTypeProperty,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

pub struct PreferSchemaTypePropertyMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub type_reference: Node,
    pub schema_name: Node,
    pub schema_name_text: String,
}

// Go: rules/prefer_schema_type_property.go AnalyzePreferSchemaTypeProperty
pub fn analyze_prefer_schema_type_property(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<PreferSchemaTypePropertyMatch> {
    let mut matches = Vec::new();
    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        node: Node,
        matches: &mut Vec<PreferSchemaTypePropertyMatch>,
    ) -> bool {
        if node.is_nil() {
            return false;
        }
        if node.kind() == SyntaxKind::TypeReference
            && let Some(m) = analyze_prefer_schema_type_property_node(tp, sf, node)
        {
            matches.push(m);
            return false;
        }
        node.for_each_child(|child| walk(tp, sf, child, matches));
        false
    }
    walk(tp, sf, sf, &mut matches);
    matches
}

// Go: rules/prefer_schema_type_property.go analyzePreferSchemaTypePropertyNode
fn analyze_prefer_schema_type_property_node(
    tp: &mut TypeParser<'_>,
    sf: Node,
    node: Node,
) -> Option<PreferSchemaTypePropertyMatch> {
    let reference = node;
    if reference.type_name().is_nil()
        || reference.type_argument_list().is_nil()
        || reference.type_argument_list().nodes().len() != 1
    {
        return None;
    }

    let type_name = reference.type_name();
    if type_name.is_nil() || type_name.kind() != SyntaxKind::QualifiedName {
        return None;
    }
    let outer_name = type_name;
    if outer_name.right().is_nil()
        || outer_name.right().text() != "Type"
        || outer_name.left().is_nil()
    {
        return None;
    }
    let middle_name = outer_name.left();
    if middle_name.is_nil() || middle_name.kind() != SyntaxKind::QualifiedName {
        return None;
    }
    let schema_export = middle_name.right();
    if schema_export.is_nil()
        || !tp.is_node_reference_to_effect_schema_module_api(schema_export, "Schema")
    {
        return None;
    }

    let type_argument = reference.type_argument_list().nodes().get(0);
    if type_argument.is_nil() || type_argument.kind() != SyntaxKind::TypeQuery {
        return None;
    }
    let query = type_argument;
    if query.expr_name().is_nil()
        || query.type_argument_list().is_some() && !query.type_argument_list().nodes().is_empty()
    {
        return None;
    }

    Some(PreferSchemaTypePropertyMatch {
        source_file: sf,
        location: get_error_range_for_node(sf, node),
        type_reference: node,
        schema_name: query.expr_name(),
        schema_name_text: get_text_of_node(query.expr_name()),
    })
}
