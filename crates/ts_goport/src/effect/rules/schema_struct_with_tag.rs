//! Port of Effect-TS/tsgo `internal/rules/schema_struct_with_tag.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// SchemaStructWithTag detects Schema.Struct(...) calls where the argument
/// contains a _tag property assigned to Schema.Literal("someString"), and
/// suggests using Schema.TaggedStruct instead.
// Go: rules/schema_struct_with_tag.go SchemaStructWithTag
pub static SCHEMA_STRUCT_WITH_TAG: Rule = Rule {
    name: "schemaStructWithTag",
    group: "style",
    description: "Suggests using Schema.TaggedStruct instead of Schema.Struct with _tag field",
    default_severity: Severity::Suggestion,
    supported_effect: &["v3", "v4"],
    codes: &[377036],
    run: run_schema_struct_with_tag,
};

fn run_schema_struct_with_tag(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_schema_struct_with_tag(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in &matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_Schema_Struct_includes_a_tag_field_Schema_TaggedStruct_is_the_tagged_struct_form_for_this_pattern_and_makes_the_tag_optional_in_the_constructor_effect_schemaStructWithTag,
            Vec::new(),
            vec![],
        ));
    }
    diags
}

/// SchemaStructWithTagMatch holds the AST nodes needed by both the diagnostic rule
/// and the quick-fix for the schemaStructWithTag pattern.
// Go: rules/schema_struct_with_tag.go SchemaStructWithTagMatch
#[derive(Clone, Debug, Default)]
pub struct SchemaStructWithTagMatch {
    pub source_file: Node,
    /// Pre-computed error range for the diagnostic
    pub location: TextRange,
    /// The full Schema.Struct(...) call expression
    pub call_node: Node,
    /// The string value extracted from Schema.Literal("...")
    pub tag_value: String,
    /// All property assignment nodes in the object literal except _tag
    pub other_properties: Vec<Node>,
    /// The expression node for the Schema part of Schema.Struct
    pub schema_expr: Node,
}

/// AnalyzeSchemaStructWithTag finds all Schema.Struct({ _tag: Schema.Literal("..."), ... })
/// call expressions and returns match structs for each.
// Go: rules/schema_struct_with_tag.go AnalyzeSchemaStructWithTag
pub fn analyze_schema_struct_with_tag(
    tp: &mut TypeParser<'_>,
    sf: Node,
) -> Vec<SchemaStructWithTagMatch> {
    let mut matches: Vec<SchemaStructWithTagMatch> = Vec::new();

    // Stack-based traversal
    let mut node_to_visit: Vec<Node> = Vec::new();
    sf.for_each_child(|child| {
        node_to_visit.push(child);
        false
    });

    while let Some(node) = node_to_visit.pop() {
        if node.kind() == SyntaxKind::CallExpression {
            if let (m, true) = analyze_schema_struct_with_tag_node(tp, sf, node) {
                matches.push(m);
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

/// analyzeSchemaStructWithTagNode checks a call expression for Schema.Struct({ _tag: Schema.Literal("...") }).
// Go: rules/schema_struct_with_tag.go analyzeSchemaStructWithTagNode
fn analyze_schema_struct_with_tag_node(
    tp: &mut TypeParser<'_>,
    sf: Node,
    node: Node,
) -> (SchemaStructWithTagMatch, bool) {
    if node.kind() != SyntaxKind::CallExpression {
        return (SchemaStructWithTagMatch::default(), false);
    }
    let call = node;

    // Check if this is Schema.Struct
    if !tp.is_node_reference_to_effect_schema_module_api(call.expression(), "Struct") {
        return (SchemaStructWithTagMatch::default(), false);
    }

    // Must have exactly 1 argument
    if call.argument_list().is_nil() || call.arguments().len() != 1 {
        return (SchemaStructWithTagMatch::default(), false);
    }

    let arg = call.arguments().get(0);
    if arg.is_nil() || arg.kind() != SyntaxKind::ObjectLiteralExpression {
        return (SchemaStructWithTagMatch::default(), false);
    }

    let obj_lit = arg;
    if obj_lit.is_nil() || obj_lit.property_list().is_nil() {
        return (SchemaStructWithTagMatch::default(), false);
    }

    // Look for a _tag property assignment
    for prop in obj_lit.properties() {
        if prop.is_nil() || prop.kind() != SyntaxKind::PropertyAssignment {
            continue;
        }
        let pa = prop;
        if pa.is_nil() || pa.name().is_nil() {
            continue;
        }
        if pa.name().kind() != SyntaxKind::Identifier || get_text_of_node(pa.name()) != "_tag" {
            continue;
        }

        // Found _tag property — check if its initializer is Schema.Literal("...")
        let init = pa.initializer();
        if init.is_nil() || init.kind() != SyntaxKind::CallExpression {
            return (SchemaStructWithTagMatch::default(), false);
        }

        let literal_call = init;
        if !tp.is_node_reference_to_effect_schema_module_api(literal_call.expression(), "Literal") {
            return (SchemaStructWithTagMatch::default(), false);
        }

        // Schema.Literal must have exactly 1 argument that is a string literal
        if literal_call.argument_list().is_nil() || literal_call.arguments().len() != 1 {
            return (SchemaStructWithTagMatch::default(), false);
        }
        if literal_call.arguments().get(0).kind() != SyntaxKind::StringLiteral {
            return (SchemaStructWithTagMatch::default(), false);
        }

        let tag_value = literal_call.arguments().get(0).text().to_string();

        // Collect all properties except _tag
        let mut other_props: Vec<Node> = Vec::new();
        for p in obj_lit.properties() {
            if p == prop {
                continue;
            }
            other_props.push(p);
        }

        // Extract the Schema expression from Schema.Struct (the left side of the property access)
        let mut schema_expr = Node::NIL;
        if call.expression().kind() == SyntaxKind::PropertyAccessExpression {
            schema_expr = call.expression().expression();
        }

        return (
            SchemaStructWithTagMatch {
                source_file: sf,
                location: get_error_range_for_node(sf, node),
                call_node: node,
                tag_value,
                other_properties: other_props,
                schema_expr,
            },
            true,
        );
    }

    (SchemaStructWithTagMatch::default(), false)
}
