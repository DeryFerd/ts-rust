//! Port of Effect-TS/tsgo `internal/rules/new_schema_class.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// NewSchemaClass suggests using the Schema make API instead of direct
/// construction with new for Schema classes.
pub static NEW_SCHEMA_CLASS: Rule = Rule {
    name: "newSchemaClass",
    group: "style",
    description: "Suggests using Schema make instead of new for Schema classes",
    default_severity: Severity::Off,
    supported_effect: &["v4"],
    codes: &[377094],
    run: run_new_schema_class,
};

fn run_new_schema_class(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_new_schema_class(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_Schema_class_is_constructed_with_new_0_make_can_be_used_to_construct_the_Schema_class_instance_effect_newSchemaClass,
            Vec::new(),
            args![m.class_text],
        ));
    }
    diags
}

pub struct NewSchemaClassMatch {
    pub source_file: Node,
    pub location: TextRange,
    pub new_node: Node,
    pub class_expr: Node,
    pub class_text: String,
    pub arguments: Vec<Node>,
}

// Go: rules/new_schema_class.go AnalyzeNewSchemaClass
pub fn analyze_new_schema_class(tp: &mut TypeParser<'_>, sf: Node) -> Vec<NewSchemaClassMatch> {
    if tp.supported_effect_version() != EffectMajorVersion::V4 {
        return Vec::new();
    }

    let mut matches = Vec::new();

    fn walk(
        tp: &mut TypeParser<'_>,
        sf: Node,
        node: Node,
        matches: &mut Vec<NewSchemaClassMatch>,
    ) -> bool {
        if node.is_nil() {
            return false;
        }

        if node.kind() == SyntaxKind::NewExpression {
            let new_expr = node;
            if new_expr.expression().is_some()
                && is_v4_schema_class_expression(tp, new_expr.expression())
            {
                let mut args = Vec::new();
                if new_expr.argument_list().is_some() {
                    args = new_expr.arguments().to_vec();
                }
                matches.push(NewSchemaClassMatch {
                    source_file: sf,
                    location: get_error_range_for_node(sf, new_expr.expression()),
                    new_node: node,
                    class_expr: new_expr.expression(),
                    class_text: get_source_text_of_node_from_source_file(
                        sf,
                        new_expr.expression(),
                        false,
                    ),
                    arguments: args,
                });
            }
        }

        node.for_each_child(|child| walk(tp, sf, child, matches));
        false
    }

    walk(tp, sf, sf, &mut matches);
    matches
}

// Go: rules/new_schema_class.go isV4SchemaClassExpression
fn is_v4_schema_class_expression(tp: &mut TypeParser<'_>, expr: Node) -> bool {
    if expr.is_nil() {
        return false;
    }

    let t = tp.get_type_at_location(expr);
    if t.is_nil() || !tp.is_schema_type(t) {
        return false;
    }

    if tp
        .checker
        .get_signatures_of_type(t, SignatureKind::CONSTRUCT)
        .is_empty()
    {
        return false;
    }

    tp.get_type_of_property_by_name(t, "make").is_some()
}
