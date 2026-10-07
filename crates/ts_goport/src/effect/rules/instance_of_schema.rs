//! Port of Effect-TS/tsgo `internal/rules/instance_of_schema.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

/// InstanceOfSchema suggests using Schema.is instead of instanceof for Effect Schema types.
/// This rule is disabled by default.
pub static INSTANCE_OF_SCHEMA: Rule = Rule {
    name: "instanceOfSchema",
    group: "effectNative",
    description: "Suggests using Schema.is instead of instanceof for Effect Schema types",
    default_severity: Severity::Off,
    supported_effect: &["v3", "v4"],
    codes: &[377042],
    run: run_instance_of_schema,
};

fn run_instance_of_schema(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let matches = analyze_instance_of_schema(ctx.tp, ctx.source_file);
    let mut diags = Vec::with_capacity(matches.len());
    for m in matches {
        diags.push(ctx.new_diagnostic(
            m.source_file,
            m.location,
            diag::This_code_uses_instanceof_with_an_Effect_Schema_type_Schema_is_is_the_schema_aware_runtime_check_for_this_case_effect_instanceOfSchema,
            Vec::new(),
            Vec::new(),
        ));
    }
    diags
}

/// InstanceOfSchemaMatch holds the AST nodes needed by both the diagnostic rule
/// and the quick-fix for the instanceOfSchema pattern.
pub struct InstanceOfSchemaMatch {
    pub source_file: Node,
    /// The pre-computed error range for this match
    pub location: TextRange,
    /// The full BinaryExpression node (the instanceof expression)
    pub instance_of_node: Node,
    /// Left operand of instanceof (the value being tested)
    pub left_expr: Node,
    /// Right operand of instanceof (the schema type reference)
    pub right_expr: Node,
}

/// AnalyzeInstanceOfSchema finds all `value instanceof SchemaClass` expressions
/// where the right-hand side is an Effect Schema type.
// Go: rules/instance_of_schema.go AnalyzeInstanceOfSchema
pub fn analyze_instance_of_schema(tp: &mut TypeParser<'_>, sf: Node) -> Vec<InstanceOfSchemaMatch> {
    let mut matches = Vec::new();

    // Stack-based traversal
    let mut node_to_visit: Vec<Node> = Vec::new();
    sf.for_each_child(|child| {
        node_to_visit.push(child);
        false
    });

    while let Some(node) = node_to_visit.pop() {
        if is_instance_of_expression(node) {
            let bin_expr = node;
            let right_expr = bin_expr.right();
            let right_type = tp.get_type_at_location(right_expr);
            if right_type.is_some() && tp.is_schema_type(right_type) {
                matches.push(InstanceOfSchemaMatch {
                    source_file: sf,
                    location: get_error_range_for_node(sf, node),
                    instance_of_node: node,
                    left_expr: bin_expr.left(),
                    right_expr,
                });
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
