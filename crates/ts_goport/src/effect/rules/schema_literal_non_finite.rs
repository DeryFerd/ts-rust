//! Port of Effect-TS/tsgo `internal/rules/schema_literal_non_finite.go`.

use crate::effect::diag;
use crate::effect::etscore::*;
use crate::effect::rule::*;
use crate::effect::typeparser::*;
use crate::prelude::*;

// Go: rules/schema_literal_non_finite.go SchemaLiteralNonFinite
pub static SCHEMA_LITERAL_NON_FINITE: Rule = Rule {
    name: "schemaLiteralNonFinite",
    group: "correctness",
    description: "Reports statically known non-finite numbers passed to Schema literal constructors",
    default_severity: Severity::Error,
    supported_effect: &["v4"],
    codes: &[377106],
    run: run_schema_literal_non_finite,
};

fn run_schema_literal_non_finite(ctx: &mut RuleContext<'_, '_>) -> Vec<Diagnostic> {
    let mut diags = Vec::new();

    fn visit(ctx: &mut RuleContext<'_, '_>, diags: &mut Vec<Diagnostic>, node: Node) {
        if node.kind() == SyntaxKind::CallExpression {
            let call = node;
            if call.is_some() && call.argument_list().is_some() && !call.arguments().is_empty() {
                let mut values: Vec<Node> = Vec::new();
                if ctx.tp.is_node_reference_to_effect_schema_module_api(
                    call.expression(),
                    member!("Literals"),
                ) {
                    let arg = call.arguments().get(0);
                    if arg.is_some() && arg.kind() == SyntaxKind::ArrayLiteralExpression {
                        values = arg.elements().to_vec();
                    }
                } else if ctx.tp.is_node_reference_to_effect_schema_module_api(
                    call.expression(),
                    member!("Literal"),
                ) || ctx.tp.is_node_reference_to_effect_schema_module_api(
                    call.expression(),
                    member!("tag"),
                ) {
                    values = vec![call.arguments().get(0)];
                }

                for value in values {
                    let (n, ok) = ctx.tp.evaluate_constant_number(value, value);
                    if ok && (n.is_infinite() || n.is_nan()) {
                        let sf = ctx.source_file;
                        diags.push(ctx.new_diagnostic(
                            sf,
                            get_error_range_for_node(sf, value),
                            diag::Schema_literal_values_must_be_finite_numbers_0_throws_during_schema_construction_Use_a_finite_literal_or_model_non_finite_values_with_a_refined_Schema_Number_effect_schemaLiteralNonFinite,
                            Vec::new(),
                            vec![get_text_of_node(value)],
                        ));
                    }
                }
            }
        }
    }

    let sf = ctx.source_file;
    // PERF: Go walks the tree; the node order has the same nodes in the same
    // order (effperf4).
    for &n in ctx.tp.node_order(sf).nodes() {
        visit(ctx, &mut diags, n);
    }
    diags
}
