//! Port of Effect-TS/tsgo `internal/fixables/schema_number.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::schema_number::analyze_schema_number;
use crate::ls::CodeAction;
use crate::lsp::lsproto;
use crate::prelude::*;

// Go: fixables/schema_number.go:13 SchemaNumberFix
pub static SCHEMA_NUMBER_FIX: Fixable = Fixable {
    name: "schemaNumber",
    description: "Replace Schema.Number APIs with finite variants",
    // Go: tsdiag.This_Schema_number_API_accepts_NaN_Infinity_and_Infinity_Use_0_for_finite_domain_numbers_If_non_finite_values_are_intentional_disable_this_diagnostic_for_that_line_effect_schemaNumber
    error_codes: &[377098],
    fix_ids: &["schemaNumber_fix"],
    run: run_schema_number_fix,
};

// Go: fixables/schema_number.go:21 runSchemaNumberFix
fn run_schema_number_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let matches = analyze_schema_number(ctx.tp, ctx.source_file);
    for m in matches {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        if m.reference_node.is_nil() || m.reference_node.kind() != SyntaxKind::Identifier {
            continue;
        }
        if m.reference_node.parent().is_nil()
            || m.reference_node.parent().kind() != SyntaxKind::PropertyAccessExpression
        {
            continue;
        }

        let reference_node = m.reference_node;
        let replacement = m.replacement_identifier;
        let description = format!("Replace with {}", m.replacement);
        let sf = ctx.source_file;
        let range = lsproto::Range {
            start: ctx.byte_pos_to_lsp_position(reference_node.pos()),
            end: ctx.byte_pos_to_lsp_position(reference_node.end()),
        };
        if let Some(action) = ctx.new_fix_action(description, |tracker| {
            tracker.replace_range_with_text(sf, range, &replacement);
        }) {
            return vec![action];
        }
        return Vec::new();
    }

    Vec::new()
}
