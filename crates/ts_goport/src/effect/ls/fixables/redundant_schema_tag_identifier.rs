//! Port of Effect-TS/tsgo `internal/fixables/redundant_schema_tag_identifier.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::redundant_schema_tag_identifier::analyze_redundant_schema_tag_identifier;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/redundant_schema_tag_identifier.go:15 RedundantSchemaTagIdentifierRemoveIdentifierFix
pub static REDUNDANT_SCHEMA_TAG_IDENTIFIER_REMOVE_IDENTIFIER_FIX: Fixable = Fixable {
    name: "redundantSchemaTagIdentifier",
    description: "Remove redundant identifier",
    // Go: tsdiag.Identifier_0_is_redundant_since_it_equals_the_tag_value_effect_redundantSchemaTagIdentifier
    error_codes: &[377045],
    fix_ids: &["redundantSchemaTagIdentifier_removeIdentifier"],
    run: run_redundant_schema_tag_identifier_fix,
};

// Go: fixables/redundant_schema_tag_identifier.go:23 runRedundantSchemaTagIdentifierFix
fn run_redundant_schema_tag_identifier_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;

    let matches = analyze_redundant_schema_tag_identifier(ctx.tp, sf);
    for m in matches {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }

        // PORT: Go `KeyStringLiteral.AsStringLiteral().Text`; the analyzer
        // keeps only StringLiteral keys.
        let key_text = m.key_string_literal.text();
        let key_node = m.key_string_literal;

        if let Some(action) = ctx.new_fix_action(
            format!("Remove redundant identifier '{key_text}'"),
            |tracker| {
                let token_pos = get_token_pos_of_node(key_node, sf, false);
                tracker.delete_range(sf, TextRange::new(token_pos, key_node.end()));
            },
        ) {
            return vec![action];
        }
        return Vec::new();
    }

    Vec::new()
}
