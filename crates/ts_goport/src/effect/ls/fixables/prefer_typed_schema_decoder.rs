//! Port of Effect-TS/tsgo `internal/fixables/prefer_typed_schema_decoder.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::prefer_typed_schema_decoder::analyze_prefer_typed_schema_decoder;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/prefer_typed_schema_decoder.go:12 PreferTypedSchemaDecoderFix
pub static PREFER_TYPED_SCHEMA_DECODER_FIX: Fixable = Fixable {
    name: "preferTypedSchemaDecoder",
    description: "Replace the unknown-input Schema decoder with its typed variant",
    // Go: tsdiag.This_input_is_already_assignable_to_the_schema_s_Encoded_type_Use_0_to_preserve_compile_time_type_checking_instead_of_discarding_the_input_type_through_1_effect_preferTypedSchemaDecoder
    error_codes: &[377112],
    fix_ids: &["preferTypedSchemaDecoder_fix"],
    run: run_prefer_typed_schema_decoder_fix,
};

// Go: fixables/prefer_typed_schema_decoder.go:22 runPreferTypedSchemaDecoderFix
fn run_prefer_typed_schema_decoder_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;
    for m in analyze_prefer_typed_schema_decoder(ctx.tp, sf) {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }
        let parent = m.decoder_name.parent();
        if parent.is_nil() || parent.kind() != SyntaxKind::PropertyAccessExpression {
            continue;
        }
        if let Some(action) =
            ctx.new_fix_action(format!("Replace with {}", m.typed_name), |tracker| {
                let typed_name = tracker.node_factory().new_identifier(m.typed_name.as_str());
                tracker.replace_node(sf, m.decoder_name, typed_name, None);
            })
        {
            return vec![action];
        }
    }
    Vec::new()
}
