//! Port of Effect-TS/tsgo `internal/fixables/unnecessary_arrow_block.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::unnecessary_arrow_block::analyze_unnecessary_arrow_block;
use crate::ls::CodeAction;
use crate::prelude::*;
use crate::scanner_util::get_source_text_of_node_from_source_file;

// Go: fixables/unnecessary_arrow_block.go:13 UnnecessaryArrowBlockFix
pub static UNNECESSARY_ARROW_BLOCK_FIX: Fixable = Fixable {
    name: "unnecessaryArrowBlock",
    description: "Use a concise arrow body",
    // Go: tsdiag.This_arrow_function_block_only_returns_an_expression_and_can_use_a_concise_body_effect_unnecessaryArrowBlock
    error_codes: &[377084],
    fix_ids: &["unnecessaryArrowBlock_fix"],
    run: run_unnecessary_arrow_block_fix,
};

// Go: fixables/unnecessary_arrow_block.go:21 runUnnecessaryArrowBlockFix
fn run_unnecessary_arrow_block_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let sf = ctx.source_file;
    let matches = analyze_unnecessary_arrow_block(ctx.tp, sf);

    for m in matches {
        let diag_range = m.location;
        if !diag_range.intersects(ctx.span) && !ctx.span.contained_by(diag_range) {
            continue;
        }

        let replacement_text = format!(
            "({})",
            get_source_text_of_node_from_source_file(sf, m.returned_expression, false)
        );
        let insert_at = ctx.byte_pos_to_lsp_position(m.body_block.pos());
        if let Some(action) =
            ctx.new_fix_action("Use a concise arrow body".to_string(), |tracker| {
                tracker.delete_range(sf, TextRange::new(m.body_block.pos(), m.body_block.end()));
                tracker.insert_text(sf, insert_at, &replacement_text);
            })
        {
            return vec![action];
        }
        return Vec::new();
    }

    Vec::new()
}
