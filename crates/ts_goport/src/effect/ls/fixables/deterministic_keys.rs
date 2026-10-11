//! Port of Effect-TS/tsgo `internal/fixables/deterministic_keys.go`.

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rules::deterministic_keys::analyze_deterministic_keys;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/deterministic_keys.go:12 DeterministicKeysFix
pub static DETERMINISTIC_KEYS_FIX: Fixable = Fixable {
    name: "deterministicKeys",
    description: "Replace key with expected deterministic key",
    // Go: tsdiag.This_key_does_not_match_the_deterministic_key_for_this_declaration_The_expected_key_is_0_effect_deterministicKeys
    error_codes: &[377049],
    fix_ids: &["deterministicKeys_fix"],
    run: run_deterministic_keys_fix,
};

// Go: fixables/deterministic_keys.go:20 runDeterministicKeysFix
// PORT: Go passes `ctx.Program`; the Rust analyzer takes the type parser's
// program, which is the same program.
fn run_deterministic_keys_fix(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let program = ctx.tp.program;
    let matches = analyze_deterministic_keys(ctx.tp, program, ctx.source_file, Some(ctx.options));
    for m in matches {
        if !m.location.intersects(ctx.span) && !ctx.span.contained_by(m.location) {
            continue;
        }

        // Determine the quote style from the original string literal
        let mut flags = TokenFlags::NONE;
        if m.key_string_literal
            .token_flags()
            .intersects(TokenFlags::SINGLE_QUOTE)
        {
            flags = TokenFlags::SINGLE_QUOTE;
        }

        let description = format!("Replace '{}' with '{}'", m.actual_key, m.expected_key);
        let sf = ctx.source_file;
        if let Some(action) = ctx.new_fix_action(description, |tracker| {
            let literal = tracker
                .node_factory()
                .new_string_literal(m.expected_key.as_str(), flags);
            tracker.replace_node(sf, m.key_string_literal, literal, None);
        }) {
            return vec![action];
        }
        return Vec::new();
    }

    Vec::new()
}
