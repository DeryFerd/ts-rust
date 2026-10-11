//! Port of Effect-TS/tsgo `internal/fixables/disable.go`.

use std::sync::LazyLock;

use crate::effect::ls::fixable::{Fixable, FixableContext};
use crate::effect::rule::{Rule, code_to_rule_name};
use crate::effect::rules;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: fixables/disable.go:17 EffectDisable
/// EffectDisable provides "disable for line/file" actions for all Effect diagnostics.
/// This fixable handles all Effect diagnostic codes and provides two actions:
/// 1. "Disable {ruleName} for this line" - inserts @effect-diagnostics-next-line directive
/// 2. "Disable {ruleName} for entire file" - inserts `/** @effect-diagnostics {ruleName}:off */`
///    at the top of the file
// PORT: Go's comment (disable.go:16) says the file action inserts a
// `skip-file` directive; its code (`createDisableFileAction`) inserts the
// `{ruleName}:off` directive above, which this port does.
// PORT: a `LazyLock` because its codes are `rule.AllCodes(rules.All)`. The
// list is made once and lives for the process.
pub static EFFECT_DISABLE: LazyLock<Fixable> = LazyLock::new(|| Fixable {
    name: "effectDisable",
    description: "Disable Effect diagnostics via directive comments",
    error_codes: all_codes(rules::ALL).leak(),
    fix_ids: &["effectDisableNextLine", "effectDisableFile"],
    run: run_effect_disable,
});

// Go: rule/rule.go:57 AllCodes
/// AllCodes returns the codes of all rules, in rule order.
// PORT: Go `internal/rule`; only the disable fix uses it, so it lives here.
fn all_codes(rules: &[&Rule]) -> Vec<i32> {
    rules.iter().flat_map(|r| r.codes.iter().copied()).collect()
}

// Go: fixables/disable.go:26 runEffectDisable
/// runEffectDisable generates disable actions for Effect diagnostics.
fn run_effect_disable(ctx: &mut FixableContext<'_, '_>) -> Vec<CodeAction> {
    let rule_name = code_to_rule_name(rules::ALL, ctx.error_code);
    if rule_name.is_empty() {
        return Vec::new();
    }

    let mut actions = Vec::new();

    // "Disable for this line" action
    if let Some(action) = create_disable_next_line_action(ctx, rule_name) {
        actions.push(action);
    }

    // "Disable for entire file" action
    if let Some(action) = create_disable_file_action(ctx, rule_name) {
        actions.push(action);
    }

    actions
}

// Go: fixables/disable.go:49 createDisableNextLineAction
/// createDisableNextLineAction creates a code action to disable the diagnostic for the next line.
/// It inserts: // @effect-diagnostics-next-line {ruleName}:off
fn create_disable_next_line_action(
    ctx: &FixableContext<'_, '_>,
    rule_name: &str,
) -> Option<CodeAction> {
    let source_file = ctx.source_file;
    let span = ctx.span;

    // Find the start of the line containing the diagnostic
    let line_start_pos = get_line_start_position_for_position(span.pos(), source_file);

    // Get the indentation at this position
    let indent = get_indentation_at_position(source_file, line_start_pos);

    // Create the comment text with proper indentation
    let comment = format!("{indent}// @effect-diagnostics-next-line {rule_name}:off\n");

    // Insert at the start of the line
    let mut insert_pos = ctx.byte_pos_to_lsp_position(line_start_pos);
    // Character must be 0 since we're inserting at line start with full indentation in the text
    insert_pos.character = 0;

    ctx.new_fix_action(format!("Disable {rule_name} for this line"), |tracker| {
        tracker.insert_text(source_file, insert_pos, &comment);
    })
}

// Go: fixables/disable.go:77 createDisableFileAction
/// createDisableFileAction creates a code action to disable the diagnostic for the entire file.
/// It inserts: /** @effect-diagnostics {ruleName}:off */ at the top of the file.
fn create_disable_file_action(ctx: &FixableContext<'_, '_>, rule_name: &str) -> Option<CodeAction> {
    // Create the comment text (uses :off for consistency with next-line directives)
    let comment = format!("/** @effect-diagnostics {rule_name}:off */\n");

    // Insert at the very beginning of the file (position 0)
    let insert_pos = ctx.byte_pos_to_lsp_position(0);

    let source_file = ctx.source_file;
    ctx.new_fix_action(format!("Disable {rule_name} for entire file"), |tracker| {
        tracker.insert_text(source_file, insert_pos, &comment);
    })
}

// Go: fixables/disable.go:93 getLineStartPositionForPosition
/// getLineStartPositionForPosition finds the start of the line containing the given position.
fn get_line_start_position_for_position(pos: i32, source_file: Node) -> i32 {
    let text = source_file_text(source_file);
    let text = text.as_bytes();
    if pos <= 0 || pos as usize > text.len() {
        return 0;
    }
    // Walk backwards to find the newline
    for i in (0..pos as usize).rev() {
        if text[i] == b'\n' {
            return i as i32 + 1;
        }
    }
    0
}

// Go: fixables/disable.go:108 getIndentationAtPosition
/// getIndentationAtPosition returns the whitespace characters from line start to the first non-whitespace.
fn get_indentation_at_position(source_file: Node, line_start_pos: i32) -> String {
    let text = source_file_text(source_file);
    let start = line_start_pos as usize;
    if start >= text.len() {
        return String::new();
    }

    // Find the end of indentation (first non-whitespace character or end of line)
    let end = start
        + text.as_bytes()[start..]
            .iter()
            .take_while(|&&ch| ch == b' ' || ch == b'\t')
            .count();

    text[start..end].to_string()
}
