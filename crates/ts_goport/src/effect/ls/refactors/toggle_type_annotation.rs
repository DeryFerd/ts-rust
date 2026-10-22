//! Port of Effect-TS/tsgo `internal/refactors/toggle_type_annotation.go`.

use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::with_kind;
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: refactors/toggle_type_annotation.go:13 ToggleTypeAnnotation
pub static TOGGLE_TYPE_ANNOTATION: Refactor = Refactor {
    name: "toggleTypeAnnotation",
    description: "Toggle type annotation",
    kind: "rewrite.effect.toggleTypeAnnotation",
    run: run_toggle_type_annotation,
};

// Go: refactors/toggle_type_annotation.go:20 runToggleTypeAnnotation
// PORT: Go reads the name, type and initializer through
// `AsVariableDeclaration` or `AsPropertyDeclaration`; the Rust accessors
// are the same for both kinds.
fn run_toggle_type_annotation(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let token = astnav::get_token_at_position(ctx.source_file, ctx.span.pos());
    if token.is_nil() {
        return Vec::new();
    }

    // Walk ancestor chain looking for a VariableDeclaration or PropertyDeclaration
    let mut matched_node = Node::NIL;
    let mut node = token;
    while node.is_some() {
        let current = node;
        node = node.parent();
        if current.kind() != SyntaxKind::VariableDeclaration
            && current.kind() != SyntaxKind::PropertyDeclaration
        {
            continue;
        }

        // Must have an initializer
        let initializer = current.initializer();
        let name = current.name();

        if initializer.is_nil() || name.is_nil() {
            continue;
        }

        // Cursor must be on the name
        let name_pos = astnav::get_start_of_node(name, ctx.source_file, false);
        let name_end = name.end();
        if ctx.span.pos() < name_pos || ctx.span.pos() > name_end {
            continue;
        }

        matched_node = current;
        break;
    }

    if matched_node.is_nil() {
        return Vec::new();
    }

    // Get name and type nodes
    let name = matched_node.name();
    let type_node = matched_node.type_();
    let initializer = matched_node.initializer();

    let sf = ctx.source_file;
    if type_node.is_some() {
        // Remove existing type annotation: delete from name.End() to type.End()
        let action = ctx.new_refactor_action("Toggle type annotation", |tracker| {
            tracker.delete_range(sf, TextRange::new(name.end(), type_node.end()));
        });
        return with_kind(action, "refactor.rewrite.effect.toggleTypeAnnotation");
    }

    // Add type annotation: infer type from initializer and insert after name
    let initializer_type = ctx.tp.get_type_at_location(initializer);
    if initializer_type.is_nil() {
        return Vec::new();
    }

    let type_str = ctx.tp.checker.type_to_string_ex(
        initializer_type,
        matched_node,
        TypeFormatFlags::NO_TRUNCATION,
        None,
    );
    if type_str.is_empty() {
        return Vec::new();
    }

    let pos = ctx.byte_pos_to_lsp_position(name.end());
    let action = ctx.new_refactor_action("Toggle type annotation", |tracker| {
        tracker.insert_text(sf, pos, &(": ".to_string() + &type_str));
    });
    with_kind(action, "refactor.rewrite.effect.toggleTypeAnnotation")
}
