//! Port of Effect-TS/tsgo `internal/refactors/wrap_with_effect_gen.go`.

use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::with_kind;
use crate::effect::typeparser::find_effect_module_identifier;
use crate::ls::CodeAction;
use crate::lsp::lsproto;
use crate::prelude::*;

// Go: refactors/wrap_with_effect_gen.go:13 WrapWithEffectGen
pub static WRAP_WITH_EFFECT_GEN: Refactor = Refactor {
    name: "wrapWithEffectGen",
    description: "Wrap with Effect.gen",
    kind: "rewrite.effect.wrapWithEffectGen",
    run: run_wrap_with_effect_gen,
};

// Go: refactors/wrap_with_effect_gen.go:20 runWrapWithEffectGen
fn run_wrap_with_effect_gen(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let token = astnav::get_token_at_position(ctx.source_file, ctx.span.pos());
    if token.is_nil() {
        return Vec::new();
    }

    // Walk ancestor chain looking for an expression whose type is a strict Effect type
    let mut matched_node = Node::NIL;
    let mut node = token;
    while node.is_some() {
        let current = node;
        node = node.parent();
        if !is_expression(current) {
            continue;
        }
        // Skip nodes inside heritage clauses (class extends/implements)
        if is_in_heritage_clause(current) {
            continue;
        }
        // Skip if this is the LHS of a variable declaration (not the initializer)
        let parent = current.parent();
        if parent.is_some()
            && parent.kind() == SyntaxKind::VariableDeclaration
            && parent.initializer() != current
        {
            continue;
        }

        let node_type = ctx.tp.get_type_at_location(current);
        if node_type.is_nil() {
            continue;
        }
        if !ctx.tp.strict_is_effect_type(node_type) {
            continue;
        }
        if ctx.tp.effect_gen_call(current).is_some() {
            continue;
        }

        matched_node = current;
        break;
    }

    if matched_node.is_nil() {
        return Vec::new();
    }

    let effect_module_name = find_effect_module_identifier(ctx.source_file);

    let sf = ctx.source_file;
    let start = astnav::get_start_of_node(matched_node, sf, false);
    let text_range = source_file_text(sf)[start as usize..matched_node.end() as usize].to_string();
    let wrapped = effect_module_name + ".gen(function*() { return yield* " + &text_range + " })";
    let range = lsproto::Range {
        start: ctx.byte_pos_to_lsp_position(start),
        end: ctx.byte_pos_to_lsp_position(matched_node.end()),
    };
    let action = ctx.new_refactor_action("Wrap with Effect.gen", |tracker| {
        tracker.replace_range_with_text(sf, range, &wrapped);
    });
    with_kind(action, "refactor.rewrite.effect.wrapWithEffectGen")
}

// Go: refactors/wrap_with_effect_gen.go:86 isInHeritageClause
// isInHeritageClause checks if a node is inside a heritage clause (extends/implements).
fn is_in_heritage_clause(node: Node) -> bool {
    let mut parent = node.parent();
    while parent.is_some() {
        if parent.kind() == SyntaxKind::HeritageClause {
            return true;
        }
        // Stop walking once we hit a statement or declaration boundary
        if parent.kind() == SyntaxKind::ClassDeclaration || parent.kind() == SyntaxKind::SourceFile
        {
            return false;
        }
        parent = parent.parent();
    }
    false
}
