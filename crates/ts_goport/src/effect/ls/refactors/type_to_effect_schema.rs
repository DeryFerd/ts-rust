//! Port of Effect-TS/tsgo `internal/refactors/type_to_effect_schema.go`.

use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::with_kind;
use crate::effect::ls::schemagen::SchemaGen;
use crate::ls::CodeAction;
use crate::ls::change::LeadingTriviaOption;
use crate::prelude::*;

// Go: refactors/type_to_effect_schema.go:12 TypeToEffectSchema
pub static TYPE_TO_EFFECT_SCHEMA: Refactor = Refactor {
    name: "typeToEffectSchema",
    description: "Generate Effect.Schema from type",
    kind: "rewrite.effect.typeToEffectSchema",
    run: run_type_to_effect_schema,
};

// Go: refactors/type_to_effect_schema.go:22 findInterfaceOrTypeAlias
/// findInterfaceOrTypeAlias walks the ancestor chain from the token at the cursor
/// to find an InterfaceDeclaration or TypeAliasDeclaration whose name overlaps the
/// selection span, and that has no type parameters.
// PORT: Go has one switch arm per kind with the same body; the Rust
// accessors are the same for both kinds.
pub(crate) fn find_interface_or_type_alias(ctx: &RefactorContext<'_, '_>) -> Node {
    let token = astnav::get_token_at_position(ctx.source_file, ctx.span.pos());
    if token.is_nil() {
        return Node::NIL;
    }

    let mut node = token;
    while node.is_some() && node.kind() != SyntaxKind::SourceFile {
        let current = node;
        node = node.parent();
        if current.kind() != SyntaxKind::InterfaceDeclaration
            && current.kind() != SyntaxKind::TypeAliasDeclaration
        {
            continue;
        }

        // Must have no type parameters
        if !current.type_parameters().is_empty() {
            continue;
        }
        // Name must overlap the selection
        let name = current.name();
        let name_pos = astnav::get_start_of_node(name, ctx.source_file, false);
        let name_end = name.end();
        if ctx.span.pos() < name_pos || ctx.span.pos() >= name_end {
            continue;
        }
        return current;
    }

    Node::NIL
}

// Go: refactors/type_to_effect_schema.go:64 runTypeToEffectSchema
fn run_type_to_effect_schema(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let matched_node = find_interface_or_type_alias(ctx);
    if matched_node.is_nil() {
        return Vec::new();
    }

    let version = ctx.tp.supported_effect_version();

    let sf = ctx.source_file;
    let action = ctx.new_refactor_action("Generate Effect.Schema from type", |tracker| {
        let new_node =
            SchemaGen::new(tracker.node_factory(), sf, version).process(matched_node, false);
        if new_node.is_some() {
            tracker.insert_node_before(sf, matched_node, new_node, true, LeadingTriviaOption::NONE);
        }
    });
    with_kind(action, "refactor.rewrite.effect.typeToEffectSchema")
}
