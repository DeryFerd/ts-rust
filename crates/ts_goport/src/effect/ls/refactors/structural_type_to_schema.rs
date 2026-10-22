//! Port of Effect-TS/tsgo `internal/refactors/structural_type_to_schema.go`.

use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::type_to_effect_schema::find_interface_or_type_alias;
use crate::effect::ls::refactors::with_kind;
use crate::effect::ls::schemagen::StructuralSchemaGen;
use crate::ls::CodeAction;
use crate::ls::change::LeadingTriviaOption;
use crate::prelude::*;

// Go: refactors/structural_type_to_schema.go:12 StructuralTypeToSchema
pub static STRUCTURAL_TYPE_TO_SCHEMA: Refactor = Refactor {
    name: "structuralTypeToSchema",
    description: "Refactor to Schema (Structural)",
    kind: "rewrite.effect.structuralTypeToSchema",
    run: run_structural_type_to_schema,
};

// Go: refactors/structural_type_to_schema.go:19 runStructuralTypeToSchema
fn run_structural_type_to_schema(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let matched_node = find_interface_or_type_alias(ctx);
    if matched_node.is_nil() {
        return Vec::new();
    }

    let version = ctx.tp.supported_effect_version();

    // Get the name node and resolve the type
    // PORT: Go reads the name through `AsInterfaceDeclaration` or
    // `AsTypeAliasDeclaration`; `name()` is the same for both kinds.
    let name_node = matched_node.name();
    if name_node.is_nil() {
        return Vec::new();
    }

    let t = ctx.tp.get_type_at_location(name_node);
    if t.is_nil() {
        return Vec::new();
    }

    let type_name = name_node.text().to_string();
    let is_exported = get_combined_modifier_flags(matched_node).intersects(ModifierFlags::EXPORT);

    // PORT: Go makes the generator and runs `Process` in the action's
    // closure, with the tracker as its node factory. The port's closure
    // gets only the tracker and cannot reach `ctx.tp` (`new_refactor_action`
    // borrows `ctx`), so `Process` runs here, just before the action, with
    // the factory of a new emit context (the tracker's factory is one too:
    // the same hooks, the same synthetic arena). Nothing comes between the
    // two in Go, so the checker calls and the statements are the same; the
    // closure inserts the statements as Go does.
    // The other context cannot change the output. The generator calls only
    // the factory's `New*` constructors (structural.go uses no other tracker
    // method, schemagen.rs no other factory or context call), and their one
    // hook is onCreate, which sets `NodeFlagsSynthesized` and writes no side
    // table (printer/emitcontext.go:50). So no context holds emit flags,
    // original links or generated names for these nodes, in Go or here, and
    // the tracker prints them with its own context as Go does.
    let emit_context = new_emit_context();
    let stmts = StructuralSchemaGen::new(
        &emit_context.factory().ast,
        ctx.tp,
        ctx.source_file,
        version,
    )
    .process(&[(type_name, t)], matched_node, is_exported);

    let sf = ctx.source_file;
    let action = ctx.new_refactor_action("Refactor to Schema (Recursive Structural)", |tracker| {
        for &stmt in stmts.iter().rev() {
            tracker.insert_node_before(sf, matched_node, stmt, true, LeadingTriviaOption::NONE);
        }
    });
    with_kind(action, "refactor.rewrite.effect.structuralTypeToSchema")
}
