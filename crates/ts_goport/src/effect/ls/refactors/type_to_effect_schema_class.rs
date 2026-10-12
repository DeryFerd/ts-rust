//! Port of Effect-TS/tsgo `internal/refactors/type_to_effect_schema_class.go`.

use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::type_to_effect_schema::find_interface_or_type_alias;
use crate::effect::ls::refactors::with_kind;
use crate::effect::ls::schemagen::{self, SchemaGen};
use crate::ls::CodeAction;
use crate::ls::change::LeadingTriviaOption;

// Go: refactors/type_to_effect_schema_class.go:10 TypeToEffectSchemaClass
pub static TYPE_TO_EFFECT_SCHEMA_CLASS: Refactor = Refactor {
    name: "typeToEffectSchemaClass",
    description: "Generate Schema.Class from type",
    kind: "rewrite.effect.typeToEffectSchemaClass",
    run: run_type_to_effect_schema_class,
};

// Go: refactors/type_to_effect_schema_class.go:17 runTypeToEffectSchemaClass
fn run_type_to_effect_schema_class(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let matched_node = find_interface_or_type_alias(ctx);
    if matched_node.is_nil() {
        return Vec::new();
    }

    // Schema.Class is not applicable when the type has index signatures
    if schemagen::has_index_signatures(matched_node) {
        return Vec::new();
    }

    let version = ctx.tp.supported_effect_version();

    let sf = ctx.source_file;
    let action = ctx.new_refactor_action("Generate Schema.Class from type", |tracker| {
        let new_node =
            SchemaGen::new(tracker.node_factory(), sf, version).process(matched_node, true);
        if new_node.is_some() {
            tracker.insert_node_before(sf, matched_node, new_node, true, LeadingTriviaOption::NONE);
        }
    });
    with_kind(action, "refactor.rewrite.effect.typeToEffectSchemaClass")
}
