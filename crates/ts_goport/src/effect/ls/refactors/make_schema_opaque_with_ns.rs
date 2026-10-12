//! Port of Effect-TS/tsgo `internal/refactors/make_schema_opaque_with_ns.go`.

use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::make_schema_opaque::{
    create_opaque_interface, create_opaque_type_alias, find_schema_variable_declaration,
    opaque_export_modifiers,
};
use crate::effect::ls::refactors::with_kind;
use crate::effect::typeparser::{EffectMajorVersion, find_module_identifier};
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: refactors/make_schema_opaque_with_ns.go:12 MakeSchemaOpaqueWithNs
pub static MAKE_SCHEMA_OPAQUE_WITH_NS: Refactor = Refactor {
    name: "makeSchemaOpaqueWithNs",
    description: "Make Schema opaque with namespace",
    kind: "rewrite.effect.makeSchemaOpaqueWithNs",
    run: run_make_schema_opaque_with_ns,
};

// Go: refactors/make_schema_opaque_with_ns.go:19 runMakeSchemaOpaqueWithNs
fn run_make_schema_opaque_with_ns(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let Some(info) = find_schema_variable_declaration(ctx) else {
        return Vec::new();
    };

    let version = ctx.tp.supported_effect_version();
    let is_v4 = version == EffectMajorVersion::V4;

    let sf = ctx.source_file;
    let checker: &Checker = ctx.tp.checker;
    let action = ctx.new_refactor_action("Make Schema opaque with namespace", |tracker| {
        let schema_id = find_module_identifier(sf, "Schema");
        let orig_name = info.identifier.text().to_string();
        let new_name = orig_name.clone() + "_";

        let is_e_object = checker
            .ty(info.schema_types.e)
            .flags()
            .intersects(TypeFlags::OBJECT);

        // 1. Rename the original variable identifier (append "_")
        let new_identifier = tracker.node_factory().new_identifier(new_name.as_str());
        tracker.replace_node(sf, info.identifier, new_identifier, None);

        let f = tracker.node_factory();

        let mut insert_nodes = Vec::new();

        // 2. Opaque Type: export interface <Name> extends Schema.Schema.Type<typeof Name_>
        // Always uses Schema.Schema.Type, always an interface
        let opaque_type =
            create_opaque_interface(f, &orig_name, &schema_id, "Schema", "Type", &new_name);
        insert_nodes.push(opaque_type);

        // 3. Build namespace members
        let mut ns_members = Vec::new();

        // Encoded: export interface/type Encoded extends Schema.{Codec|Schema}.Encoded<typeof Name_>
        let encoded_ns = if is_v4 { "Codec" } else { "Schema" };
        let encoded_member = if is_e_object {
            create_opaque_interface(f, "Encoded", &schema_id, encoded_ns, "Encoded", &new_name)
        } else {
            create_opaque_type_alias(f, "Encoded", &schema_id, encoded_ns, "Encoded", &new_name)
        };
        ns_members.push(encoded_member);

        // Context/DecodingServices
        let context_member_name = if is_v4 {
            let context_member = create_opaque_type_alias(
                f,
                "DecodingServices",
                &schema_id,
                "Codec",
                "DecodingServices",
                &new_name,
            );
            ns_members.push(context_member);
            "DecodingServices"
        } else {
            let context_member =
                create_opaque_type_alias(f, "Context", &schema_id, "Schema", "Context", &new_name);
            ns_members.push(context_member);
            "Context"
        };

        // V4 only: EncodingServices
        if is_v4 {
            let es_member = create_opaque_type_alias(
                f,
                "EncodingServices",
                &schema_id,
                "Codec",
                "EncodingServices",
                &new_name,
            );
            ns_members.push(es_member);
        }

        // 4. Create namespace declaration
        // PORT: Go calls the rewriter's `NewModuleDeclaration`, a shim that
        // calls the factory with nil attributes; the port calls the factory.
        let ns_block = f.new_module_block(f.new_node_list(&ns_members));
        let ns_decl = f.new_module_declaration(
            opaque_export_modifiers(f),
            SyntaxKind::NamespaceKeyword,
            f.new_identifier(orig_name.as_str()),
            Node::NIL, // attributes
            ns_block,
        );
        set_parent_in_children(ns_decl);
        insert_nodes.push(ns_decl);

        // 5. Re-export const: export const <Name>: Schema.Schema<Name, Name.Encoded, Name.{Context|DecodingServices}> = Name_
        // Always uses Schema.Schema with 3 type args for the namespace variant
        let type_args = [
            f.new_type_reference_node(f.new_identifier(orig_name.as_str()), NodeList::NIL),
            f.new_type_reference_node(
                f.new_qualified_name(
                    f.new_identifier(orig_name.as_str()),
                    f.new_identifier("Encoded"),
                ),
                NodeList::NIL,
            ),
            f.new_type_reference_node(
                f.new_qualified_name(
                    f.new_identifier(orig_name.as_str()),
                    f.new_identifier(context_member_name),
                ),
                NodeList::NIL,
            ),
        ];

        let const_type = f.new_type_reference_node(
            f.new_qualified_name(
                f.new_identifier(schema_id.as_str()),
                f.new_identifier("Schema"),
            ),
            f.new_node_list(&type_args),
        );

        let const_decl = f.new_variable_declaration(
            f.new_identifier(orig_name.as_str()),
            Node::NIL,  // exclamationToken
            const_type, // type annotation
            f.new_identifier(new_name.as_str()),
        );
        let const_decl_list =
            f.new_variable_declaration_list(f.new_node_list(&[const_decl]), NodeFlags::CONST);
        let const_statement = f.new_variable_statement(opaque_export_modifiers(f), const_decl_list);
        set_parent_in_children(const_statement);
        insert_nodes.push(const_statement);

        // Insert all nodes after the variable statement
        // PORT: the base change tracker's InsertNodesAfter, as in
        // makeSchemaOpaque.
        tracker.insert_nodes_after(sf, info.var_statement, &insert_nodes);
    });
    with_kind(action, "refactor.rewrite.effect.makeSchemaOpaqueWithNs")
}
