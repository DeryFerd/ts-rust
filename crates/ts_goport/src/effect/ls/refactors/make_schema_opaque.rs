//! Port of Effect-TS/tsgo `internal/refactors/make_schema_opaque.go`.

use crate::astnav;
use crate::effect::ls::refactor::{Refactor, RefactorContext};
use crate::effect::ls::refactors::with_kind;
use crate::effect::typeparser::{EffectMajorVersion, SchemaTypes, find_module_identifier};
use crate::ls::CodeAction;
use crate::prelude::*;

// Go: refactors/make_schema_opaque.go:13 MakeSchemaOpaque
pub static MAKE_SCHEMA_OPAQUE: Refactor = Refactor {
    name: "makeSchemaOpaque",
    description: "Make Schema opaque",
    kind: "rewrite.effect.makeSchemaOpaque",
    run: run_make_schema_opaque,
};

// Go: refactors/make_schema_opaque.go:21 schemaVarInfo
/// schemaVarInfo holds the result of finding a schema variable declaration.
// PORT: Go also keeps the VariableDeclarationList and the initializer; no
// refactor reads them.
pub(crate) struct SchemaVarInfo {
    /// the variable name identifier
    pub identifier: Node,
    /// the enclosing VariableStatement
    pub var_statement: Node,
    pub schema_types: Rc<SchemaTypes>,
}

// Go: refactors/make_schema_opaque.go:31 findSchemaVariableDeclaration
/// findSchemaVariableDeclaration walks the ancestor chain from the cursor to find a
/// VariableDeclaration whose initializer has a Schema type. Returns None if not found.
// PORT: Go's unused checker parameter is not ported.
pub(crate) fn find_schema_variable_declaration(
    ctx: &mut RefactorContext<'_, '_>,
) -> Option<SchemaVarInfo> {
    let token = astnav::get_token_at_position(ctx.source_file, ctx.span.pos());
    if token.is_nil() {
        return None;
    }

    let mut node = token;
    while node.is_some() && node.kind() != SyntaxKind::SourceFile {
        let current = node;
        node = node.parent();
        if current.kind() != SyntaxKind::VariableDeclaration {
            continue;
        }

        // Must have an identifier name
        let name_node = current.name();
        if name_node.is_nil() || name_node.kind() != SyntaxKind::Identifier {
            continue;
        }

        // Name must be within the selection span
        let name_pos = astnav::get_start_of_node(name_node, ctx.source_file, false);
        let name_end = name_node.end();
        if ctx.span.pos() < name_pos || ctx.span.pos() >= name_end {
            continue;
        }

        // Must have an initializer
        let initializer = current.initializer();
        if initializer.is_nil() {
            continue;
        }

        // Parent chain: VariableDeclaration → VariableDeclarationList → VariableStatement
        let var_decl_list = current.parent();
        if var_decl_list.is_nil() || var_decl_list.kind() != SyntaxKind::VariableDeclarationList {
            continue;
        }
        let var_statement = var_decl_list.parent();
        if var_statement.is_nil() || var_statement.kind() != SyntaxKind::VariableStatement {
            continue;
        }

        // Check the initializer's type is a Schema type
        let init_type = ctx.tp.get_type_at_location(initializer);
        if init_type.is_nil() {
            continue;
        }

        let Some(schema_types) = ctx.tp.effect_schema_types(init_type) else {
            continue;
        };

        return Some(SchemaVarInfo {
            identifier: name_node,
            var_statement,
            schema_types,
        });
    }

    None
}

// Go: refactors/make_schema_opaque.go:96 createTypeofReference
/// createTypeofReference creates: typeof <name>
// PORT: the Go helpers of this file take the rewriter tracker and call only
// its node factory; the port takes the factory.
fn create_typeof_reference(f: &NodeFactory, name: &str) -> Node {
    f.new_type_query_node(f.new_identifier(name), NodeList::NIL)
}

// Go: refactors/make_schema_opaque.go:105 createSchemaPropertyAccess
/// createSchemaPropertyAccess creates: <schemaId>.<ns>.<member> as a property access expression.
/// Used in ExpressionWithTypeArguments for heritage clauses.
fn create_schema_property_access(f: &NodeFactory, schema_id: &str, ns: &str, member: &str) -> Node {
    f.new_property_access_expression(
        f.new_property_access_expression(
            f.new_identifier(schema_id),
            Node::NIL,
            f.new_identifier(ns),
            NodeFlags::NONE,
        ),
        Node::NIL,
        f.new_identifier(member),
        NodeFlags::NONE,
    )
}

// Go: refactors/make_schema_opaque.go:121 createSchemaQualifiedName
/// createSchemaQualifiedName creates: <schemaId>.<ns>.<member> as a qualified name.
/// Used in TypeReferenceNode for type alias declarations.
fn create_schema_qualified_name(f: &NodeFactory, schema_id: &str, ns: &str, member: &str) -> Node {
    f.new_qualified_name(
        f.new_qualified_name(f.new_identifier(schema_id), f.new_identifier(ns)),
        f.new_identifier(member),
    )
}

// Go: refactors/make_schema_opaque.go:133 createHeritageTypeRef
/// createHeritageTypeRef creates: <schemaId>.<ns>.<member><typeof <inferFrom>>
/// as an ExpressionWithTypeArguments node for use in interface heritage clauses.
fn create_heritage_type_ref(
    f: &NodeFactory,
    schema_id: &str,
    ns: &str,
    member: &str,
    infer_from: &str,
) -> Node {
    f.new_expression_with_type_arguments(
        create_schema_property_access(f, schema_id, ns, member),
        f.new_node_list(&[create_typeof_reference(f, infer_from)]),
    )
}

// Go: refactors/make_schema_opaque.go:144 createTypeAliasTypeRef
/// createTypeAliasTypeRef creates: <schemaId>.<ns>.<member><typeof <inferFrom>>
/// as a TypeReferenceNode for use in type alias declarations.
fn create_type_alias_type_ref(
    f: &NodeFactory,
    schema_id: &str,
    ns: &str,
    member: &str,
    infer_from: &str,
) -> Node {
    f.new_type_reference_node(
        create_schema_qualified_name(f, schema_id, ns, member),
        f.new_node_list(&[create_typeof_reference(f, infer_from)]),
    )
}

// Go: refactors/make_schema_opaque.go:153 opaqueExportModifiers
pub(crate) fn opaque_export_modifiers(f: &NodeFactory) -> ModifierList {
    f.new_modifier_list(&[f.new_modifier(SyntaxKind::ExportKeyword)])
}

// Go: refactors/make_schema_opaque.go:160 createOpaqueInterface
/// createOpaqueInterface creates: export interface <name> extends <heritage> { }
pub(crate) fn create_opaque_interface(
    f: &NodeFactory,
    name: &str,
    schema_id: &str,
    ns: &str,
    member: &str,
    infer_from: &str,
) -> Node {
    let heritage = create_heritage_type_ref(f, schema_id, ns, member, infer_from);
    let node = f.new_interface_declaration(
        opaque_export_modifiers(f),
        f.new_identifier(name),
        NodeList::NIL, // typeParameters
        f.new_node_list(&[
            f.new_heritage_clause(SyntaxKind::ExtendsKeyword, f.new_node_list(&[heritage]))
        ]),
        f.new_node_list(&[]), // empty members
    );
    set_parent_in_children(node);
    node
}

// Go: refactors/make_schema_opaque.go:179 createOpaqueTypeAlias
/// createOpaqueTypeAlias creates: export type <name> = <schemaId>.<ns>.<member><typeof inferFrom>
pub(crate) fn create_opaque_type_alias(
    f: &NodeFactory,
    name: &str,
    schema_id: &str,
    ns: &str,
    member: &str,
    infer_from: &str,
) -> Node {
    let type_ref = create_type_alias_type_ref(f, schema_id, ns, member, infer_from);
    let node = f.new_type_alias_declaration(
        opaque_export_modifiers(f),
        f.new_identifier(name),
        NodeList::NIL, // typeParameters
        type_ref,
    );
    set_parent_in_children(node);
    node
}

// Go: refactors/make_schema_opaque.go:192 createOpaqueTypeDecl
/// createOpaqueTypeDecl creates an interface (if isObject) or type alias for the given schema property.
fn create_opaque_type_decl(
    f: &NodeFactory,
    name: &str,
    schema_id: &str,
    ns: &str,
    member: &str,
    infer_from: &str,
    is_object: bool,
) -> Node {
    if is_object {
        return create_opaque_interface(f, name, schema_id, ns, member, infer_from);
    }
    create_opaque_type_alias(f, name, schema_id, ns, member, infer_from)
}

// Go: refactors/make_schema_opaque.go:199 runMakeSchemaOpaque
fn run_make_schema_opaque(ctx: &mut RefactorContext<'_, '_>) -> Vec<CodeAction> {
    let Some(info) = find_schema_variable_declaration(ctx) else {
        return Vec::new();
    };

    let version = ctx.tp.supported_effect_version();
    let is_v4 = version == EffectMajorVersion::V4;

    let sf = ctx.source_file;
    let checker: &Checker = ctx.tp.checker;
    let action = ctx.new_refactor_action("Make Schema opaque", |tracker| {
        let schema_id = find_module_identifier(sf, "Schema");
        let orig_name = info.identifier.text().to_string();
        let new_name = orig_name.clone() + "_";

        let is_a_object = checker
            .ty(info.schema_types.a)
            .flags()
            .intersects(TypeFlags::OBJECT);
        let is_e_object = checker
            .ty(info.schema_types.e)
            .flags()
            .intersects(TypeFlags::OBJECT);

        // 1. Rename the original variable identifier (append "_")
        let new_identifier = tracker.node_factory().new_identifier(new_name.as_str());
        tracker.replace_node(sf, info.identifier, new_identifier, None);

        let f = tracker.node_factory();

        // Build all nodes to insert after the variable statement
        let mut insert_nodes = Vec::new();

        // 2. Opaque Type: export interface/type <Name> extends Schema.Schema.Type<typeof Name_>
        let opaque_type = create_opaque_type_decl(
            f,
            &orig_name,
            &schema_id,
            "Schema",
            "Type",
            &new_name,
            is_a_object,
        );
        insert_nodes.push(opaque_type);

        // 3. Encoded: export interface/type <Name>Encoded extends Schema.{Codec|Schema}.Encoded<typeof Name_>
        let encoded_ns = if is_v4 { "Codec" } else { "Schema" };
        let encoded_name = orig_name.clone() + "Encoded";
        let encoded_type = create_opaque_type_decl(
            f,
            &encoded_name,
            &schema_id,
            encoded_ns,
            "Encoded",
            &new_name,
            is_e_object,
        );
        insert_nodes.push(encoded_type);

        // 4. Context / DecodingServices
        let (context_ns, context_member, context_name) = if is_v4 {
            (
                "Codec",
                "DecodingServices",
                orig_name.clone() + "DecodingServices",
            )
        } else {
            ("Schema", "Context", orig_name.clone() + "Context")
        };
        let context_type = create_opaque_type_alias(
            f,
            &context_name,
            &schema_id,
            context_ns,
            context_member,
            &new_name,
        );
        insert_nodes.push(context_type);

        // 5. V4 only: EncodingServices
        let mut encoding_services_name = String::new();
        if is_v4 {
            encoding_services_name = orig_name.clone() + "EncodingServices";
            let es_type = create_opaque_type_alias(
                f,
                &encoding_services_name,
                &schema_id,
                "Codec",
                "EncodingServices",
                &new_name,
            );
            insert_nodes.push(es_type);
        }

        // 6. Re-export const: export const <Name>: Schema.{Codec|Schema}<...> = Name_
        let schema_type_ns = if is_v4 { "Codec" } else { "Schema" };
        let mut type_args = vec![
            f.new_type_reference_node(f.new_identifier(orig_name.as_str()), NodeList::NIL),
            f.new_type_reference_node(f.new_identifier(encoded_name.as_str()), NodeList::NIL),
            f.new_type_reference_node(f.new_identifier(context_name.as_str()), NodeList::NIL),
        ];
        if is_v4 {
            type_args.push(f.new_type_reference_node(
                f.new_identifier(encoding_services_name.as_str()),
                NodeList::NIL,
            ));
        }

        let const_type = f.new_type_reference_node(
            f.new_qualified_name(
                f.new_identifier(schema_id.as_str()),
                f.new_identifier(schema_type_ns),
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
        // PORT: the rewriter does not override InsertNodesAfter: this is the
        // base change tracker's (formatted nodes).
        tracker.insert_nodes_after(sf, info.var_statement, &insert_nodes);
    });
    with_kind(action, "refactor.rewrite.effect.makeSchemaOpaque")
}
