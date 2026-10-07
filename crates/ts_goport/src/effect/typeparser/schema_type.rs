// Go: internal/typeparser/schema_type.go

use crate::effect::typeparser::*;
use crate::prelude::*;
use std::sync::LazyLock;

static EFFECT_SCHEMA_MODULE_DESCRIPTOR: LazyLock<PackageSourceFileDescriptor> =
    LazyLock::new(|| {
        new_package_source_file_descriptor("effect", Some(is_schema_type_source_file))
    });

static EFFECT_PARSE_RESULT_MODULE_DESCRIPTOR: LazyLock<PackageSourceFileDescriptor> =
    LazyLock::new(|| {
        new_package_source_file_descriptor("effect", Some(is_parse_result_source_file))
    });

static EFFECT_SCHEMA_PARSER_MODULE_DESCRIPTOR: LazyLock<PackageSourceFileDescriptor> =
    LazyLock::new(|| {
        new_package_source_file_descriptor("effect", Some(is_schema_parser_source_file))
    });

/// SchemaTypeId is the property key for Schema's variance struct.
pub const SCHEMA_TYPE_ID: &str = "~effect/Schema/Schema";

/// SchemaTypes holds the A (Type) and E (Encoded) types extracted from a Schema type.
#[derive(Clone, Debug)]
pub struct SchemaTypes {
    pub a: TypeId,
    pub e: TypeId,
}

impl TypeParser<'_> {
    // Go: typeparser/schema_type.go IsSchemaType
    /// IsSchemaType returns true if the type is a Schema type (v4 or v3).
    pub fn is_schema_type(&mut self, t: TypeId) -> bool {
        self.effect_schema_types(t).is_some()
    }

    // Go: typeparser/schema_type.go EffectSchemaTypes
    /// EffectSchemaTypes extracts the A (Type) and E (Encoded) types from a Schema type.
    /// Returns nil if the type is not a recognized Schema type or types cannot be extracted.
    pub fn effect_schema_types(&mut self, t: TypeId) -> Option<Rc<SchemaTypes>> {
        if t.is_nil() {
            return None;
        }
        cached!(self, effect_schema_types, t, 'compute: {
            let version = self.detect_effect_version();
            if version == EffectMajorVersion::V4 {
                if self
                    .get_type_of_property_by_name(t, SCHEMA_TYPE_ID)
                    .is_nil()
                {
                    break 'compute None;
                }
                // V4: get Type and Encoded properties directly
                let a_type = self.get_type_of_property_by_name(t, "Type");
                let e_type = self.get_type_of_property_by_name(t, "Encoded");
                if a_type.is_nil() || e_type.is_nil() {
                    break 'compute None;
                }
                break 'compute Some(Rc::new(SchemaTypes {
                    a: a_type,
                    e: e_type,
                }));
            }

            // V3: check for 'ast' property first
            if self
                .checker
                .get_property_of_type_exported(t, "ast")
                .is_nil()
            {
                break 'compute None;
            }

            // Find the variance struct property and extract A/I types
            let props = self.checker.get_properties_of_type_exported(t);
            for prop in props {
                if prop.is_nil() {
                    continue;
                }
                let (flags, value_declaration) = {
                    let s = self.checker.sym(prop);
                    (s.flags, s.value_declaration)
                };
                if !flags.intersects(SymbolFlags::PROPERTY)
                    || flags.intersects(SymbolFlags::OPTIONAL)
                    || value_declaration.is_nil()
                {
                    continue;
                }
                let prop_type = self.checker.get_type_of_symbol_at_location(prop, Node::NIL);
                let a = self.extract_invariant_type(prop_type, "_A");
                if a.is_nil() {
                    continue;
                }
                let i = self.extract_invariant_type(prop_type, "_I");
                if i.is_nil() {
                    continue;
                }
                let r = self.extract_covariant_type(prop_type, "_R");
                if r.is_nil() {
                    continue;
                }
                break 'compute Some(Rc::new(SchemaTypes { a, e: i }));
            }

            None
        })
    }
}

// Go: typeparser/schema_type.go isSchemaTypeSourceFile
fn is_schema_type_source_file(tp: &mut TypeParser<'_>, sf: Node) -> bool {
    if sf.is_nil() {
        return false;
    }

    let module_sym = tp.checker.get_symbol_of_declaration(sf);
    if module_sym.is_nil() {
        return false;
    }

    let schema_sym = tp
        .checker
        .try_get_member_in_module_exports_and_properties("Schema", module_sym);
    if schema_sym.is_nil() {
        return false;
    }

    let schema_type = tp.checker.get_declared_type_of_symbol_exported(schema_sym);
    if schema_type.is_nil() {
        return false;
    }

    tp.is_schema_type(schema_type)
}

impl TypeParser<'_> {
    // Go: typeparser/schema_type.go IsNodeReferenceToEffectSchemaModuleApi
    /// IsNodeReferenceToEffectSchemaModuleApi reports whether node resolves to a member
    /// exported by the "effect" package from a module that exports the Schema type.
    pub fn is_node_reference_to_effect_schema_module_api(
        &mut self,
        node: Node,
        member_name: &str,
    ) -> bool {
        self.is_node_reference_to_module_export(node, &EFFECT_SCHEMA_MODULE_DESCRIPTOR, member_name)
    }
}

// Go: typeparser/schema_type.go isParseResultSourceFile
fn is_parse_result_source_file(tp: &mut TypeParser<'_>, sf: Node) -> bool {
    if sf.is_nil() {
        return false;
    }

    let module_sym = tp.checker.get_symbol_of_declaration(sf);
    if module_sym.is_nil() {
        return false;
    }

    // Check for ParseIssue type
    if tp
        .checker
        .try_get_member_in_module_exports_and_properties("ParseIssue", module_sym)
        .is_nil()
    {
        return false;
    }

    // Check for decodeSync export
    if tp
        .checker
        .try_get_member_in_module_exports_and_properties("decodeSync", module_sym)
        .is_nil()
    {
        return false;
    }

    // Check for encodeSync export
    if tp
        .checker
        .try_get_member_in_module_exports_and_properties("encodeSync", module_sym)
        .is_nil()
    {
        return false;
    }

    true
}

impl TypeParser<'_> {
    // Go: typeparser/schema_type.go IsNodeReferenceToEffectParseResultModuleApi
    /// IsNodeReferenceToEffectParseResultModuleApi reports whether node resolves to a member
    /// exported by the "effect" package from a module that exports the ParseResult type (V3).
    pub fn is_node_reference_to_effect_parse_result_module_api(
        &mut self,
        node: Node,
        member_name: &str,
    ) -> bool {
        self.is_node_reference_to_module_export(
            node,
            &EFFECT_PARSE_RESULT_MODULE_DESCRIPTOR,
            member_name,
        )
    }
}

// Go: typeparser/schema_type.go isSchemaParserSourceFile
fn is_schema_parser_source_file(tp: &mut TypeParser<'_>, sf: Node) -> bool {
    if sf.is_nil() {
        return false;
    }

    let module_sym = tp.checker.get_symbol_of_declaration(sf);
    if module_sym.is_nil() {
        return false;
    }

    // Check for decodeEffect export
    if tp
        .checker
        .try_get_member_in_module_exports_and_properties("decodeEffect", module_sym)
        .is_nil()
    {
        return false;
    }

    // Check for encodeEffect export
    if tp
        .checker
        .try_get_member_in_module_exports_and_properties("encodeEffect", module_sym)
        .is_nil()
    {
        return false;
    }

    true
}

impl TypeParser<'_> {
    // Go: typeparser/schema_type.go IsNodeReferenceToEffectSchemaParserModuleApi
    /// IsNodeReferenceToEffectSchemaParserModuleApi reports whether node resolves to a member
    /// exported by the "effect" package from a module that exports the SchemaParser type (V4).
    pub fn is_node_reference_to_effect_schema_parser_module_api(
        &mut self,
        node: Node,
        member_name: &str,
    ) -> bool {
        self.is_node_reference_to_module_export(
            node,
            &EFFECT_SCHEMA_PARSER_MODULE_DESCRIPTOR,
            member_name,
        )
    }
}
