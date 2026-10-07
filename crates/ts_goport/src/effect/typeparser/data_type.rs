// Go: internal/typeparser/data_type.go

use crate::effect::typeparser::*;
use crate::prelude::*;
use std::sync::LazyLock;

static EFFECT_DATA_PACKAGE_SOURCE_FILE_DESCRIPTOR: LazyLock<PackageSourceFileDescriptor> =
    LazyLock::new(|| {
        new_package_source_file_descriptor("effect", Some(effect_data_package_source_file_matches))
    });

/// The Go func literal passed to `newPackageSourceFileDescriptor` for
/// `effectDataPackageSourceFileDescriptor`.
fn effect_data_package_source_file_matches(tp: &mut TypeParser<'_>, sf: Node) -> bool {
    if sf.is_nil() {
        return false;
    }

    let module_sym = tp.checker.get_symbol_of_declaration(sf);
    if module_sym.is_nil() {
        return false;
    }

    // The Data module exports "TaggedError"
    let tagged_error_sym = tp
        .checker
        .try_get_member_in_module_exports_and_properties("TaggedError", module_sym);
    if tagged_error_sym.is_nil() {
        return false;
    }

    // The Data module also exports "TaggedEnum" (v4) or "taggedEnum" (v3)
    let mut tagged_enum_sym = tp
        .checker
        .try_get_member_in_module_exports_and_properties("TaggedEnum", module_sym);
    if tagged_enum_sym.is_nil() {
        tagged_enum_sym = tp
            .checker
            .try_get_member_in_module_exports_and_properties("taggedEnum", module_sym);
    }
    if tagged_enum_sym.is_nil() {
        return false;
    }

    true
}

impl TypeParser<'_> {
    // Go: typeparser/data_type.go IsNodeReferenceToEffectDataModuleApi
    pub fn is_node_reference_to_effect_data_module_api(
        &mut self,
        node: Node,
        member_name: &str,
    ) -> bool {
        self.is_node_reference_to_module_export(
            node,
            &EFFECT_DATA_PACKAGE_SOURCE_FILE_DESCRIPTOR,
            member_name,
        )
    }
}
