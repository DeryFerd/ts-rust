// Go: internal/typeparser/context_type.go

use crate::effect::typeparser::*;
use crate::prelude::*;
use std::sync::LazyLock;

static EFFECT_CONTEXT_PACKAGE_SOURCE_FILE_DESCRIPTOR: LazyLock<PackageSourceFileDescriptor> =
    LazyLock::new(|| {
        new_package_source_file_descriptor(
            "effect",
            Some(effect_context_package_source_file_matches),
        )
    });

/// The Go func literal passed to `newPackageSourceFileDescriptor` for
/// `effectContextPackageSourceFileDescriptor`.
fn effect_context_package_source_file_matches(tp: &mut TypeParser<'_>, sf: Node) -> bool {
    if sf.is_nil() {
        return false;
    }

    let module_sym = tp.checker.get_symbol_of_declaration(sf);
    if module_sym.is_nil() {
        return false;
    }

    // The Context module exports "Context" (the namespace/type)
    let context_sym = tp
        .checker
        .try_get_member_in_module_exports_and_properties("Context", module_sym);
    if context_sym.is_nil() {
        return false;
    }

    // Effect v3 exports Context.Tag, while newer v4 betas export Context.Service.
    if tp.supported_effect_version() == EffectMajorVersion::V4 {
        let service_sym = tp
            .checker
            .try_get_member_in_module_exports_and_properties("Service", module_sym);
        return service_sym.is_some();
    }
    let tag_sym = tp
        .checker
        .try_get_member_in_module_exports_and_properties("Tag", module_sym);
    tag_sym.is_some()
}

impl TypeParser<'_> {
    // Go: typeparser/context_type.go IsNodeReferenceToEffectContextModuleApi
    pub fn is_node_reference_to_effect_context_module_api(
        &mut self,
        node: Node,
        member_name: &str,
    ) -> bool {
        self.is_node_reference_to_module_export(
            node,
            &EFFECT_CONTEXT_PACKAGE_SOURCE_FILE_DESCRIPTOR,
            member_name,
        )
    }
}
