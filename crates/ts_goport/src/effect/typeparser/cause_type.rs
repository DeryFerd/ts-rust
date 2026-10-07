// Go: internal/typeparser/cause_type.go

use crate::effect::typeparser::*;
use crate::prelude::*;
use std::sync::LazyLock;

pub static EFFECT_CAUSE_PACKAGE_SOURCE_FILE_DESCRIPTOR: LazyLock<PackageSourceFileDescriptor> =
    LazyLock::new(|| {
        new_package_source_file_descriptor("effect", Some(effect_cause_package_source_file_matches))
    });

/// The Go func literal passed to `newPackageSourceFileDescriptor` for
/// `effectCausePackageSourceFileDescriptor`.
fn effect_cause_package_source_file_matches(tp: &mut TypeParser<'_>, sf: Node) -> bool {
    if sf.is_nil() {
        return false;
    }
    let c = &mut *tp.checker;

    let module_sym = c.get_symbol_of_declaration(sf);
    if module_sym.is_nil() {
        return false;
    }

    c.try_get_member_in_module_exports_and_properties("Cause", module_sym)
        .is_some()
        && c.try_get_member_in_module_exports_and_properties("isCause", module_sym)
            .is_some()
        && c.try_get_member_in_module_exports_and_properties("NoSuchElementError", module_sym)
            .is_some()
}

impl TypeParser<'_> {
    /// IsNodeReferenceToEffectCauseModuleApi reports whether node resolves to a
    /// member exported by Effect's Cause module.
    pub fn is_node_reference_to_effect_cause_module_api(
        &mut self,
        node: Node,
        member_name: &str,
    ) -> bool {
        self.is_node_reference_to_module_export(
            node,
            &EFFECT_CAUSE_PACKAGE_SOURCE_FILE_DESCRIPTOR,
            member_name,
        )
    }
}
