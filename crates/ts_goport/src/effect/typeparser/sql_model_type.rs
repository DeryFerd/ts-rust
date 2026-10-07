// Go: internal/typeparser/sql_model_type.go

use crate::effect::typeparser::*;
use crate::prelude::*;
use std::sync::LazyLock;

static SQL_MODEL_MODULE_DESCRIPTOR: LazyLock<PackageSourceFileDescriptor> = LazyLock::new(|| {
    new_package_source_file_descriptor("@effect/sql", Some(is_sql_model_type_source_file))
});

// Go: typeparser/sql_model_type.go isSqlModelTypeSourceFile
/// isSqlModelTypeSourceFile checks if a source file is @effect/sql Model module
/// by verifying it exports "Class", "makeRepository", and "makeDataLoaders".
fn is_sql_model_type_source_file(tp: &mut TypeParser<'_>, sf: Node) -> bool {
    if sf.is_nil() {
        return false;
    }

    let module_sym = tp.checker.get_symbol_of_declaration(sf);
    if module_sym.is_nil() {
        return false;
    }

    if tp
        .checker
        .try_get_member_in_module_exports_and_properties("Class", module_sym)
        .is_nil()
    {
        return false;
    }
    if tp
        .checker
        .try_get_member_in_module_exports_and_properties("makeRepository", module_sym)
        .is_nil()
    {
        return false;
    }
    if tp
        .checker
        .try_get_member_in_module_exports_and_properties("makeDataLoaders", module_sym)
        .is_nil()
    {
        return false;
    }

    true
}

impl TypeParser<'_> {
    // Go: typeparser/sql_model_type.go IsNodeReferenceToEffectSqlModelModuleApi
    /// IsNodeReferenceToEffectSqlModelModuleApi reports whether node resolves to a member
    /// exported by the "@effect/sql" package from a module that exports the Model API.
    pub fn is_node_reference_to_effect_sql_model_module_api(
        &mut self,
        node: Node,
        member_name: &str,
    ) -> bool {
        self.is_node_reference_to_module_export(node, &SQL_MODEL_MODULE_DESCRIPTOR, member_name)
    }
}
