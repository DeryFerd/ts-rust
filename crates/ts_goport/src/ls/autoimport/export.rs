use crate::ls::autoimport::prelude::*;

// Port of Go `ls/autoimport/export.go` and `ls/autoimport/export_stringer_generated.go`.

use crate::flags_macros::go_enum;
use crate::frontend::tspath;
use crate::ls::lsutil;

// Go: ls/autoimport/export.go:18 ModuleID
// ModuleID uniquely identifies a module across multiple declarations.
// If the export is from an ambient module declaration, this is the module name.
// If the export is from a module augmentation, this is the Path() of the resolved module file.
// Otherwise this is the Path() of the exporting source file.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ModuleID(pub String);

// Go: ls/autoimport/export.go:20 ExportID
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ExportID {
    pub module_id: ModuleID,
    pub export_name: String,
}

// Go: ls/autoimport/export.go:25 ExportSyntax
go_enum!(ExportSyntax, i32 {
    NONE = 0; // ExportSyntaxNone
    // export const x = {}
    MODIFIER = 1; // ExportSyntaxModifier
    // export { x }
    NAMED = 2; // ExportSyntaxNamed
    // export default function f() {}
    DEFAULT_MODIFIER = 3; // ExportSyntaxDefaultModifier
    // export default f
    DEFAULT_DECLARATION = 4; // ExportSyntaxDefaultDeclaration
    // export = x
    EQUALS = 5; // ExportSyntaxEquals
    // export as namespace x
    UMD = 6; // ExportSyntaxUMD
    // export * from "module"
    STAR = 7; // ExportSyntaxStar
    // module.exports = {}
    COMMON_JS_MODULE_EXPORTS = 8; // ExportSyntaxCommonJSModuleExports
    // exports.x = {}
    COMMON_JS_EXPORTS_PROPERTY = 9; // ExportSyntaxCommonJSExportsProperty
});

// Go: ls/autoimport/export.go:49 Export
// PORT: Go embeds `ExportID`; it is the nested `export_id` field, and `Deref`
// promotes its fields (`export.module_id`, `export.export_name`) as Go does.
// Go `*Export` values are shared (`Rc<Export>`) once they are complete.
#[derive(Clone, Debug, Default)]
pub struct Export {
    pub export_id: ExportID,
    pub module_file_name: String,
    pub syntax: ExportSyntax,
    pub flags: SymbolFlags,
    pub local_name: String,
    // through is the name of the module symbol's export that this export was found on,
    // either 'export=', InternalSymbolNameExportStar, or empty string.
    pub through: String,

    // Checker-set fields
    pub target: ExportID,
    pub is_type_only: bool,
    pub script_element_kind: lsutil::ScriptElementKind,
    pub script_element_kind_modifiers: lsutil::ScriptElementKindModifier,

    // The file where the export was found.
    pub path: tspath::Path,

    pub package_name: String,
}

impl std::ops::Deref for Export {
    type Target = ExportID;
    fn deref(&self) -> &ExportID {
        &self.export_id
    }
}

impl std::ops::DerefMut for Export {
    fn deref_mut(&mut self) -> &mut ExportID {
        &mut self.export_id
    }
}

impl Export {
    // Go: ls/autoimport/export.go:72 Name
    pub fn name(&self) -> String {
        if !self.local_name.is_empty() {
            return self.local_name.clone();
        }
        if self.export_id.export_name == INTERNAL_SYMBOL_NAME_EXPORT_EQUALS {
            return self.target.export_name.clone();
        }
        self.export_id.export_name.clone()
    }

    // Go: ls/autoimport/export.go:82 IsRenameable
    pub fn is_renameable(&self) -> bool {
        self.export_id.export_name == INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
            || self.export_id.export_name == INTERNAL_SYMBOL_NAME_DEFAULT
    }

    // Go: ls/autoimport/export.go:86 AmbientModuleName
    pub fn ambient_module_name(&self) -> String {
        if !tspath::is_external_module_name_relative(&self.export_id.module_id.0) {
            return self.export_id.module_id.0.clone();
        }
        String::new()
    }

    // Go: ls/autoimport/export.go:93 IsUnresolvedAlias
    pub fn is_unresolved_alias(&self) -> bool {
        self.flags == SymbolFlags::ALIAS
    }
}

// Go: ls/autoimport/export.go:97 SymbolToExport
// PORT: Go `*Export` result; nil is `None`.
pub fn symbol_to_export(symbol: SymbolId, ch: &mut Checker) -> Option<Rc<Export>> {
    let parent = ch.sym(symbol).parent;
    if parent.is_some() && ch.is_external_module_symbol(parent) {
        let (module_id, module_file_name, ok) =
            try_get_module_id_and_file_name_of_module_symbol(&ch.symbols, parent);
        if ok {
            let file = get_source_file_of_module(&ch.symbols, parent);
            return extract_first_export(symbol, ch, &module_id, &module_file_name, file);
        }
        return None;
    }

    // Go: core.FirstOrNil(symbol.Declarations)
    let declaration = ch
        .sym(symbol)
        .declarations
        .first()
        .copied()
        .unwrap_or(Node::NIL);
    if declaration.is_nil() {
        return None;
    }

    let file = get_source_file_of_node(declaration);
    if file.symbol().is_nil() {
        return None;
    }

    let module_symbol = ch.get_merged_symbol_exported(file.symbol());
    let module_id = ModuleID(source_file_info(file).path.clone());
    let module_file_name = source_file_file_name(file).to_string();
    let skipped = ch.skip_alias_exported(symbol);
    let target = ch.get_merged_symbol_exported(skipped);

    if let Some(export) = try_get_module_export(
        INTERNAL_SYMBOL_NAME_DEFAULT,
        target,
        module_symbol,
        ch,
        &module_id,
        &module_file_name,
        file,
    ) {
        return Some(export);
    }
    if let Some(export) = try_get_module_export(
        INTERNAL_SYMBOL_NAME_EXPORT_EQUALS,
        target,
        module_symbol,
        ch,
        &module_id,
        &module_file_name,
        file,
    ) {
        return Some(export);
    }
    let name = ch.sym(symbol).name.to_string();
    try_get_module_export(
        &name,
        target,
        module_symbol,
        ch,
        &module_id,
        &module_file_name,
        file,
    )
}

// Go: ls/autoimport/export.go:129 tryGetModuleExport
pub fn try_get_module_export(
    export_name: &str,
    target: SymbolId,
    module_symbol: SymbolId,
    ch: &mut Checker,
    module_id: &ModuleID,
    module_file_name: &str,
    file: Node,
) -> Option<Rc<Export>> {
    let exported = ch.try_get_member_in_module_exports_and_properties(export_name, module_symbol);
    if exported.is_some() {
        let skipped = ch.skip_alias_exported(exported);
        if ch.get_merged_symbol_exported(skipped) == target {
            return extract_first_export(exported, ch, module_id, module_file_name, file);
        }
    }
    None
}

// Go: ls/autoimport/export.go:137 extractFirstExport
pub fn extract_first_export(
    symbol: SymbolId,
    ch: &mut Checker,
    module_id: &ModuleID,
    module_file_name: &str,
    file: Node,
) -> Option<Rc<Export>> {
    let mut exports: Vec<Rc<Export>> = Vec::new();
    let name = ch.sym(symbol).name.to_string();
    let mut extractor = new_symbol_extractor("", ch, None, None);
    extractor.extract_from_symbol(
        &name,
        symbol,
        module_id,
        module_file_name,
        file,
        &mut exports,
    );
    // Go: core.FirstOrNil(exports)
    exports.first().cloned()
}

// ---------------------------------------------------------------------------
// export_stringer_generated.go
// ---------------------------------------------------------------------------

// Go: ls/autoimport/export_stringer_generated.go:23 _ExportSyntax_name
const EXPORT_SYNTAX_NAME: &str = "ExportSyntaxNoneExportSyntaxModifierExportSyntaxNamedExportSyntaxDefaultModifierExportSyntaxDefaultDeclarationExportSyntaxEqualsExportSyntaxUMDExportSyntaxStarExportSyntaxCommonJSModuleExportsExportSyntaxCommonJSExportsProperty";

// Go: ls/autoimport/export_stringer_generated.go:25 _ExportSyntax_index
const EXPORT_SYNTAX_INDEX: [u8; 11] = [0, 16, 36, 53, 80, 110, 128, 143, 159, 192, 227];

impl ExportSyntax {
    // Go: ls/autoimport/export_stringer_generated.go:27 String
    pub fn string(self) -> String {
        let idx = self.0 - 0;
        if self.0 < 0 || idx as usize >= EXPORT_SYNTAX_INDEX.len() - 1 {
            return format!("ExportSyntax({})", self.0);
        }
        let idx = idx as usize;
        EXPORT_SYNTAX_NAME[EXPORT_SYNTAX_INDEX[idx] as usize..EXPORT_SYNTAX_INDEX[idx + 1] as usize]
            .to_string()
    }
}

impl std::fmt::Display for ExportSyntax {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string())
    }
}
