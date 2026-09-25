//! Go `core` and `ast` pieces that only the frontend needs.

use crate::frontend::prelude::*;

// Go: core/typeacquisition.go:5 TypeAcquisition
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TypeAcquisition {
    pub enable: Tristate,
    pub include: Vec<String>,
    pub exclude: Vec<String>,
    pub disable_filename_based_type_acquisition: Tristate,
}

// Go: core/projectreference.go:5 ProjectReference
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ProjectReference {
    pub path: String,
    pub original_path: String,
    pub circular: bool,
}

// Go: core/projectreference.go:11 ResolveProjectReferencePath
pub fn resolve_project_reference_path(r: &ProjectReference) -> String {
    resolve_config_file_name_of_project_reference(&r.path)
}

// Go: core/projectreference.go:15 ResolveConfigFileNameOfProjectReference
pub fn resolve_config_file_name_of_project_reference(path: &str) -> String {
    if file_extension_is(path, EXTENSION_JSON) {
        return path.to_string();
    }
    combine_paths(path, &["tsconfig.json"])
}

/// Go interface `ast.HasFileName`.
pub trait HasFileName {
    fn file_name(&self) -> String;
    fn path(&self) -> Path;
}

impl HasFileName for HasFileNameImpl {
    fn file_name(&self) -> String {
        self.file_name.clone()
    }
    fn path(&self) -> Path {
        Path(self.path.clone())
    }
}

// Go: ast.SourceFile implements `ast.HasFileName`.
impl HasFileName for ParsedSourceFile {
    fn file_name(&self) -> String {
        ParsedSourceFile::file_name(self).to_string()
    }
    fn path(&self) -> Path {
        ParsedSourceFile::path(self).clone()
    }
}

// Go: core/core.go:527 GetScriptKindFromFileName
pub fn get_script_kind_from_file_name(file_name: &str) -> ScriptKind {
    if let Some(dot_pos) = file_name.rfind('.') {
        let ext = file_name[dot_pos..].to_lowercase();
        match ext.as_str() {
            EXTENSION_JS | EXTENSION_CJS | EXTENSION_MJS => return ScriptKind::JS,
            EXTENSION_JSX => return ScriptKind::JSX,
            EXTENSION_TS | EXTENSION_CTS | EXTENSION_MTS => return ScriptKind::TS,
            EXTENSION_TSX => return ScriptKind::TSX,
            EXTENSION_JSON => return ScriptKind::JSON,
            _ => {}
        }
    }
    ScriptKind::UNKNOWN
}
