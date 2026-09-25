//! Port of Go `core/compileroptions.go`, `core/tristate.go`,
//! `core/languagevariant.go`, `core/scriptkind.go` (plus their stringers),
//! and the conversion from `ts_options::CompilerOptions`.
//!
//! The Go enum types (`ScriptTarget`, `ModuleKind`, `ModuleResolutionKind`,
//! `ModuleDetectionKind`, `NewLineKind`, `JsxEmit`, `LanguageVariant`,
//! `ScriptKind`) are defined in `crate::flags` with the Go values. Their Go
//! methods are added here as inherent impls.

use crate::prelude::*;

// ---------------------------------------------------------------------------
// core/tristate.go
// ---------------------------------------------------------------------------

/// Go `core.Tristate`. Values match Go (`TSUnknown` = 0, `TSFalse` = 1,
/// `TSTrue` = 2).
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum Tristate {
    #[default]
    Unknown = 0,
    False = 1,
    True = 2,
}

impl Tristate {
    // Go: core/tristate.go:16 IsTrue
    #[must_use]
    pub fn is_true(self) -> bool {
        self == Tristate::True
    }

    // Go: core/tristate.go:20 IsTrueOrUnknown
    #[must_use]
    pub fn is_true_or_unknown(self) -> bool {
        self == Tristate::True || self == Tristate::Unknown
    }

    // Go: core/tristate.go:24 IsFalse
    #[must_use]
    pub fn is_false(self) -> bool {
        self == Tristate::False
    }

    // Go: core/tristate.go:28 IsFalseOrUnknown
    #[must_use]
    pub fn is_false_or_unknown(self) -> bool {
        self == Tristate::False || self == Tristate::Unknown
    }

    // Go: core/tristate.go:32 IsUnknown
    #[must_use]
    pub fn is_unknown(self) -> bool {
        self == Tristate::Unknown
    }

    // Go: core/tristate.go:36 DefaultIfUnknown
    #[must_use]
    pub fn default_if_unknown(self, value: Tristate) -> Tristate {
        if self == Tristate::Unknown {
            return value;
        }
        self
    }

    // Go: core/tristate.go:43 UnmarshalJSON
    pub fn unmarshal_json(&mut self, data: &[u8]) {
        *self = match data {
            b"true" => Tristate::True,
            b"false" => Tristate::False,
            _ => Tristate::Unknown,
        };
    }

    // Go: core/tristate.go:55 MarshalJSON
    #[must_use]
    pub fn marshal_json(self) -> &'static [u8] {
        match self {
            Tristate::True => b"true",
            Tristate::False => b"false",
            Tristate::Unknown => b"null",
        }
    }

    // Go: core/tristate_stringer_generated.go String
    #[must_use]
    pub fn string(self) -> String {
        match self {
            Tristate::Unknown => "TSUnknown",
            Tristate::False => "TSFalse",
            Tristate::True => "TSTrue",
        }
        .to_string()
    }
}

impl std::fmt::Display for Tristate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string())
    }
}

// Go: core/tristate.go:66 BoolToTristate
#[must_use]
pub fn bool_to_tristate(b: bool) -> Tristate {
    if b {
        return Tristate::True;
    }
    Tristate::False
}

// ---------------------------------------------------------------------------
// core/compileroptions.go
// ---------------------------------------------------------------------------

/// Go `core.CompilerOptions`. Field names are the Go names in snake case.
// Go: core/compileroptions.go:16 CompilerOptions
// PORT: Go `noCopy` is dropped. Go `[]string` fields are `Vec<String>`
// (nil and empty are the same for every reader) except `type_roots`, where
// `GetEffectiveTypeRoots` tests `TypeRoots != nil`, so it is
// `Option<Vec<String>>`. Go `*collections.OrderedMap` is `Option<IndexMap>`
// and Go `*int` is `Option<i32>`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CompilerOptions {
    pub allow_js: Tristate,
    pub allow_arbitrary_extensions: Tristate,
    pub allow_importing_ts_extensions: Tristate,
    pub allow_non_ts_extensions: Tristate,
    pub allow_umd_global_access: Tristate,
    pub allow_unreachable_code: Tristate,
    pub allow_unused_labels: Tristate,
    pub assume_changes_only_affect_direct_dependencies: Tristate,
    pub check_js: Tristate,
    pub custom_conditions: Vec<String>,
    pub composite: Tristate,
    pub emit_declaration_only: Tristate,
    pub emit_bom: Tristate,
    pub emit_decorator_metadata: Tristate,
    pub declaration: Tristate,
    pub declaration_dir: String,
    pub declaration_map: Tristate,
    pub deduplicate_packages: Tristate,
    pub disable_size_limit: Tristate,
    pub disable_source_of_project_reference_redirect: Tristate,
    pub disable_solution_searching: Tristate,
    pub disable_referenced_project_load: Tristate,
    pub erasable_syntax_only: Tristate,
    pub exact_optional_property_types: Tristate,
    pub experimental_decorators: Tristate,
    pub force_consistent_casing_in_file_names: Tristate,
    pub isolated_modules: Tristate,
    pub isolated_declarations: Tristate,
    pub ignore_config: Tristate,
    pub ignore_deprecations: String,
    pub import_helpers: Tristate,
    pub inline_source_map: Tristate,
    pub inline_sources: Tristate,
    pub init: Tristate,
    pub incremental: Tristate,
    pub jsx: JsxEmit,
    pub jsx_factory: String,
    pub jsx_fragment_factory: String,
    pub jsx_import_source: String,
    pub lib: Vec<String>,
    pub lib_replacement: Tristate,
    pub locale: String,
    pub map_root: String,
    pub module: ModuleKind,
    pub module_resolution: ModuleResolutionKind,
    pub module_suffixes: Vec<String>,
    pub module_detection: ModuleDetectionKind,
    pub new_line: NewLineKind,
    pub no_emit: Tristate,
    pub no_check: Tristate,
    pub no_error_truncation: Tristate,
    pub no_fallthrough_cases_in_switch: Tristate,
    pub no_implicit_any: Tristate,
    pub no_implicit_this: Tristate,
    pub no_implicit_returns: Tristate,
    pub no_emit_helpers: Tristate,
    pub no_lib: Tristate,
    pub no_property_access_from_index_signature: Tristate,
    pub no_unchecked_indexed_access: Tristate,
    pub no_emit_on_error: Tristate,
    pub no_unused_locals: Tristate,
    pub no_unused_parameters: Tristate,
    pub no_resolve: Tristate,
    pub no_implicit_override: Tristate,
    pub no_unchecked_side_effect_imports: Tristate,
    pub out_dir: String,
    /// Go `*OrderedMap[string, []string]`; a nil substitution slice is `None`.
    pub paths: Option<IndexMap<String, Option<Vec<String>>>>,
    pub preserve_const_enums: Tristate,
    pub preserve_symlinks: Tristate,
    pub project: String,
    pub resolve_json_module: Tristate,
    pub resolve_package_json_exports: Tristate,
    pub resolve_package_json_imports: Tristate,
    pub remove_comments: Tristate,
    pub rewrite_relative_import_extensions: Tristate,
    pub react_namespace: String,
    pub root_dir: String,
    pub root_dirs: Vec<String>,
    pub skip_lib_check: Tristate,
    pub stable_type_ordering: Tristate,
    pub strict: Tristate,
    pub strict_bind_call_apply: Tristate,
    pub strict_builtin_iterator_return: Tristate,
    pub strict_function_types: Tristate,
    pub strict_null_checks: Tristate,
    pub strict_property_initialization: Tristate,
    pub strip_internal: Tristate,
    pub skip_default_lib_check: Tristate,
    pub source_map: Tristate,
    pub source_root: String,
    pub suppress_output_path_check: Tristate,
    pub target: ScriptTarget,
    pub trace_resolution: Tristate,
    pub ts_build_info_file: String,
    pub type_roots: Option<Vec<String>>,
    pub types: Vec<String>,
    pub use_define_for_class_fields: Tristate,
    pub use_unknown_in_catch_variables: Tristate,
    pub verbatim_module_syntax: Tristate,
    pub max_node_module_js_depth: Option<i32>,

    // Deprecated: Do not use outside of options parsing and validation.
    pub allow_synthetic_default_imports: Tristate,
    // Deprecated: Do not use outside of options parsing and validation.
    pub always_strict: Tristate,
    // Deprecated: Do not use outside of options parsing and validation.
    pub base_url: String,
    // Deprecated: Do not use outside of options parsing and validation.
    pub downlevel_iteration: Tristate,
    // Deprecated: Do not use outside of options parsing and validation.
    pub es_module_interop: Tristate,
    // Deprecated: Do not use outside of options parsing and validation.
    pub out_file: String,

    // Internal fields
    pub config_file_path: String,
    pub no_dts_resolution: Tristate,
    pub paths_base_path: String,
    pub diagnostics: Tristate,
    pub extended_diagnostics: Tristate,
    pub generate_cpu_profile: String,
    pub generate_trace: String,
    pub list_emitted_files: Tristate,
    pub list_files: Tristate,
    pub explain_files: Tristate,
    pub list_files_only: Tristate,
    pub no_emit_for_js_files: Tristate,
    pub preserve_watch_output: Tristate,
    pub pretty: Tristate,
    pub version: Tristate,
    pub watch: Tristate,
    pub show_config: Tristate,
    pub build: Tristate,
    pub help: Tristate,
    pub all: Tristate,

    pub pprof_dir: String,
    pub single_threaded: Tristate,
    pub quiet: Tristate,
    pub checkers: Option<i32>,
}

static EMPTY_COMPILER_OPTIONS: std::sync::OnceLock<CompilerOptions> = std::sync::OnceLock::new();

// Go: core/compileroptions.go:172 EmptyCompilerOptions
#[must_use]
pub fn empty_compiler_options() -> &'static CompilerOptions {
    EMPTY_COMPILER_OPTIONS.get_or_init(CompilerOptions::default)
}

impl CompilerOptions {
    // Go: core/compileroptions.go:177 Clone
    // Clone creates a shallow copy of the CompilerOptions.
    // PORT: Go copies every exported field by reflection. The derived
    // `Clone::clone` copies every field, which is the same set, so Go
    // `options.Clone()` ports to `options.clone()` with no inherent method.

    // Go: core/compileroptions.go:193 GetEmitScriptTarget
    #[must_use]
    pub fn get_emit_script_target(&self) -> ScriptTarget {
        if self.target != ScriptTarget::NONE {
            return self.target;
        }
        ScriptTarget::LATEST_STANDARD
    }

    // Go: core/compileroptions.go:200 GetEmitModuleKind
    #[must_use]
    pub fn get_emit_module_kind(&self) -> ModuleKind {
        if self.module != ModuleKind::NONE {
            return self.module;
        }

        let target = self.get_emit_script_target();
        if target == ScriptTarget::ES_NEXT {
            return ModuleKind::ES_NEXT;
        }
        if target >= ScriptTarget::ES2022 {
            return ModuleKind::ES2022;
        }
        if target >= ScriptTarget::ES2020 {
            return ModuleKind::ES2020;
        }
        if target >= ScriptTarget::ES2015 {
            return ModuleKind::ES2015;
        }
        ModuleKind::COMMON_JS
    }

    // Go: core/compileroptions.go:221 GetModuleResolutionKind
    #[must_use]
    pub fn get_module_resolution_kind(&self) -> ModuleResolutionKind {
        match self.module_resolution {
            ModuleResolutionKind::UNKNOWN
            | ModuleResolutionKind::CLASSIC
            | ModuleResolutionKind::NODE10 => match self.get_emit_module_kind() {
                ModuleKind::NODE16 | ModuleKind::NODE18 | ModuleKind::NODE20 => {
                    ModuleResolutionKind::NODE16
                }
                ModuleKind::NODE_NEXT => ModuleResolutionKind::NODE_NEXT,
                _ => ModuleResolutionKind::BUNDLER,
            },
            _ => self.module_resolution,
        }
    }

    // Go: core/compileroptions.go:237 GetEmitModuleDetectionKind
    #[must_use]
    pub fn get_emit_module_detection_kind(&self) -> ModuleDetectionKind {
        if self.module_detection != ModuleDetectionKind::NONE {
            return self.module_detection;
        }
        let module_kind = self.get_emit_module_kind();
        if ModuleKind::NODE16 <= module_kind && module_kind <= ModuleKind::NODE_NEXT {
            return ModuleDetectionKind::FORCE;
        }
        ModuleDetectionKind::AUTO
    }

    // Go: core/compileroptions.go:248 GetResolvePackageJsonExports
    #[must_use]
    pub fn get_resolve_package_json_exports(&self) -> bool {
        self.resolve_package_json_exports.is_true_or_unknown()
    }

    // Go: core/compileroptions.go:252 GetResolvePackageJsonImports
    #[must_use]
    pub fn get_resolve_package_json_imports(&self) -> bool {
        self.resolve_package_json_imports.is_true_or_unknown()
    }

    // Go: core/compileroptions.go:256 GetAllowImportingTsExtensions
    #[must_use]
    pub fn get_allow_importing_ts_extensions(&self) -> bool {
        self.allow_importing_ts_extensions.is_true()
            || self.rewrite_relative_import_extensions.is_true()
    }

    // Go: core/compileroptions.go:260 AllowImportingTsExtensionsFrom
    #[must_use]
    pub fn allow_importing_ts_extensions_from(&self, file_name: &str) -> bool {
        self.get_allow_importing_ts_extensions() || tspath_is_declaration_file_name(file_name)
    }

    // Go: core/compileroptions.go:264 GetResolveJsonModule
    #[must_use]
    pub fn get_resolve_json_module(&self) -> bool {
        if self.resolve_json_module != Tristate::Unknown {
            return self.resolve_json_module == Tristate::True;
        }
        match self.get_emit_module_kind() {
            // TODO in 6.0: add Node16/Node18
            ModuleKind::NODE20 | ModuleKind::NODE_NEXT => return true,
            _ => {}
        }
        self.get_module_resolution_kind() == ModuleResolutionKind::BUNDLER
    }

    // Go: core/compileroptions.go:276 ShouldPreserveConstEnums
    #[must_use]
    pub fn should_preserve_const_enums(&self) -> bool {
        self.preserve_const_enums == Tristate::True || self.get_isolated_modules()
    }

    // Go: core/compileroptions.go:280 GetAllowJS
    #[must_use]
    pub fn get_allow_js(&self) -> bool {
        if self.allow_js != Tristate::Unknown {
            return self.allow_js == Tristate::True;
        }
        self.check_js == Tristate::True
    }

    // Go: core/compileroptions.go:287 GetJSXTransformEnabled
    #[must_use]
    pub fn get_jsx_transform_enabled(&self) -> bool {
        let jsx = self.jsx;
        jsx == JsxEmit::REACT || jsx == JsxEmit::REACT_JSX || jsx == JsxEmit::REACT_JSX_DEV
    }

    // Go: core/compileroptions.go:292 GetStrictOptionValue
    #[must_use]
    pub fn get_strict_option_value(&self, value: Tristate) -> bool {
        if value != Tristate::Unknown {
            return value == Tristate::True;
        }
        self.strict != Tristate::False
    }

    // Go: core/compileroptions.go:299 GetEffectiveTypeRoots
    /// Returns `(result, fromConfig)`.
    #[must_use]
    pub fn get_effective_type_roots(&self, current_directory: &str) -> (Vec<String>, bool) {
        if let Some(type_roots) = &self.type_roots {
            return (type_roots.clone(), true);
        }
        let base_dir: String;
        if !self.config_file_path.is_empty() {
            base_dir = tspath_get_directory_path(&self.config_file_path);
        } else {
            base_dir = current_directory.to_string();
            if base_dir.is_empty() {
                // This was accounted for in the TS codebase, but only for third-party API usage
                // where the module resolution host does not provide a getCurrentDirectory().
                panic!(
                    "cannot get effective type roots without a config file path or current directory"
                );
            }
        }

        let mut type_roots: Vec<String> = Vec::with_capacity(base_dir.matches('/').count());
        tspath_for_each_ancestor_directory(&base_dir, &mut |dir: &str| {
            type_roots.push(ts_path::combine_paths(dir, &["node_modules", "@types"]));
            false
        });
        (type_roots, false)
    }

    // Go: core/compileroptions.go:324 UsesWildcardTypes
    // UsesWildcardTypes returns true if this option's types array includes "*"
    #[must_use]
    pub fn uses_wildcard_types(&self) -> bool {
        self.types.iter().any(|t| t == "*")
    }

    // Go: core/compileroptions.go:328 GetIsolatedModules
    #[must_use]
    pub fn get_isolated_modules(&self) -> bool {
        self.isolated_modules == Tristate::True || self.verbatim_module_syntax == Tristate::True
    }

    // Go: core/compileroptions.go:332 IsIncremental
    #[must_use]
    pub fn is_incremental(&self) -> bool {
        self.incremental.is_true() || self.composite.is_true()
    }

    // Go: core/compileroptions.go:336 GetEmitStandardClassFields
    #[must_use]
    pub fn get_emit_standard_class_fields(&self) -> bool {
        self.use_define_for_class_fields != Tristate::False
            && self.get_emit_script_target() >= ScriptTarget::ES2022
    }

    // Go: core/compileroptions.go:340 GetUseDefineForClassFields
    #[must_use]
    pub fn get_use_define_for_class_fields(&self) -> bool {
        if self.use_define_for_class_fields == Tristate::Unknown {
            return self.get_emit_script_target() >= ScriptTarget::ES2022;
        }
        self.use_define_for_class_fields == Tristate::True
    }

    // Go: core/compileroptions.go:347 GetEmitDeclarations
    #[must_use]
    pub fn get_emit_declarations(&self) -> bool {
        self.declaration.is_true() || self.composite.is_true()
    }

    // Go: core/compileroptions.go:351 GetAreDeclarationMapsEnabled
    #[must_use]
    pub fn get_are_declaration_maps_enabled(&self) -> bool {
        self.declaration_map == Tristate::True && self.get_emit_declarations()
    }

    // Go: core/compileroptions.go:355 HasJsonModuleEmitEnabled
    #[must_use]
    pub fn has_json_module_emit_enabled(&self) -> bool {
        match self.get_emit_module_kind() {
            ModuleKind::SYSTEM | ModuleKind::UMD => return false,
            _ => {}
        }
        true
    }

    // Go: core/compileroptions.go:363 GetPathsBasePath
    #[must_use]
    pub fn get_paths_base_path(&self, current_directory: &str) -> String {
        // Go `Paths.Size()` is 0 for a nil map.
        if self.paths.as_ref().map_or(0, IndexMap::len) == 0 {
            return String::new();
        }
        if !self.paths_base_path.is_empty() {
            return self.paths_base_path.clone();
        }
        current_directory.to_string()
    }
}

impl ModuleKind {
    // Go: core/compileroptions.go:424 ResolutionModeESM
    // PORT: Go `ResolutionMode` is an alias of `ModuleKind`, so
    // `core.ResolutionModeESM` is also reachable as `ResolutionMode::ESM`.
    // `ResolutionModeNone` and `ResolutionModeCommonJS` are
    // `ResolutionMode::NONE` and `ResolutionMode::COMMON_JS`.
    pub const ESM: Self = Self::ES_NEXT;

    // Go: core/compileroptions.go:409 IsNonNodeESM
    #[must_use]
    pub fn is_non_node_esm(self) -> bool {
        self >= ModuleKind::ES2015 && self <= ModuleKind::ES_NEXT
    }

    // Go: core/compileroptions.go:413 SupportsImportAttributes
    #[must_use]
    pub fn supports_import_attributes(self) -> bool {
        ModuleKind::NODE18 <= self && self <= ModuleKind::NODE_NEXT
            || self == ModuleKind::PRESERVE
            || self == ModuleKind::ES_NEXT
    }

    // Go: core/modulekind_stringer_generated.go String
    #[must_use]
    pub fn string(self) -> String {
        let name = match self {
            ModuleKind::NONE => "None",
            ModuleKind::COMMON_JS => "CommonJS",
            ModuleKind::AMD => "AMD",
            ModuleKind::UMD => "UMD",
            ModuleKind::SYSTEM => "System",
            ModuleKind::ES2015 => "ES2015",
            ModuleKind::ES2020 => "ES2020",
            ModuleKind::ES2022 => "ES2022",
            ModuleKind::ES_NEXT => "ESNext",
            ModuleKind::NODE16 => "Node16",
            ModuleKind::NODE18 => "Node18",
            ModuleKind::NODE20 => "Node20",
            ModuleKind::NODE_NEXT => "NodeNext",
            ModuleKind::PRESERVE => "Preserve",
            _ => return format!("ModuleKind({})", self.0),
        };
        name.to_string()
    }
}

impl std::fmt::Display for ModuleKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string())
    }
}

/// Go `core.ResolutionMode` (`ModuleKindNone | ModuleKindCommonJS | ModuleKindESNext`).
// Go: core/compileroptions.go:419 ResolutionMode
pub type ResolutionMode = ModuleKind;

// Go: core/compileroptions.go:422 ResolutionModeNone
pub const RESOLUTION_MODE_NONE: ResolutionMode = ModuleKind::NONE;
// Go: core/compileroptions.go:423 ResolutionModeCommonJS
pub const RESOLUTION_MODE_COMMON_JS: ResolutionMode = ModuleKind::COMMON_JS;
// Go: core/compileroptions.go:424 ResolutionModeESM
pub const RESOLUTION_MODE_ESM: ResolutionMode = ModuleKind::ES_NEXT;

// Go: core/compileroptions.go:445 ModuleKindToModuleResolutionKind
/// Go map lookup `ModuleKindToModuleResolutionKind[kind]` as `(value, ok)`.
#[must_use]
pub fn module_kind_to_module_resolution_kind(kind: ModuleKind) -> (ModuleResolutionKind, bool) {
    match kind {
        ModuleKind::NODE16 => (ModuleResolutionKind::NODE16, true),
        ModuleKind::NODE_NEXT => (ModuleResolutionKind::NODE_NEXT, true),
        _ => (ModuleResolutionKind::UNKNOWN, false),
    }
}

impl ModuleResolutionKind {
    // Go: core/compileroptions.go:457 String
    // We don't use stringer on this for now, because these values
    // are user-facing in --traceResolution, and stringer currently
    // lacks the ability to remove the "ModuleResolutionKind" prefix
    // when generating code for multiple types into the same output
    // file. Additionally, since there's no TS equivalent of
    // `ModuleResolutionKindUnknown`, we want to panic on that case,
    // as it probably represents a mistake when porting TS to Go.
    #[must_use]
    pub fn string(self) -> String {
        match self {
            ModuleResolutionKind::UNKNOWN => {
                panic!("should not use zero value of ModuleResolutionKind")
            }
            ModuleResolutionKind::CLASSIC => "Classic".to_string(),
            ModuleResolutionKind::NODE10 => "Node10".to_string(),
            ModuleResolutionKind::NODE16 => "Node16".to_string(),
            ModuleResolutionKind::NODE_NEXT => "NodeNext".to_string(),
            ModuleResolutionKind::BUNDLER => "Bundler".to_string(),
            _ => panic!("unhandled case in ModuleResolutionKind.String"),
        }
    }
}

impl std::fmt::Display for ModuleResolutionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string())
    }
}

// Go: core/compileroptions.go:484 GetNewLineKind
#[must_use]
pub fn get_new_line_kind(s: &str) -> NewLineKind {
    match s {
        "\r\n" => NewLineKind::CRLF,
        "\n" => NewLineKind::LF,
        _ => NewLineKind::NONE,
    }
}

impl NewLineKind {
    // Go: core/compileroptions.go:495 GetNewLineCharacter
    #[must_use]
    pub fn get_new_line_character(self) -> &'static str {
        match self {
            NewLineKind::CRLF => "\r\n",
            _ => "\n",
        }
    }
}

impl ScriptTarget {
    // Go: core/scripttarget_stringer_generated.go String
    #[must_use]
    pub fn string(self) -> String {
        let name = match self.0 {
            0 => "None",
            1 => "ES5",
            2 => "ES2015",
            3 => "ES2016",
            4 => "ES2017",
            5 => "ES2018",
            6 => "ES2019",
            7 => "ES2020",
            8 => "ES2021",
            9 => "ES2022",
            10 => "ES2023",
            11 => "ES2024",
            12 => "ES2025",
            99 => "ESNext",
            100 => "JSON",
            _ => return format!("ScriptTarget({})", self.0),
        };
        name.to_string()
    }
}

impl std::fmt::Display for ScriptTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string())
    }
}

impl JsxEmit {
    // Go: core/compileroptions.go:538 String
    #[must_use]
    pub fn string(self) -> String {
        match self {
            JsxEmit::NONE => panic!("should not use zero value of JsxEmit"),
            JsxEmit::PRESERVE => "preserve".to_string(),
            JsxEmit::REACT_NATIVE => "react-native".to_string(),
            JsxEmit::REACT => "react".to_string(),
            JsxEmit::REACT_JSX => "react-jsx".to_string(),
            JsxEmit::REACT_JSX_DEV => "react-jsxdev".to_string(),
            _ => panic!("unhandled case in JsxEmit.String"),
        }
    }
}

impl std::fmt::Display for JsxEmit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string())
    }
}

// ---------------------------------------------------------------------------
// core/languagevariant.go, core/scriptkind.go
// ---------------------------------------------------------------------------
// The types and constants live in `crate::flags` (`LanguageVariant`,
// `ScriptKind`). Only the generated stringers are ported here.

impl LanguageVariant {
    // Go: core/languagevariant_stringer_generated.go String
    #[must_use]
    pub fn string(self) -> String {
        match self {
            LanguageVariant::STANDARD => "LanguageVariantStandard".to_string(),
            LanguageVariant::JSX => "LanguageVariantJSX".to_string(),
            _ => format!("LanguageVariant({})", self.0),
        }
    }
}

impl std::fmt::Display for LanguageVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string())
    }
}

impl ScriptKind {
    // Go: core/scriptkind_stringer_generated.go String
    // PORT: matches the named constants, so it follows whatever value
    // `crate::flags` gives `ScriptKind::DEFERRED`. Go iota makes it 7.
    #[must_use]
    pub fn string(self) -> String {
        let name = match self {
            ScriptKind::UNKNOWN => "ScriptKindUnknown",
            ScriptKind::JS => "ScriptKindJS",
            ScriptKind::JSX => "ScriptKindJSX",
            ScriptKind::TS => "ScriptKindTS",
            ScriptKind::TSX => "ScriptKindTSX",
            ScriptKind::EXTERNAL => "ScriptKindExternal",
            ScriptKind::JSON => "ScriptKindJSON",
            ScriptKind::DEFERRED => "ScriptKindDeferred",
            _ => return format!("ScriptKind({})", self.0),
        };
        name.to_string()
    }
}

impl std::fmt::Display for ScriptKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string())
    }
}

// ---------------------------------------------------------------------------
// tspath helpers used above. Private so they do not clash with a tspath port
// elsewhere in the crate.
// ---------------------------------------------------------------------------

// Go: tspath/path.go:697 RemoveTrailingDirectorySeparator
fn tspath_remove_trailing_directory_separator(path: &str) -> &str {
    if path.ends_with('/') || path.ends_with('\\') {
        return &path[..path.len() - 1];
    }
    path
}

// Go: tspath/path.go:250 GetDirectoryPath
fn tspath_get_directory_path(path: &str) -> String {
    let path = ts_path::normalize_slashes(path);

    // If the path provided is itself a root, then return it.
    let root_length = ts_path::root_length(&path);
    if root_length == path.len() {
        return path;
    }

    // return the leading portion of the path up to the last (non-terminal) directory separator
    // but not including any trailing directory separator.
    let path = tspath_remove_trailing_directory_separator(&path);
    let last = path.rfind('/').map_or(-1, |i| i as i64);
    let end = std::cmp::max(root_length as i64, last) as usize;
    path[..end].to_string()
}

// Go: tspath/path.go:840 GetBaseFileName
fn tspath_get_base_file_name(path: &str) -> String {
    let path = ts_path::normalize_slashes(path);

    // if the path provided is itself the root, then it has no file name.
    let root_length = ts_path::root_length(&path);
    if root_length == path.len() {
        return String::new();
    }

    // return the trailing portion of the path starting after the last (non-terminal) directory
    // separator but not including any trailing directory separator.
    let path = tspath_remove_trailing_directory_separator(&path);
    let after_sep = path.rfind('/').map_or(0, |i| i + 1);
    let start = std::cmp::max(ts_path::root_length(path), after_sep);
    path[start..].to_string()
}

// Go: tspath/extension.go:111 GetDeclarationFileExtension
fn tspath_get_declaration_file_extension(file_name: &str) -> String {
    let base = tspath_get_base_file_name(file_name);
    // Go: tspath.SupportedDeclarationExtensions
    for ext in [".d.ts", ".d.cts", ".d.mts"] {
        if base.ends_with(ext) {
            return ext.to_string();
        }
    }
    if base.ends_with(".ts") {
        if let Some(index) = base.find(".d.") {
            return base[index..].to_string();
        }
    }
    String::new()
}

// Go: tspath/extension.go:103 IsDeclarationFileName
fn tspath_is_declaration_file_name(file_name: &str) -> bool {
    !tspath_get_declaration_file_extension(file_name).is_empty()
}

// Go: tspath/path.go:1066 ForEachAncestorDirectory
// PORT: the callback returns only `stop`; the only caller here has no result.
fn tspath_for_each_ancestor_directory(
    directory: &str,
    callback: &mut dyn FnMut(&str) -> bool,
) -> bool {
    let mut directory = directory.to_string();
    loop {
        if callback(&directory) {
            return true;
        }

        let parent_path = tspath_get_directory_path(&directory);
        if parent_path == directory {
            return false;
        }

        directory = parent_path;
    }
}

// ---------------------------------------------------------------------------
// tsoptions/enummaps.go (lib names), used by `from_ts_options`.
// ---------------------------------------------------------------------------

// PORT: Go `LibMap` and `GetLibFileName` live in `ts_compiler`
// (`ts_compiler::tsoptions_lib_map` and `ts_compiler::tsoptions_get_lib_file_name`), because
// the `ts_compiler` program loader also resolves `/// <reference lib>` names
// through them and cannot depend on this crate.

// ---------------------------------------------------------------------------
// Conversion from `ts_options::CompilerOptions`.
// ---------------------------------------------------------------------------

/// Maps a `ts_options` bool that has no "specified" flag. `ts_options`
/// applies defaults, so a value equal to its default is taken as unset
/// (Go `TSUnknown`), and any other value as explicit.
fn ts_default_tristate(value: bool, ts_default: bool) -> Tristate {
    if value == ts_default {
        return Tristate::Unknown;
    }
    bool_to_tristate(value)
}

/// Maps a `ts_options` bool that has a matching `*_specified` flag.
fn ts_specified_tristate(value: bool, specified: bool) -> Tristate {
    if specified {
        return bool_to_tristate(value);
    }
    Tristate::Unknown
}

fn ts_option_tristate(value: Option<bool>) -> Tristate {
    match value {
        Some(b) => bool_to_tristate(b),
        None => Tristate::Unknown,
    }
}

fn ts_module_kind(kind: ts_options::ModuleKind) -> ModuleKind {
    use ts_options::ModuleKind as K;
    match kind {
        K::None => ModuleKind::NONE,
        K::CommonJs => ModuleKind::COMMON_JS,
        K::Amd => ModuleKind::AMD,
        K::Umd => ModuleKind::UMD,
        K::System => ModuleKind::SYSTEM,
        K::Es2015 => ModuleKind::ES2015,
        K::Es2020 => ModuleKind::ES2020,
        K::Es2022 => ModuleKind::ES2022,
        K::EsNext => ModuleKind::ES_NEXT,
        K::Node16 => ModuleKind::NODE16,
        K::Node18 => ModuleKind::NODE18,
        K::Node20 => ModuleKind::NODE20,
        K::NodeNext => ModuleKind::NODE_NEXT,
        K::Preserve => ModuleKind::PRESERVE,
    }
}

fn ts_module_resolution_kind(kind: ts_options::ModuleResolutionKind) -> ModuleResolutionKind {
    use ts_options::ModuleResolutionKind as K;
    match kind {
        K::Classic => ModuleResolutionKind::CLASSIC,
        K::Node10 => ModuleResolutionKind::NODE10,
        K::Node16 => ModuleResolutionKind::NODE16,
        K::NodeNext => ModuleResolutionKind::NODE_NEXT,
        K::Bundler => ModuleResolutionKind::BUNDLER,
    }
}

fn ts_script_target(target: ts_options::ScriptTarget) -> ScriptTarget {
    use ts_options::ScriptTarget as K;
    match target {
        // PORT: Go has no ES3 target (tsoptions rejects it). Map to the
        // lowest Go target.
        K::Es3 | K::Es5 => ScriptTarget::ES5,
        K::Es2015 => ScriptTarget::ES2015,
        K::Es2016 => ScriptTarget::ES2016,
        K::Es2017 => ScriptTarget::ES2017,
        K::Es2018 => ScriptTarget::ES2018,
        K::Es2019 => ScriptTarget::ES2019,
        K::Es2020 => ScriptTarget::ES2020,
        K::Es2021 => ScriptTarget::ES2021,
        K::Es2022 => ScriptTarget::ES2022,
        K::Es2023 => ScriptTarget::ES2023,
        K::Es2024 => ScriptTarget::ES2024,
        K::Es2025 => ScriptTarget::ES2025,
        K::EsNext => ScriptTarget::ES_NEXT,
    }
}

fn ts_jsx_emit(jsx: ts_options::JsxEmit) -> JsxEmit {
    use ts_options::JsxEmit as K;
    match jsx {
        K::None => JsxEmit::NONE,
        K::Preserve => JsxEmit::PRESERVE,
        K::React => JsxEmit::REACT,
        K::ReactNative => JsxEmit::REACT_NATIVE,
        K::ReactJsx => JsxEmit::REACT_JSX,
        K::ReactJsxDev => JsxEmit::REACT_JSX_DEV,
    }
}

fn ts_module_detection_kind(kind: ts_options::ModuleDetectionKind) -> ModuleDetectionKind {
    use ts_options::ModuleDetectionKind as K;
    match kind {
        K::Legacy => ModuleDetectionKind::LEGACY,
        K::Auto => ModuleDetectionKind::AUTO,
        K::Force => ModuleDetectionKind::FORCE,
    }
}

fn ts_new_line_kind(kind: ts_options::NewLineKind) -> NewLineKind {
    use ts_options::NewLineKind as K;
    match kind {
        K::Lf => NewLineKind::LF,
        K::Crlf => NewLineKind::CRLF,
    }
}

/// Builds the Go-shaped options from the normalized `ts_options` options.
///
/// `ts_options` stores values after defaults. Go stores only what the user
/// wrote, and its getters apply the defaults. Rules used here:
/// - a field with a `*_specified` flag is `Unknown` unless specified;
/// - an `Option<bool>` field is `Unknown` when `None`;
/// - any other bool is `Unknown` when it equals the `ts_options` default;
/// - `module` and `moduleDetection` are `NONE` unless specified, and
///   `moduleResolution` is the configured value (`UNKNOWN` when not set);
/// - `target` keeps its value (the `ts_options` default is ES2025, which is
///   Go `ScriptTargetLatestStandard`, so `GetEmitScriptTarget` agrees);
/// - `lib` holds Go lib file names (`lib.dom.d.ts`), as Go tsoptions stores;
/// - fields that `ts_options` does not model keep the Go zero value.
#[must_use]
pub fn from_ts_options(opts: &ts_options::CompilerOptions) -> CompilerOptions {
    let d = ts_options::CompilerOptions::default();

    let lib: Vec<String> = opts
        .lib
        .as_ref()
        .map(|libs| {
            libs.iter()
                .filter_map(|name| ts_compiler::tsoptions_get_lib_file_name(name))
                .collect()
        })
        .unwrap_or_default();

    // PORT: `ts_options` keeps `paths` in a BTreeMap, so Go's source order
    // is lost; keys come out sorted. An empty map is treated as nil.
    let paths = if opts.paths.is_empty() {
        None
    } else {
        Some(
            opts.paths
                .iter()
                .map(|(k, v)| (k.clone(), Some(v.clone())))
                .collect::<IndexMap<_, _>>(),
        )
    };

    CompilerOptions {
        allow_js: ts_specified_tristate(opts.allow_js, opts.allow_js_specified),
        allow_arbitrary_extensions: ts_default_tristate(
            opts.allow_arbitrary_extensions,
            d.allow_arbitrary_extensions,
        ),
        allow_importing_ts_extensions: ts_default_tristate(
            opts.allow_importing_ts_extensions,
            d.allow_importing_ts_extensions,
        ),
        allow_non_ts_extensions: Tristate::Unknown,
        allow_umd_global_access: ts_default_tristate(
            opts.allow_umd_global_access,
            d.allow_umd_global_access,
        ),
        allow_unreachable_code: ts_option_tristate(opts.allow_unreachable_code),
        allow_unused_labels: ts_option_tristate(opts.allow_unused_labels),
        assume_changes_only_affect_direct_dependencies: ts_default_tristate(
            opts.assume_changes_only_affect_direct_dependencies,
            d.assume_changes_only_affect_direct_dependencies,
        ),
        // PORT: `ts_options` has no "specified" flag for checkJs, so an
        // explicit `checkJs: false` reads as Go `TSUnknown` here.
        check_js: ts_default_tristate(opts.check_js, d.check_js),
        custom_conditions: opts.custom_conditions.clone().unwrap_or_default(),
        composite: ts_default_tristate(opts.composite, d.composite),
        emit_declaration_only: ts_default_tristate(
            opts.emit_declaration_only,
            d.emit_declaration_only,
        ),
        emit_bom: ts_default_tristate(opts.emit_bom, d.emit_bom),
        emit_decorator_metadata: ts_default_tristate(
            opts.emit_decorator_metadata,
            d.emit_decorator_metadata,
        ),
        declaration: ts_specified_tristate(opts.declaration, opts.declaration_specified),
        declaration_dir: opts.declaration_dir.clone().unwrap_or_default(),
        declaration_map: ts_default_tristate(opts.declaration_map, d.declaration_map),
        deduplicate_packages: ts_default_tristate(
            opts.deduplicate_packages,
            d.deduplicate_packages,
        ),
        disable_size_limit: ts_default_tristate(opts.disable_size_limit, d.disable_size_limit),
        disable_source_of_project_reference_redirect: Tristate::Unknown,
        disable_solution_searching: Tristate::Unknown,
        disable_referenced_project_load: Tristate::Unknown,
        erasable_syntax_only: ts_default_tristate(
            opts.erasable_syntax_only,
            d.erasable_syntax_only,
        ),
        exact_optional_property_types: ts_default_tristate(
            opts.exact_optional_property_types,
            d.exact_optional_property_types,
        ),
        experimental_decorators: ts_default_tristate(
            opts.experimental_decorators,
            d.experimental_decorators,
        ),
        force_consistent_casing_in_file_names: ts_default_tristate(
            opts.force_consistent_casing_in_file_names,
            d.force_consistent_casing_in_file_names,
        ),
        isolated_modules: ts_default_tristate(opts.isolated_modules, d.isolated_modules),
        isolated_declarations: ts_default_tristate(
            opts.isolated_declarations,
            d.isolated_declarations,
        ),
        ignore_config: Tristate::Unknown,
        ignore_deprecations: opts.ignore_deprecations.clone().unwrap_or_default(),
        import_helpers: ts_default_tristate(opts.import_helpers, d.import_helpers),
        inline_source_map: ts_default_tristate(opts.inline_source_map, d.inline_source_map),
        inline_sources: ts_default_tristate(opts.inline_sources, d.inline_sources),
        init: Tristate::Unknown,
        incremental: ts_specified_tristate(opts.incremental, opts.incremental_specified),
        jsx: ts_jsx_emit(opts.jsx),
        jsx_factory: opts.jsx_factory.clone().unwrap_or_default(),
        jsx_fragment_factory: opts.jsx_fragment_factory.clone().unwrap_or_default(),
        jsx_import_source: opts.jsx_import_source.clone().unwrap_or_default(),
        lib,
        lib_replacement: ts_default_tristate(opts.lib_replacement, d.lib_replacement),
        locale: String::new(),
        map_root: opts.map_root.clone().unwrap_or_default(),
        module: if opts.module_specified {
            ts_module_kind(opts.module)
        } else {
            ModuleKind::NONE
        },
        module_resolution: opts
            .module_resolution_configured
            .map_or(ModuleResolutionKind::UNKNOWN, ts_module_resolution_kind),
        module_suffixes: opts.module_suffixes.clone().unwrap_or_default(),
        module_detection: if opts.module_detection_specified {
            ts_module_detection_kind(opts.module_detection)
        } else {
            ModuleDetectionKind::NONE
        },
        new_line: ts_new_line_kind(opts.new_line),
        no_emit: ts_default_tristate(opts.no_emit, d.no_emit),
        no_check: ts_default_tristate(opts.no_check, d.no_check),
        no_error_truncation: ts_default_tristate(opts.no_error_truncation, d.no_error_truncation),
        no_fallthrough_cases_in_switch: ts_default_tristate(
            opts.no_fallthrough_cases_in_switch,
            d.no_fallthrough_cases_in_switch,
        ),
        no_implicit_any: ts_specified_tristate(
            opts.no_implicit_any,
            opts.no_implicit_any_specified,
        ),
        no_implicit_this: ts_specified_tristate(
            opts.no_implicit_this,
            opts.no_implicit_this_specified,
        ),
        no_implicit_returns: ts_default_tristate(opts.no_implicit_returns, d.no_implicit_returns),
        no_emit_helpers: ts_default_tristate(opts.no_emit_helpers, d.no_emit_helpers),
        no_lib: ts_default_tristate(opts.no_lib, d.no_lib),
        no_property_access_from_index_signature: ts_default_tristate(
            opts.no_property_access_from_index_signature,
            d.no_property_access_from_index_signature,
        ),
        no_unchecked_indexed_access: ts_default_tristate(
            opts.no_unchecked_indexed_access,
            d.no_unchecked_indexed_access,
        ),
        no_emit_on_error: ts_default_tristate(opts.no_emit_on_error, d.no_emit_on_error),
        no_unused_locals: ts_default_tristate(opts.no_unused_locals, d.no_unused_locals),
        no_unused_parameters: ts_default_tristate(
            opts.no_unused_parameters,
            d.no_unused_parameters,
        ),
        no_resolve: ts_default_tristate(opts.no_resolve, d.no_resolve),
        no_implicit_override: ts_default_tristate(
            opts.no_implicit_override,
            d.no_implicit_override,
        ),
        no_unchecked_side_effect_imports: ts_specified_tristate(
            opts.no_unchecked_side_effect_imports,
            opts.no_unchecked_side_effect_imports_specified,
        ),
        out_dir: opts.out_dir.clone().unwrap_or_default(),
        paths,
        preserve_const_enums: ts_default_tristate(
            opts.preserve_const_enums,
            d.preserve_const_enums,
        ),
        preserve_symlinks: ts_default_tristate(opts.preserve_symlinks, d.preserve_symlinks),
        project: String::new(),
        resolve_json_module: ts_specified_tristate(
            opts.resolve_json_module,
            opts.resolve_json_module_specified,
        ),
        resolve_package_json_exports: ts_default_tristate(
            opts.resolve_package_json_exports,
            d.resolve_package_json_exports,
        ),
        resolve_package_json_imports: ts_default_tristate(
            opts.resolve_package_json_imports,
            d.resolve_package_json_imports,
        ),
        remove_comments: ts_default_tristate(opts.remove_comments, d.remove_comments),
        rewrite_relative_import_extensions: ts_default_tristate(
            opts.rewrite_relative_import_extensions,
            d.rewrite_relative_import_extensions,
        ),
        react_namespace: opts.react_namespace.clone().unwrap_or_default(),
        root_dir: opts.root_dir.clone().unwrap_or_default(),
        root_dirs: opts.root_dirs.clone(),
        skip_lib_check: ts_default_tristate(opts.skip_lib_check, d.skip_lib_check),
        stable_type_ordering: ts_default_tristate(
            opts.stable_type_ordering,
            d.stable_type_ordering,
        ),
        strict: ts_specified_tristate(opts.strict, opts.strict_specified),
        strict_bind_call_apply: ts_specified_tristate(
            opts.strict_bind_call_apply,
            opts.strict_bind_call_apply_specified,
        ),
        strict_builtin_iterator_return: ts_specified_tristate(
            opts.strict_builtin_iterator_return,
            opts.strict_builtin_iterator_return_specified,
        ),
        strict_function_types: ts_specified_tristate(
            opts.strict_function_types,
            opts.strict_function_types_specified,
        ),
        strict_null_checks: ts_specified_tristate(
            opts.strict_null_checks,
            opts.strict_null_checks_specified,
        ),
        strict_property_initialization: ts_specified_tristate(
            opts.strict_property_initialization,
            opts.strict_property_initialization_specified,
        ),
        strip_internal: ts_default_tristate(opts.strip_internal, d.strip_internal),
        skip_default_lib_check: ts_default_tristate(
            opts.skip_default_lib_check,
            d.skip_default_lib_check,
        ),
        source_map: ts_default_tristate(opts.source_map, d.source_map),
        source_root: opts.source_root.clone().unwrap_or_default(),
        suppress_output_path_check: Tristate::Unknown,
        target: ts_script_target(opts.target),
        trace_resolution: ts_default_tristate(opts.trace_resolution, d.trace_resolution),
        ts_build_info_file: opts.ts_build_info_file.clone().unwrap_or_default(),
        type_roots: opts.type_roots.clone(),
        types: opts.types.clone().unwrap_or_default(),
        use_define_for_class_fields: ts_option_tristate(opts.use_define_for_class_fields),
        use_unknown_in_catch_variables: ts_specified_tristate(
            opts.use_unknown_in_catch_variables,
            opts.use_unknown_in_catch_variables_specified,
        ),
        verbatim_module_syntax: ts_default_tristate(
            opts.verbatim_module_syntax,
            d.verbatim_module_syntax,
        ),
        max_node_module_js_depth: opts
            .max_node_module_js_depth
            .map(|depth| i32::try_from(depth).unwrap_or(i32::MAX)),

        allow_synthetic_default_imports: ts_default_tristate(
            opts.allow_synthetic_default_imports,
            d.allow_synthetic_default_imports,
        ),
        always_strict: ts_default_tristate(opts.always_strict, d.always_strict),
        base_url: opts.base_url.clone().unwrap_or_default(),
        downlevel_iteration: ts_default_tristate(opts.downlevel_iteration, d.downlevel_iteration),
        es_module_interop: ts_default_tristate(opts.es_module_interop, d.es_module_interop),
        out_file: opts.out_file.clone().unwrap_or_default(),

        // Internal fields are not modeled by `ts_options`.
        ..CompilerOptions::default()
    }
}
