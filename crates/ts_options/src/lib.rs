//! Typed compiler option parsing and normalization.

use std::collections::{BTreeMap, BTreeSet};

use ts_config::{JsonValue, ProjectConfig};
use ts_diagnostics::{Diagnostic, message_by_code};
use ts_module::{ResolutionMode, ResolutionOptions};

/// JavaScript module format used by the emitter.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ModuleKind {
    #[default]
    None,
    CommonJs,
    Amd,
    Umd,
    System,
    Es2015,
    Es2020,
    Es2022,
    EsNext,
    Node16,
    Node18,
    Node20,
    NodeNext,
    Preserve,
}

/// Algorithm used to resolve module specifiers.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ModuleResolutionKind {
    Classic,
    #[default]
    Node10,
    Node16,
    NodeNext,
    Bundler,
}

/// ECMAScript language version used for checking and emission.
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub enum ScriptTarget {
    Es3,
    #[default]
    Es5,
    Es2015,
    Es2016,
    Es2017,
    Es2018,
    Es2019,
    Es2020,
    Es2021,
    Es2022,
    Es2023,
    Es2024,
    Es2025,
    EsNext,
}

/// JSX transformation mode.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum JsxEmit {
    #[default]
    None,
    Preserve,
    React,
    ReactNative,
    ReactJsx,
    ReactJsxDev,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ModuleDetectionKind {
    Legacy,
    #[default]
    Auto,
    Force,
}

/// Line ending requested for emitted files.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum NewLineKind {
    #[default]
    Lf,
    Crlf,
}

/// Diagnostic treatment for an unused label under `allowUnusedLabels`.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum UnusedLabelReporting {
    Ignore,
    #[default]
    Suggestion,
    Error,
}

/// Normalized compiler options consumed by compiler subsystems.
#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(clippy::struct_excessive_bools)]
pub struct CompilerOptions {
    pub always_strict: bool,
    pub allow_arbitrary_extensions: bool,
    pub allow_importing_ts_extensions: bool,
    pub allow_js: bool,
    /// Whether `allowJs` was explicitly supplied instead of implied by `checkJs`.
    pub allow_js_specified: bool,
    pub allow_umd_global_access: bool,
    pub allow_unreachable_code: Option<bool>,
    pub allow_unused_labels: Option<bool>,
    pub allow_synthetic_default_imports: bool,
    pub assume_changes_only_affect_direct_dependencies: bool,
    pub check_js: bool,
    pub composite: bool,
    pub declaration: bool,
    /// Whether `declaration` was explicitly supplied instead of implied by `composite`.
    pub declaration_specified: bool,
    pub declaration_map: bool,
    pub deduplicate_packages: bool,
    pub disable_size_limit: bool,
    pub downlevel_iteration: bool,
    pub emit_declaration_only: bool,
    pub emit_bom: bool,
    pub emit_decorator_metadata: bool,
    pub erasable_syntax_only: bool,
    pub experimental_decorators: bool,
    pub es_module_interop: bool,
    pub exact_optional_property_types: bool,
    pub force_consistent_casing_in_file_names: bool,
    pub isolated_modules: bool,
    pub isolated_declarations: bool,
    pub import_helpers: bool,
    pub lib_replacement: bool,
    pub module_detection: ModuleDetectionKind,
    /// Whether `moduleDetection` was explicitly supplied instead of inferred.
    pub module_detection_specified: bool,
    pub new_line: NewLineKind,
    pub no_check: bool,
    pub no_emit: bool,
    pub no_emit_helpers: bool,
    pub no_emit_on_error: bool,
    pub no_error_truncation: bool,
    pub remove_comments: bool,
    pub rewrite_relative_import_extensions: bool,
    pub no_implicit_any: bool,
    /// Whether `noImplicitAny` was explicitly supplied rather than inherited
    /// from `strict`.
    pub no_implicit_any_specified: bool,
    pub no_implicit_override: bool,
    pub no_implicit_returns: bool,
    pub no_implicit_this: bool,
    /// Whether `noImplicitThis` was explicitly supplied rather than inherited
    /// from `strict`.
    pub no_implicit_this_specified: bool,
    pub no_lib: bool,
    pub no_fallthrough_cases_in_switch: bool,
    pub no_property_access_from_index_signature: bool,
    pub no_resolve: bool,
    pub no_unchecked_indexed_access: bool,
    pub no_unchecked_side_effect_imports: bool,
    /// Whether side-effect import checking was explicitly enabled or disabled.
    pub no_unchecked_side_effect_imports_specified: bool,
    pub no_unused_locals: bool,
    pub no_unused_parameters: bool,
    pub preserve_const_enums: bool,
    pub preserve_symlinks: bool,
    pub skip_default_lib_check: bool,
    pub skip_lib_check: bool,
    pub stable_type_ordering: bool,
    pub strip_internal: bool,
    pub strict: bool,
    /// Whether `strict` was explicitly supplied.
    pub strict_specified: bool,
    pub strict_bind_call_apply: bool,
    /// Whether `strictBindCallApply` was explicitly supplied rather than
    /// inherited from `strict`.
    pub strict_bind_call_apply_specified: bool,
    pub strict_builtin_iterator_return: bool,
    /// Whether `strictBuiltinIteratorReturn` was explicitly supplied rather
    /// than inherited from `strict`.
    pub strict_builtin_iterator_return_specified: bool,
    pub strict_function_types: bool,
    /// Whether `strictFunctionTypes` was explicitly supplied rather than
    /// inherited from `strict`.
    pub strict_function_types_specified: bool,
    pub strict_null_checks: bool,
    /// Whether `strictNullChecks` was explicitly supplied rather than inherited
    /// from `strict`.
    pub strict_null_checks_specified: bool,
    pub strict_property_initialization: bool,
    /// Whether `strictPropertyInitialization` was explicitly supplied rather
    /// than inherited from `strict`.
    pub strict_property_initialization_specified: bool,
    pub use_define_for_class_fields: Option<bool>,
    pub use_unknown_in_catch_variables: bool,
    /// Whether `useUnknownInCatchVariables` was explicitly supplied rather than
    /// inherited from `strict`.
    pub use_unknown_in_catch_variables_specified: bool,
    pub verbatim_module_syntax: bool,
    pub lib: Option<Vec<String>>,
    pub module: ModuleKind,
    /// Whether `module` was explicitly supplied rather than selected as the default.
    pub module_specified: bool,
    pub module_resolution: ModuleResolutionKind,
    pub target: ScriptTarget,
    pub jsx: JsxEmit,
    pub jsx_factory: Option<String>,
    pub jsx_fragment_factory: Option<String>,
    pub jsx_import_source: Option<String>,
    pub react_namespace: Option<String>,
    pub ignore_deprecations: Option<String>,
    pub max_node_module_js_depth: Option<i64>,
    pub custom_conditions: Option<Vec<String>>,
    pub module_suffixes: Option<Vec<String>>,
    pub resolve_json_module: bool,
    /// Whether `resolveJsonModule` was explicitly supplied instead of inferred.
    pub resolve_json_module_specified: bool,
    pub resolve_package_json_exports: bool,
    pub resolve_package_json_imports: bool,
    pub source_map: bool,
    pub inline_source_map: bool,
    pub inline_sources: bool,
    pub map_root: Option<String>,
    pub source_root: Option<String>,
    pub incremental: bool,
    /// Whether `incremental` was explicitly supplied instead of implied by `composite`.
    pub incremental_specified: bool,
    pub trace_resolution: bool,
    pub out_file: Option<String>,
    pub out_dir: Option<String>,
    pub root_dir: Option<String>,
    pub declaration_dir: Option<String>,
    pub ts_build_info_file: Option<String>,
    pub base_url: Option<String>,
    pub paths: BTreeMap<String, Vec<String>>,
    pub root_dirs: Vec<String>,
    pub type_roots: Option<Vec<String>>,
    pub types: Option<Vec<String>>,
}

impl Default for CompilerOptions {
    #[allow(clippy::too_many_lines)] // Each compiler option has an explicit upstream default.
    fn default() -> Self {
        Self {
            always_strict: true,
            allow_arbitrary_extensions: false,
            allow_importing_ts_extensions: false,
            allow_js: false,
            allow_js_specified: false,
            allow_umd_global_access: false,
            allow_unreachable_code: None,
            allow_unused_labels: None,
            allow_synthetic_default_imports: true,
            assume_changes_only_affect_direct_dependencies: false,
            check_js: false,
            composite: false,
            declaration: false,
            declaration_specified: false,
            declaration_map: false,
            deduplicate_packages: true,
            disable_size_limit: false,
            downlevel_iteration: false,
            emit_declaration_only: false,
            emit_bom: false,
            emit_decorator_metadata: false,
            erasable_syntax_only: false,
            experimental_decorators: false,
            es_module_interop: true,
            exact_optional_property_types: false,
            force_consistent_casing_in_file_names: true,
            isolated_modules: false,
            isolated_declarations: false,
            import_helpers: false,
            lib_replacement: false,
            module_detection: ModuleDetectionKind::Auto,
            module_detection_specified: false,
            new_line: NewLineKind::Lf,
            no_check: false,
            no_emit: false,
            no_emit_helpers: false,
            no_emit_on_error: false,
            no_error_truncation: false,
            remove_comments: false,
            rewrite_relative_import_extensions: false,
            no_implicit_any: true,
            no_implicit_any_specified: false,
            no_implicit_override: false,
            no_implicit_returns: false,
            no_implicit_this: true,
            no_implicit_this_specified: false,
            no_lib: false,
            no_fallthrough_cases_in_switch: false,
            no_property_access_from_index_signature: false,
            no_resolve: false,
            no_unchecked_indexed_access: false,
            no_unchecked_side_effect_imports: true,
            no_unchecked_side_effect_imports_specified: false,
            no_unused_locals: false,
            no_unused_parameters: false,
            preserve_const_enums: false,
            preserve_symlinks: false,
            skip_default_lib_check: false,
            skip_lib_check: false,
            stable_type_ordering: true,
            strip_internal: false,
            strict: true,
            strict_specified: false,
            strict_bind_call_apply: true,
            strict_bind_call_apply_specified: false,
            strict_builtin_iterator_return: true,
            strict_builtin_iterator_return_specified: false,
            strict_function_types: true,
            strict_function_types_specified: false,
            strict_null_checks: true,
            strict_null_checks_specified: false,
            strict_property_initialization: true,
            strict_property_initialization_specified: false,
            use_define_for_class_fields: None,
            use_unknown_in_catch_variables: true,
            use_unknown_in_catch_variables_specified: false,
            verbatim_module_syntax: false,
            lib: None,
            module: ModuleKind::default(),
            module_specified: false,
            module_resolution: ModuleResolutionKind::Node10,
            target: ScriptTarget::Es5,
            jsx: JsxEmit::None,
            jsx_factory: None,
            jsx_fragment_factory: None,
            jsx_import_source: None,
            react_namespace: None,
            ignore_deprecations: None,
            max_node_module_js_depth: None,
            custom_conditions: None,
            module_suffixes: None,
            resolve_json_module: false,
            resolve_json_module_specified: false,
            resolve_package_json_exports: true,
            resolve_package_json_imports: true,
            source_map: false,
            inline_source_map: false,
            inline_sources: false,
            map_root: None,
            source_root: None,
            incremental: false,
            incremental_specified: false,
            trace_resolution: false,
            out_file: None,
            out_dir: None,
            root_dir: None,
            declaration_dir: None,
            ts_build_info_file: None,
            base_url: None,
            paths: BTreeMap::new(),
            root_dirs: Vec::new(),
            type_roots: None,
            types: None,
        }
    }
}

/// Emitter-facing settings derived from normalized compiler options.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(clippy::struct_excessive_bools)]
pub struct PrinterSettings {
    pub always_strict: bool,
    pub target: ScriptTarget,
    pub module: ModuleKind,
    pub jsx: JsxEmit,
    pub emit_javascript: bool,
    pub emit_declarations: bool,
    pub source_map: bool,
    pub inline_source_map: bool,
    pub import_helpers: bool,
    pub no_emit_helpers: bool,
    pub experimental_decorators: bool,
    pub remove_comments: bool,
    pub use_define_for_class_fields: Option<bool>,
}

/// Result of parsing a `compilerOptions` JSON object.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseOptionsResult {
    pub options: CompilerOptions,
    pub diagnostics: Vec<Diagnostic>,
}

impl ParseOptionsResult {
    #[must_use]
    pub const fn is_ok(&self) -> bool {
        self.diagnostics.is_empty()
    }
}

impl CompilerOptions {
    /// Applies `strict` to strict-family options that were not explicitly set.
    pub fn normalize_strict_flags(&mut self) {
        if !self.no_implicit_any_specified {
            self.no_implicit_any = self.strict;
        }
        if !self.no_implicit_this_specified {
            self.no_implicit_this = self.strict;
        }
        if !self.strict_bind_call_apply_specified {
            self.strict_bind_call_apply = self.strict;
        }
        if !self.strict_builtin_iterator_return_specified {
            self.strict_builtin_iterator_return = self.strict;
        }
        if !self.strict_function_types_specified {
            self.strict_function_types = self.strict;
        }
        if !self.strict_null_checks_specified {
            self.strict_null_checks = self.strict;
        }
        if !self.strict_property_initialization_specified {
            self.strict_property_initialization = self.strict;
        }
        if !self.use_unknown_in_catch_variables_specified {
            self.use_unknown_in_catch_variables = self.strict;
        }
    }

    /// Returns whether a source file is exempt from semantic diagnostics.
    #[must_use]
    pub const fn skips_type_checking(
        &self,
        is_declaration_file: bool,
        is_default_library: bool,
    ) -> bool {
        self.no_check
            || (self.skip_lib_check && is_declaration_file)
            || (self.skip_default_lib_check && is_default_library)
    }

    /// Classifies unused-label diagnostics using TypeScript's three-state option.
    #[must_use]
    pub const fn unused_label_reporting(&self) -> UnusedLabelReporting {
        match self.allow_unused_labels {
            Some(true) => UnusedLabelReporting::Ignore,
            Some(false) => UnusedLabelReporting::Error,
            None => UnusedLabelReporting::Suggestion,
        }
    }

    /// Tests whether imports from this source may retain TypeScript extensions.
    #[must_use]
    pub fn allows_importing_typescript_extensions_from(&self, source_file: &str) -> bool {
        self.allow_importing_ts_extensions
            || self.rewrite_relative_import_extensions
            || ts_path::is_declaration_file(source_file)
    }

    /// Returns the automatic JSX runtime module selected by the emit mode.
    #[must_use]
    pub fn jsx_runtime_module_specifier(&self) -> Option<String> {
        self.jsx_runtime_module_specifier_for_source(None, None)
    }

    /// Returns the JSX runtime selected by compiler options and source pragmas.
    #[must_use]
    pub fn jsx_runtime_module_specifier_for_source(
        &self,
        runtime_pragma: Option<&str>,
        import_source_pragma: Option<&str>,
    ) -> Option<String> {
        if runtime_pragma == Some("classic") {
            return None;
        }
        let runtime = match self.jsx {
            JsxEmit::ReactJsxDev => "jsx-dev-runtime",
            JsxEmit::ReactJsx => "jsx-runtime",
            JsxEmit::None | JsxEmit::Preserve | JsxEmit::React | JsxEmit::ReactNative
                if runtime_pragma == Some("automatic")
                    || import_source_pragma.is_some()
                    || self
                        .jsx_import_source
                        .as_deref()
                        .is_some_and(|source| !source.is_empty()) =>
            {
                "jsx-runtime"
            }
            _ => return None,
        };
        Some(format!(
            "{}/{runtime}",
            import_source_pragma
                .filter(|source| !source.is_empty())
                .or_else(|| {
                    self.jsx_import_source
                        .as_deref()
                        .filter(|source| !source.is_empty())
                })
                .unwrap_or("react")
        ))
    }

    /// Returns the root namespace used by classic JSX factories.
    #[must_use]
    pub fn jsx_factory_namespace(&self) -> &str {
        self.jsx_factory_namespace_for_source(None, None, false)
    }

    /// Returns the classic JSX namespace after applying per-file factory pragmas.
    #[must_use]
    pub fn jsx_factory_namespace_for_source<'a>(
        &'a self,
        factory_pragma: Option<&'a str>,
        fragment_factory_pragma: Option<&'a str>,
        is_fragment: bool,
    ) -> &'a str {
        let fragment_factory = is_fragment
            .then(|| {
                fragment_factory_pragma
                    .filter(|factory| is_jsx_entity_name(factory, true))
                    .or_else(|| {
                        self.jsx_fragment_factory
                            .as_deref()
                            .filter(|factory| is_jsx_entity_name(factory, true))
                    })
            })
            .flatten();
        fragment_factory
            .or_else(|| (!is_fragment).then_some(factory_pragma).flatten())
            .or(self.jsx_factory.as_deref())
            .and_then(|factory| factory.split('.').next())
            .filter(|namespace| !namespace.is_empty())
            .or(self.react_namespace.as_deref())
            .unwrap_or("React")
    }

    #[allow(clippy::too_many_lines)]
    pub fn apply_overrides(&mut self, overrides: &Self, names: &BTreeSet<String>) {
        for name in names {
            match name.as_str() {
                "alwaysstrict" => self.always_strict = overrides.always_strict,
                "allowarbitraryextensions" => {
                    self.allow_arbitrary_extensions = overrides.allow_arbitrary_extensions;
                }
                "allowimportingtsextensions" => {
                    self.allow_importing_ts_extensions = overrides.allow_importing_ts_extensions;
                }
                "allowjs" => {
                    self.allow_js = overrides.allow_js;
                    self.allow_js_specified = true;
                }
                "allowumdglobalaccess" => {
                    self.allow_umd_global_access = overrides.allow_umd_global_access;
                }
                "allowunreachablecode" => {
                    self.allow_unreachable_code = overrides.allow_unreachable_code;
                }
                "allowunusedlabels" => self.allow_unused_labels = overrides.allow_unused_labels,
                "allowsyntheticdefaultimports" => {
                    self.allow_synthetic_default_imports =
                        overrides.allow_synthetic_default_imports;
                }
                "assumechangesonlyaffectdirectdependencies" => {
                    self.assume_changes_only_affect_direct_dependencies =
                        overrides.assume_changes_only_affect_direct_dependencies;
                }
                "baseurl" => self.base_url.clone_from(&overrides.base_url),
                "checkjs" => {
                    self.check_js = overrides.check_js;
                    if !names.contains("allowjs") && !self.allow_js_specified {
                        self.allow_js = overrides.allow_js;
                    }
                }
                "composite" => {
                    self.composite = overrides.composite;
                    if !names.contains("declaration") && !self.declaration_specified {
                        self.declaration = overrides.declaration;
                    }
                    if !names.contains("incremental") && !self.incremental_specified {
                        self.incremental = overrides.incremental;
                    }
                }
                "customconditions" => {
                    self.custom_conditions
                        .clone_from(&overrides.custom_conditions);
                }
                "declaration" => {
                    self.declaration = overrides.declaration;
                    self.declaration_specified = true;
                }
                "declarationdir" => self.declaration_dir.clone_from(&overrides.declaration_dir),
                "declarationmap" => self.declaration_map = overrides.declaration_map,
                "deduplicatepackages" => self.deduplicate_packages = overrides.deduplicate_packages,
                "disablesizelimit" => self.disable_size_limit = overrides.disable_size_limit,
                "downleveliteration" => {
                    self.downlevel_iteration = overrides.downlevel_iteration;
                }
                "emitdeclarationonly" => {
                    self.emit_declaration_only = overrides.emit_declaration_only;
                }
                "esmoduleinterop" => {
                    self.es_module_interop = overrides.es_module_interop;
                    if !names.contains("allowsyntheticdefaultimports") {
                        self.allow_synthetic_default_imports =
                            overrides.allow_synthetic_default_imports;
                    }
                }
                "exactoptionalpropertytypes" => {
                    self.exact_optional_property_types = overrides.exact_optional_property_types;
                }
                "forceconsistentcasinginfilenames" => {
                    self.force_consistent_casing_in_file_names =
                        overrides.force_consistent_casing_in_file_names;
                }
                "isolatedmodules" => self.isolated_modules = overrides.isolated_modules,
                "isolateddeclarations" => {
                    self.isolated_declarations = overrides.isolated_declarations;
                }
                "emitdecoratormetadata" => {
                    self.emit_decorator_metadata = overrides.emit_decorator_metadata;
                }
                "experimentaldecorators" => {
                    self.experimental_decorators = overrides.experimental_decorators;
                }
                "emitbom" => self.emit_bom = overrides.emit_bom,
                "erasablesyntaxonly" => self.erasable_syntax_only = overrides.erasable_syntax_only,
                "ignoredeprecations" => {
                    self.ignore_deprecations
                        .clone_from(&overrides.ignore_deprecations);
                }
                "importhelpers" => self.import_helpers = overrides.import_helpers,
                "incremental" => {
                    self.incremental = overrides.incremental;
                    self.incremental_specified = true;
                }
                "jsx" => self.jsx = overrides.jsx,
                "jsxfactory" => self.jsx_factory.clone_from(&overrides.jsx_factory),
                "jsxfragmentfactory" => self
                    .jsx_fragment_factory
                    .clone_from(&overrides.jsx_fragment_factory),
                "jsximportsource" => self
                    .jsx_import_source
                    .clone_from(&overrides.jsx_import_source),
                "lib" => self.lib.clone_from(&overrides.lib),
                "libreplacement" => self.lib_replacement = overrides.lib_replacement,
                "maxnodemodulejsdepth" => {
                    self.max_node_module_js_depth = overrides.max_node_module_js_depth;
                }
                "reactnamespace" => self.react_namespace.clone_from(&overrides.react_namespace),
                "module" => {
                    self.module = overrides.module;
                    self.module_specified = true;
                    if !names.contains("moduleresolution") {
                        self.module_resolution = overrides.module_resolution;
                    }
                    if !names.contains("moduledetection") && !self.module_detection_specified {
                        self.module_detection = overrides.module_detection;
                    }
                    if !names.contains("resolvejsonmodule") && !self.resolve_json_module_specified {
                        self.resolve_json_module = overrides.resolve_json_module;
                    }
                }
                "moduledetection" => {
                    self.module_detection = overrides.module_detection;
                    self.module_detection_specified = true;
                }
                "moduleresolution" => {
                    self.module_resolution = overrides.module_resolution;
                    if !names.contains("resolvejsonmodule") && !self.resolve_json_module_specified {
                        self.resolve_json_module = overrides.resolve_json_module;
                    }
                }
                "modulesuffixes" => self.module_suffixes.clone_from(&overrides.module_suffixes),
                "newline" => self.new_line = overrides.new_line,
                "nocheck" => self.no_check = overrides.no_check,
                "noemit" => self.no_emit = overrides.no_emit,
                "noemithelpers" => self.no_emit_helpers = overrides.no_emit_helpers,
                "noemitonerror" => self.no_emit_on_error = overrides.no_emit_on_error,
                "noerrortruncation" => self.no_error_truncation = overrides.no_error_truncation,
                "removecomments" => self.remove_comments = overrides.remove_comments,
                "rewriterelativeimportextensions" => {
                    self.rewrite_relative_import_extensions =
                        overrides.rewrite_relative_import_extensions;
                }
                "noimplicitany" => {
                    self.no_implicit_any = overrides.no_implicit_any;
                    self.no_implicit_any_specified = true;
                }
                "noimplicitoverride" => self.no_implicit_override = overrides.no_implicit_override,
                "noimplicitreturns" => self.no_implicit_returns = overrides.no_implicit_returns,
                "noimplicitthis" => {
                    self.no_implicit_this = overrides.no_implicit_this;
                    self.no_implicit_this_specified = true;
                }
                "nolib" => self.no_lib = overrides.no_lib,
                "nofallthroughcasesinswitch" => {
                    self.no_fallthrough_cases_in_switch = overrides.no_fallthrough_cases_in_switch;
                }
                "nopropertyaccessfromindexsignature" => {
                    self.no_property_access_from_index_signature =
                        overrides.no_property_access_from_index_signature;
                }
                "noresolve" => self.no_resolve = overrides.no_resolve,
                "nouncheckedindexedaccess" => {
                    self.no_unchecked_indexed_access = overrides.no_unchecked_indexed_access;
                }
                "nouncheckedsideeffectimports" => {
                    self.no_unchecked_side_effect_imports =
                        overrides.no_unchecked_side_effect_imports;
                    self.no_unchecked_side_effect_imports_specified = true;
                }
                "nounusedlocals" => self.no_unused_locals = overrides.no_unused_locals,
                "nounusedparameters" => self.no_unused_parameters = overrides.no_unused_parameters,
                "outfile" => self.out_file.clone_from(&overrides.out_file),
                "outdir" => self.out_dir.clone_from(&overrides.out_dir),
                "paths" => self.paths.clone_from(&overrides.paths),
                "preserveconstenums" => {
                    self.preserve_const_enums = overrides.preserve_const_enums;
                }
                "preservesymlinks" => self.preserve_symlinks = overrides.preserve_symlinks,
                "resolvejsonmodule" => {
                    self.resolve_json_module = overrides.resolve_json_module;
                    self.resolve_json_module_specified = true;
                }
                "resolvepackagejsonexports" => {
                    self.resolve_package_json_exports = overrides.resolve_package_json_exports;
                }
                "resolvepackagejsonimports" => {
                    self.resolve_package_json_imports = overrides.resolve_package_json_imports;
                }
                "rootdir" => self.root_dir.clone_from(&overrides.root_dir),
                "rootdirs" => self.root_dirs.clone_from(&overrides.root_dirs),
                "skipdefaultlibcheck" => {
                    self.skip_default_lib_check = overrides.skip_default_lib_check;
                }
                "skiplibcheck" => self.skip_lib_check = overrides.skip_lib_check,
                "stabletypeordering" => self.stable_type_ordering = overrides.stable_type_ordering,
                "stripinternal" => self.strip_internal = overrides.strip_internal,
                "sourcemap" => self.source_map = overrides.source_map,
                "inlinesourcemap" => self.inline_source_map = overrides.inline_source_map,
                "inlinesources" => self.inline_sources = overrides.inline_sources,
                "maproot" => self.map_root.clone_from(&overrides.map_root),
                "sourceroot" => self.source_root.clone_from(&overrides.source_root),
                "strict" => {
                    self.strict = overrides.strict;
                    self.strict_specified = true;
                    if !names.contains("strictbindcallapply")
                        && !self.strict_bind_call_apply_specified
                    {
                        self.strict_bind_call_apply = overrides.strict_bind_call_apply;
                    }
                    if !names.contains("strictbuiltiniteratorreturn")
                        && !self.strict_builtin_iterator_return_specified
                    {
                        self.strict_builtin_iterator_return =
                            overrides.strict_builtin_iterator_return;
                    }
                    if !names.contains("strictfunctiontypes")
                        && !self.strict_function_types_specified
                    {
                        self.strict_function_types = overrides.strict_function_types;
                    }
                    if !names.contains("noimplicitany") && !self.no_implicit_any_specified {
                        self.no_implicit_any = overrides.no_implicit_any;
                    }
                    if !names.contains("noimplicitthis") && !self.no_implicit_this_specified {
                        self.no_implicit_this = overrides.no_implicit_this;
                    }
                    if !names.contains("strictnullchecks") && !self.strict_null_checks_specified {
                        self.strict_null_checks = overrides.strict_null_checks;
                    }
                    if !names.contains("strictpropertyinitialization")
                        && !self.strict_property_initialization_specified
                    {
                        self.strict_property_initialization =
                            overrides.strict_property_initialization;
                    }
                    if !names.contains("useunknownincatchvariables")
                        && !self.use_unknown_in_catch_variables_specified
                    {
                        self.use_unknown_in_catch_variables =
                            overrides.use_unknown_in_catch_variables;
                    }
                }
                "strictbindcallapply" => {
                    self.strict_bind_call_apply = overrides.strict_bind_call_apply;
                    self.strict_bind_call_apply_specified = true;
                }
                "strictbuiltiniteratorreturn" => {
                    self.strict_builtin_iterator_return = overrides.strict_builtin_iterator_return;
                    self.strict_builtin_iterator_return_specified = true;
                }
                "strictfunctiontypes" => {
                    self.strict_function_types = overrides.strict_function_types;
                    self.strict_function_types_specified = true;
                }
                "strictnullchecks" => {
                    self.strict_null_checks = overrides.strict_null_checks;
                    self.strict_null_checks_specified = true;
                }
                "strictpropertyinitialization" => {
                    self.strict_property_initialization = overrides.strict_property_initialization;
                    self.strict_property_initialization_specified = true;
                }
                "tsbuildinfofile" => {
                    self.ts_build_info_file
                        .clone_from(&overrides.ts_build_info_file);
                }
                "traceresolution" => self.trace_resolution = overrides.trace_resolution,
                "typeroots" => self.type_roots.clone_from(&overrides.type_roots),
                "types" => self.types.clone_from(&overrides.types),
                "target" => self.target = overrides.target,
                "usedefineforclassfields" => {
                    self.use_define_for_class_fields = overrides.use_define_for_class_fields;
                }
                "useunknownincatchvariables" => {
                    self.use_unknown_in_catch_variables = overrides.use_unknown_in_catch_variables;
                    self.use_unknown_in_catch_variables_specified = true;
                }
                "verbatimmodulesyntax" => {
                    self.verbatim_module_syntax = overrides.verbatim_module_syntax;
                }
                _ => {}
            }
        }
    }

    /// Converts these options to the module resolver's settings.
    #[must_use]
    pub fn module_resolution_options(&self) -> ResolutionOptions {
        ResolutionOptions {
            mode: match self.module_resolution {
                ModuleResolutionKind::Classic => ResolutionMode::Classic,
                ModuleResolutionKind::Node10 => ResolutionMode::Node10,
                ModuleResolutionKind::Node16 => ResolutionMode::Node16,
                ModuleResolutionKind::NodeNext => ResolutionMode::NodeNext,
                ModuleResolutionKind::Bundler => ResolutionMode::Bundler,
            },
            allow_arbitrary_extensions: self.allow_arbitrary_extensions,
            allow_javascript: self.allow_js,
            resolve_json: self.resolve_json_module,
            resolve_package_json_exports: self.resolve_package_json_exports,
            resolve_package_json_imports: self.resolve_package_json_imports,
            prefer_types: true,
            custom_conditions: self.custom_conditions.clone().unwrap_or_default(),
            module_suffixes: self.module_suffixes.clone().unwrap_or_default(),
            base_url: self.base_url.clone(),
            paths: self.paths.clone(),
            root_dirs: self.root_dirs.clone(),
            type_roots: self.type_roots.clone(),
            types: self.types.clone(),
        }
    }

    /// Converts these options to settings used when invoking the printer.
    #[must_use]
    pub const fn printer_settings(&self) -> PrinterSettings {
        PrinterSettings {
            always_strict: self.always_strict,
            target: self.target,
            module: self.module,
            jsx: self.jsx,
            emit_javascript: !self.no_emit && !self.emit_declaration_only,
            emit_declarations: !self.no_emit && (self.declaration || self.composite),
            source_map: (self.source_map || self.inline_source_map)
                && !self.no_emit
                && !self.emit_declaration_only,
            inline_source_map: self.inline_source_map,
            import_helpers: self.import_helpers,
            no_emit_helpers: self.no_emit_helpers,
            experimental_decorators: self.experimental_decorators,
            remove_comments: self.remove_comments,
            use_define_for_class_fields: self.use_define_for_class_fields,
        }
    }
}

/// Parses and normalizes the `compilerOptions` object from a config value.
#[must_use]
pub fn parse_compiler_options(value: &JsonValue) -> ParseOptionsResult {
    let Some(object) = value.as_object() else {
        return ParseOptionsResult {
            options: CompilerOptions::default(),
            diagnostics: vec![diagnostic(5024, ["compilerOptions", "object"])],
        };
    };
    parse_compiler_options_map(object)
}

/// Parses the compiler options retained by a project configuration.
#[must_use]
pub fn parse_project_options(config: &ProjectConfig) -> ParseOptionsResult {
    let mut result = parse_compiler_options_map(&config.compiler_options);
    if config
        .path
        .rsplit('/')
        .next()
        .is_some_and(|name| name.eq_ignore_ascii_case("jsconfig.json"))
    {
        apply_javascript_project_defaults(&mut result.options, &config.compiler_options);
    }
    let directory = config.path.rsplit_once('/').map_or(".", |(path, _)| path);
    if let Some(base_url) = &mut result.options.base_url
        && !ts_path::is_absolute(base_url)
    {
        *base_url = ts_path::resolve_path(directory, &[base_url]);
    }
    if let Some(map_root) = &mut result.options.map_root
        && !ts_path::is_absolute(map_root)
    {
        *map_root = ts_path::resolve_path(directory, &[map_root]);
    }
    for root_dir in &mut result.options.root_dirs {
        if !ts_path::is_absolute(root_dir) {
            *root_dir = ts_path::resolve_path(directory, &[root_dir]);
        }
    }
    if let Some(type_roots) = &mut result.options.type_roots {
        for type_root in type_roots {
            if !ts_path::is_absolute(type_root) {
                *type_root = ts_path::resolve_path(directory, &[type_root]);
            }
        }
    }
    for path in [
        &mut result.options.out_file,
        &mut result.options.out_dir,
        &mut result.options.root_dir,
        &mut result.options.declaration_dir,
        &mut result.options.ts_build_info_file,
    ] {
        if let Some(path) = path
            && !ts_path::is_absolute(path)
        {
            *path = ts_path::resolve_path(directory, &[path]);
        }
    }
    result
}

fn apply_javascript_project_defaults(
    options: &mut CompilerOptions,
    configured: &BTreeMap<String, JsonValue>,
) {
    let is_specified = |name: &str| {
        configured
            .iter()
            .any(|(key, value)| key.eq_ignore_ascii_case(name) && !matches!(value, JsonValue::Null))
    };
    if !is_specified("allowJs") {
        options.allow_js = true;
    }
    if !is_specified("maxNodeModuleJsDepth") {
        options.max_node_module_js_depth = Some(2);
    }
    if !is_specified("skipLibCheck") {
        options.skip_lib_check = true;
    }
    if !is_specified("noEmit") {
        options.no_emit = true;
    }
}

/// Parses and normalizes a map of compiler option values.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn parse_compiler_options_map(options: &BTreeMap<String, JsonValue>) -> ParseOptionsResult {
    let mut parsed = PartialOptions::default();
    let mut diagnostics = Vec::new();
    for (original_name, value) in options {
        let name = original_name.to_ascii_lowercase();
        match name.as_str() {
            "alwaysstrict" => {
                parsed.always_strict = boolean(original_name, value, &mut diagnostics);
            }
            "allowarbitraryextensions" => {
                parsed.allow_arbitrary_extensions = boolean(original_name, value, &mut diagnostics);
            }
            "allowimportingtsextensions" => {
                parsed.allow_importing_ts_extensions =
                    boolean(original_name, value, &mut diagnostics);
            }
            "allowjs" => parsed.allow_js = boolean(original_name, value, &mut diagnostics),
            "allowumdglobalaccess" => {
                parsed.allow_umd_global_access = boolean(original_name, value, &mut diagnostics);
            }
            "allowunreachablecode" => {
                parsed.allow_unreachable_code = boolean(original_name, value, &mut diagnostics);
            }
            "allowunusedlabels" => {
                parsed.allow_unused_labels = boolean(original_name, value, &mut diagnostics);
            }
            "allowsyntheticdefaultimports" => {
                parsed.allow_synthetic_default_imports =
                    boolean(original_name, value, &mut diagnostics);
            }
            "assumechangesonlyaffectdirectdependencies" => {
                parsed.assume_changes_only_affect_direct_dependencies =
                    boolean(original_name, value, &mut diagnostics);
            }
            "checkjs" => parsed.check_js = boolean(original_name, value, &mut diagnostics),
            "composite" => parsed.composite = boolean(original_name, value, &mut diagnostics),
            "customconditions" => {
                parsed.custom_conditions = string_array(original_name, value, &mut diagnostics);
            }
            "declaration" => {
                parsed.declaration = boolean(original_name, value, &mut diagnostics);
            }
            "declarationmap" => {
                parsed.declaration_map = boolean(original_name, value, &mut diagnostics);
            }
            "deduplicatepackages" => {
                parsed.deduplicate_packages = boolean(original_name, value, &mut diagnostics);
            }
            "disablesizelimit" => {
                parsed.disable_size_limit = boolean(original_name, value, &mut diagnostics);
            }
            "downleveliteration" => {
                parsed.downlevel_iteration = boolean(original_name, value, &mut diagnostics);
            }
            "emitdeclarationonly" => {
                parsed.emit_declaration_only = boolean(original_name, value, &mut diagnostics);
            }
            "emitbom" => {
                parsed.emit_bom = boolean(original_name, value, &mut diagnostics);
            }
            "emitdecoratormetadata" => {
                parsed.emit_decorator_metadata = boolean(original_name, value, &mut diagnostics);
            }
            "erasablesyntaxonly" => {
                parsed.erasable_syntax_only = boolean(original_name, value, &mut diagnostics);
            }
            "experimentaldecorators" => {
                parsed.experimental_decorators = boolean(original_name, value, &mut diagnostics);
            }
            "esmoduleinterop" => {
                parsed.es_module_interop = boolean(original_name, value, &mut diagnostics);
            }
            "exactoptionalpropertytypes" => {
                parsed.exact_optional_property_types =
                    boolean(original_name, value, &mut diagnostics);
            }
            "forceconsistentcasinginfilenames" => {
                parsed.force_consistent_casing_in_file_names =
                    boolean(original_name, value, &mut diagnostics);
            }
            "isolatedmodules" => {
                parsed.isolated_modules = boolean(original_name, value, &mut diagnostics);
            }
            "isolateddeclarations" => {
                parsed.isolated_declarations = boolean(original_name, value, &mut diagnostics);
            }
            "importhelpers" => {
                parsed.import_helpers = boolean(original_name, value, &mut diagnostics);
            }
            "ignoredeprecations" => {
                parsed.ignore_deprecations = string(original_name, value, &mut diagnostics);
            }
            "libreplacement" => {
                parsed.lib_replacement = boolean(original_name, value, &mut diagnostics);
            }
            "maxnodemodulejsdepth" => {
                parsed.max_node_module_js_depth = number(original_name, value, &mut diagnostics);
            }
            "moduledetection" => {
                parsed.module_detection =
                    enum_value(original_name, value, &mut diagnostics, module_detection);
            }
            "modulesuffixes" => {
                parsed.module_suffixes = string_array(original_name, value, &mut diagnostics);
            }
            "newline" => {
                parsed.new_line = enum_value(original_name, value, &mut diagnostics, new_line);
            }
            "nocheck" => parsed.no_check = boolean(original_name, value, &mut diagnostics),
            "noemit" => parsed.no_emit = boolean(original_name, value, &mut diagnostics),
            "noemithelpers" => {
                parsed.no_emit_helpers = boolean(original_name, value, &mut diagnostics);
            }
            "noemitonerror" => {
                parsed.no_emit_on_error = boolean(original_name, value, &mut diagnostics);
            }
            "noerrortruncation" => {
                parsed.no_error_truncation = boolean(original_name, value, &mut diagnostics);
            }
            "removecomments" => {
                parsed.remove_comments = boolean(original_name, value, &mut diagnostics);
            }
            "rewriterelativeimportextensions" => {
                parsed.rewrite_relative_import_extensions =
                    boolean(original_name, value, &mut diagnostics);
            }
            "noimplicitany" => {
                parsed.no_implicit_any = boolean(original_name, value, &mut diagnostics);
            }
            "noimplicitoverride" => {
                parsed.no_implicit_override = boolean(original_name, value, &mut diagnostics);
            }
            "noimplicitreturns" => {
                parsed.no_implicit_returns = boolean(original_name, value, &mut diagnostics);
            }
            "noimplicitthis" => {
                parsed.no_implicit_this = boolean(original_name, value, &mut diagnostics);
            }
            "nolib" => parsed.no_lib = boolean(original_name, value, &mut diagnostics),
            "nofallthroughcasesinswitch" => {
                parsed.no_fallthrough_cases_in_switch =
                    boolean(original_name, value, &mut diagnostics);
            }
            "nopropertyaccessfromindexsignature" => {
                parsed.no_property_access_from_index_signature =
                    boolean(original_name, value, &mut diagnostics);
            }
            "noresolve" => parsed.no_resolve = boolean(original_name, value, &mut diagnostics),
            "nouncheckedindexedaccess" => {
                parsed.no_unchecked_indexed_access =
                    boolean(original_name, value, &mut diagnostics);
            }
            "nouncheckedsideeffectimports" => {
                parsed.no_unchecked_side_effect_imports =
                    boolean(original_name, value, &mut diagnostics);
            }
            "nounusedlocals" => {
                parsed.no_unused_locals = boolean(original_name, value, &mut diagnostics);
            }
            "nounusedparameters" => {
                parsed.no_unused_parameters = boolean(original_name, value, &mut diagnostics);
            }
            "preserveconstenums" => {
                parsed.preserve_const_enums = boolean(original_name, value, &mut diagnostics);
            }
            "preservesymlinks" => {
                parsed.preserve_symlinks = boolean(original_name, value, &mut diagnostics);
            }
            "plugins" => validate_plugins(original_name, value, &mut diagnostics),
            "skipdefaultlibcheck" => {
                parsed.skip_default_lib_check = boolean(original_name, value, &mut diagnostics);
            }
            "skiplibcheck" => {
                parsed.skip_lib_check = boolean(original_name, value, &mut diagnostics);
            }
            "stabletypeordering" => {
                parsed.stable_type_ordering = boolean(original_name, value, &mut diagnostics);
            }
            "stripinternal" => {
                parsed.strip_internal = boolean(original_name, value, &mut diagnostics);
            }
            "strict" => parsed.strict = boolean(original_name, value, &mut diagnostics),
            "strictbindcallapply" => {
                parsed.strict_bind_call_apply = boolean(original_name, value, &mut diagnostics);
            }
            "strictbuiltiniteratorreturn" => {
                parsed.strict_builtin_iterator_return =
                    boolean(original_name, value, &mut diagnostics);
            }
            "strictfunctiontypes" => {
                parsed.strict_function_types = boolean(original_name, value, &mut diagnostics);
            }
            "strictnullchecks" => {
                parsed.strict_null_checks = boolean(original_name, value, &mut diagnostics);
            }
            "strictpropertyinitialization" => {
                parsed.strict_property_initialization =
                    boolean(original_name, value, &mut diagnostics);
            }
            "usedefineforclassfields" => {
                parsed.use_define_for_class_fields =
                    boolean(original_name, value, &mut diagnostics);
            }
            "verbatimmodulesyntax" => {
                parsed.verbatim_module_syntax = boolean(original_name, value, &mut diagnostics);
            }
            "useunknownincatchvariables" => {
                parsed.use_unknown_in_catch_variables =
                    boolean(original_name, value, &mut diagnostics);
            }
            "lib" => parsed.lib = string_array(original_name, value, &mut diagnostics),
            "resolvejsonmodule" => {
                parsed.resolve_json_module = boolean(original_name, value, &mut diagnostics);
            }
            "resolvepackagejsonexports" => {
                parsed.resolve_package_json_exports =
                    boolean(original_name, value, &mut diagnostics);
            }
            "resolvepackagejsonimports" => {
                parsed.resolve_package_json_imports =
                    boolean(original_name, value, &mut diagnostics);
            }
            "sourcemap" => parsed.source_map = boolean(original_name, value, &mut diagnostics),
            "inlinesourcemap" => {
                parsed.inline_source_map = boolean(original_name, value, &mut diagnostics);
            }
            "inlinesources" => {
                parsed.inline_sources = boolean(original_name, value, &mut diagnostics);
            }
            "maproot" => parsed.map_root = string(original_name, value, &mut diagnostics),
            "sourceroot" => parsed.source_root = string(original_name, value, &mut diagnostics),
            "incremental" => parsed.incremental = boolean(original_name, value, &mut diagnostics),
            "outfile" => parsed.out_file = string(original_name, value, &mut diagnostics),
            "outdir" => parsed.out_dir = string(original_name, value, &mut diagnostics),
            "rootdir" => parsed.root_dir = string(original_name, value, &mut diagnostics),
            "declarationdir" => {
                parsed.declaration_dir = string(original_name, value, &mut diagnostics);
            }
            "tsbuildinfofile" => {
                parsed.ts_build_info_file = string(original_name, value, &mut diagnostics);
            }
            "traceresolution" => {
                parsed.trace_resolution = boolean(original_name, value, &mut diagnostics);
            }
            "baseurl" => parsed.base_url = string(original_name, value, &mut diagnostics),
            "paths" => parsed.paths = paths(original_name, value, &mut diagnostics),
            "rootdirs" => parsed.root_dirs = string_array(original_name, value, &mut diagnostics),
            "typeroots" => {
                parsed.type_roots = string_array(original_name, value, &mut diagnostics);
            }
            "types" => parsed.types = string_array(original_name, value, &mut diagnostics),
            "module" => parsed.module = enum_value(original_name, value, &mut diagnostics, module),
            "moduleresolution" => {
                parsed.module_resolution =
                    enum_value(original_name, value, &mut diagnostics, module_resolution);
            }
            "target" => parsed.target = enum_value(original_name, value, &mut diagnostics, target),
            "jsx" => parsed.jsx = enum_value(original_name, value, &mut diagnostics, jsx),
            "jsxfactory" => parsed.jsx_factory = string(original_name, value, &mut diagnostics),
            "jsxfragmentfactory" => {
                parsed.jsx_fragment_factory = string(original_name, value, &mut diagnostics);
            }
            "jsximportsource" => {
                parsed.jsx_import_source = string(original_name, value, &mut diagnostics);
            }
            "reactnamespace" => {
                parsed.react_namespace = string(original_name, value, &mut diagnostics);
            }
            _ => diagnostics.push(diagnostic(5023, [original_name.as_str()])),
        }
    }
    validate_options(&parsed, &mut diagnostics);
    ParseOptionsResult {
        options: parsed.normalize(),
        diagnostics,
    }
}

#[derive(Default)]
struct PartialOptions {
    always_strict: Option<bool>,
    allow_arbitrary_extensions: Option<bool>,
    allow_importing_ts_extensions: Option<bool>,
    allow_js: Option<bool>,
    allow_umd_global_access: Option<bool>,
    allow_unreachable_code: Option<bool>,
    allow_unused_labels: Option<bool>,
    allow_synthetic_default_imports: Option<bool>,
    assume_changes_only_affect_direct_dependencies: Option<bool>,
    check_js: Option<bool>,
    composite: Option<bool>,
    custom_conditions: Option<Vec<String>>,
    declaration: Option<bool>,
    declaration_map: Option<bool>,
    deduplicate_packages: Option<bool>,
    disable_size_limit: Option<bool>,
    downlevel_iteration: Option<bool>,
    emit_declaration_only: Option<bool>,
    emit_bom: Option<bool>,
    emit_decorator_metadata: Option<bool>,
    erasable_syntax_only: Option<bool>,
    experimental_decorators: Option<bool>,
    es_module_interop: Option<bool>,
    exact_optional_property_types: Option<bool>,
    force_consistent_casing_in_file_names: Option<bool>,
    isolated_modules: Option<bool>,
    isolated_declarations: Option<bool>,
    ignore_deprecations: Option<String>,
    import_helpers: Option<bool>,
    lib_replacement: Option<bool>,
    max_node_module_js_depth: Option<i64>,
    module_detection: Option<ModuleDetectionKind>,
    module_suffixes: Option<Vec<String>>,
    new_line: Option<NewLineKind>,
    no_check: Option<bool>,
    no_emit: Option<bool>,
    no_emit_helpers: Option<bool>,
    no_emit_on_error: Option<bool>,
    no_error_truncation: Option<bool>,
    remove_comments: Option<bool>,
    rewrite_relative_import_extensions: Option<bool>,
    no_implicit_any: Option<bool>,
    no_implicit_override: Option<bool>,
    no_implicit_returns: Option<bool>,
    no_implicit_this: Option<bool>,
    no_lib: Option<bool>,
    no_fallthrough_cases_in_switch: Option<bool>,
    no_property_access_from_index_signature: Option<bool>,
    no_resolve: Option<bool>,
    no_unchecked_indexed_access: Option<bool>,
    no_unchecked_side_effect_imports: Option<bool>,
    no_unused_locals: Option<bool>,
    no_unused_parameters: Option<bool>,
    preserve_const_enums: Option<bool>,
    preserve_symlinks: Option<bool>,
    skip_default_lib_check: Option<bool>,
    skip_lib_check: Option<bool>,
    stable_type_ordering: Option<bool>,
    strip_internal: Option<bool>,
    strict: Option<bool>,
    strict_bind_call_apply: Option<bool>,
    strict_builtin_iterator_return: Option<bool>,
    strict_function_types: Option<bool>,
    strict_null_checks: Option<bool>,
    strict_property_initialization: Option<bool>,
    use_define_for_class_fields: Option<bool>,
    use_unknown_in_catch_variables: Option<bool>,
    verbatim_module_syntax: Option<bool>,
    lib: Option<Vec<String>>,
    module: Option<ModuleKind>,
    module_resolution: Option<ModuleResolutionKind>,
    target: Option<ScriptTarget>,
    jsx: Option<JsxEmit>,
    jsx_factory: Option<String>,
    jsx_fragment_factory: Option<String>,
    jsx_import_source: Option<String>,
    react_namespace: Option<String>,
    resolve_json_module: Option<bool>,
    resolve_package_json_exports: Option<bool>,
    resolve_package_json_imports: Option<bool>,
    source_map: Option<bool>,
    inline_source_map: Option<bool>,
    inline_sources: Option<bool>,
    map_root: Option<String>,
    source_root: Option<String>,
    incremental: Option<bool>,
    trace_resolution: Option<bool>,
    out_file: Option<String>,
    out_dir: Option<String>,
    root_dir: Option<String>,
    declaration_dir: Option<String>,
    ts_build_info_file: Option<String>,
    base_url: Option<String>,
    paths: Option<BTreeMap<String, Vec<String>>>,
    root_dirs: Option<Vec<String>>,
    type_roots: Option<Vec<String>>,
    types: Option<Vec<String>>,
}

impl PartialOptions {
    #[allow(clippy::too_many_lines)] // Flat field-by-field option mapping.
    fn normalize(self) -> CompilerOptions {
        let check_js = self.check_js.unwrap_or(false);
        let allow_js_specified = self.allow_js.is_some();
        let declaration_specified = self.declaration.is_some();
        let incremental_specified = self.incremental.is_some();
        let no_unchecked_side_effect_imports_specified =
            self.no_unchecked_side_effect_imports.is_some();
        let no_implicit_any_specified = self.no_implicit_any.is_some();
        let no_implicit_this_specified = self.no_implicit_this.is_some();
        let strict_specified = self.strict.is_some();
        let strict_bind_call_apply_specified = self.strict_bind_call_apply.is_some();
        let strict_builtin_iterator_return_specified =
            self.strict_builtin_iterator_return.is_some();
        let strict_function_types_specified = self.strict_function_types.is_some();
        let strict_null_checks_specified = self.strict_null_checks.is_some();
        let strict_property_initialization_specified =
            self.strict_property_initialization.is_some();
        let use_unknown_in_catch_variables_specified =
            self.use_unknown_in_catch_variables.is_some();
        // The current TypeScript/ts-go command-line contract enables the strict
        // family unless `strict` is explicitly disabled. Individual strict
        // options remain independently overridable.
        let strict = self.strict.unwrap_or(true);
        let emit_declaration_only = self.emit_declaration_only.unwrap_or(false);
        let composite = self.composite.unwrap_or(false);
        let module_specified = self.module.is_some();
        let module_detection_specified = self.module_detection.is_some();
        let resolve_json_module_specified = self.resolve_json_module.is_some();
        let module = self.module.unwrap_or(if self.out_file.is_some() {
            ModuleKind::None
        } else {
            ModuleKind::default()
        });
        let module_resolution = self
            .module_resolution
            .unwrap_or_else(|| default_module_resolution(module));
        let es_module_interop = self.es_module_interop.unwrap_or(true);
        CompilerOptions {
            always_strict: self.always_strict.unwrap_or(true),
            allow_arbitrary_extensions: self.allow_arbitrary_extensions.unwrap_or(false),
            allow_importing_ts_extensions: self.allow_importing_ts_extensions.unwrap_or(false),
            allow_js: self.allow_js.unwrap_or(check_js),
            allow_js_specified,
            allow_umd_global_access: self.allow_umd_global_access.unwrap_or(false),
            allow_unreachable_code: self.allow_unreachable_code,
            allow_unused_labels: self.allow_unused_labels,
            allow_synthetic_default_imports: self.allow_synthetic_default_imports.unwrap_or(
                es_module_interop
                    || module == ModuleKind::System
                    || module_resolution == ModuleResolutionKind::Bundler,
            ),
            assume_changes_only_affect_direct_dependencies: self
                .assume_changes_only_affect_direct_dependencies
                .unwrap_or(false),
            check_js,
            composite,
            declaration: self.declaration.unwrap_or(composite),
            declaration_specified,
            declaration_map: self.declaration_map.unwrap_or(false),
            deduplicate_packages: self.deduplicate_packages.unwrap_or(true),
            disable_size_limit: self.disable_size_limit.unwrap_or(false),
            downlevel_iteration: self.downlevel_iteration.unwrap_or(false),
            emit_declaration_only,
            emit_bom: self.emit_bom.unwrap_or(false),
            emit_decorator_metadata: self.emit_decorator_metadata.unwrap_or(false),
            erasable_syntax_only: self.erasable_syntax_only.unwrap_or(false),
            experimental_decorators: self.experimental_decorators.unwrap_or(false),
            es_module_interop,
            exact_optional_property_types: self.exact_optional_property_types.unwrap_or(false),
            force_consistent_casing_in_file_names: self
                .force_consistent_casing_in_file_names
                .unwrap_or(true),
            isolated_modules: self.isolated_modules.unwrap_or(false),
            isolated_declarations: self.isolated_declarations.unwrap_or(false),
            import_helpers: self.import_helpers.unwrap_or(false),
            lib_replacement: self.lib_replacement.unwrap_or(false),
            module_detection: self.module_detection.unwrap_or({
                if matches!(
                    module,
                    ModuleKind::Node16
                        | ModuleKind::Node18
                        | ModuleKind::Node20
                        | ModuleKind::NodeNext
                ) {
                    ModuleDetectionKind::Force
                } else {
                    ModuleDetectionKind::Auto
                }
            }),
            module_detection_specified,
            new_line: self.new_line.unwrap_or_default(),
            no_check: self.no_check.unwrap_or(false),
            no_emit: self.no_emit.unwrap_or(false),
            no_emit_helpers: self.no_emit_helpers.unwrap_or(false),
            no_emit_on_error: self.no_emit_on_error.unwrap_or(false),
            no_error_truncation: self.no_error_truncation.unwrap_or(false),
            remove_comments: self.remove_comments.unwrap_or(false),
            rewrite_relative_import_extensions: self
                .rewrite_relative_import_extensions
                .unwrap_or(false),
            no_implicit_any: self.no_implicit_any.unwrap_or(strict),
            no_implicit_any_specified,
            no_implicit_override: self.no_implicit_override.unwrap_or(false),
            no_implicit_returns: self.no_implicit_returns.unwrap_or(false),
            no_implicit_this: self.no_implicit_this.unwrap_or(strict),
            no_implicit_this_specified,
            no_lib: self.no_lib.unwrap_or(false),
            no_fallthrough_cases_in_switch: self.no_fallthrough_cases_in_switch.unwrap_or(false),
            no_property_access_from_index_signature: self
                .no_property_access_from_index_signature
                .unwrap_or(false),
            no_resolve: self.no_resolve.unwrap_or(false),
            no_unchecked_indexed_access: self.no_unchecked_indexed_access.unwrap_or(false),
            no_unchecked_side_effect_imports: self.no_unchecked_side_effect_imports.unwrap_or(true),
            no_unchecked_side_effect_imports_specified,
            no_unused_locals: self.no_unused_locals.unwrap_or(false),
            no_unused_parameters: self.no_unused_parameters.unwrap_or(false),
            preserve_const_enums: self.preserve_const_enums.unwrap_or(false),
            preserve_symlinks: self.preserve_symlinks.unwrap_or(false),
            skip_default_lib_check: self.skip_default_lib_check.unwrap_or(false),
            skip_lib_check: self.skip_lib_check.unwrap_or(false),
            stable_type_ordering: self.stable_type_ordering.unwrap_or(true),
            strip_internal: self.strip_internal.unwrap_or(false),
            strict,
            strict_specified,
            strict_bind_call_apply: self.strict_bind_call_apply.unwrap_or(strict),
            strict_bind_call_apply_specified,
            strict_builtin_iterator_return: self.strict_builtin_iterator_return.unwrap_or(strict),
            strict_builtin_iterator_return_specified,
            strict_function_types: self.strict_function_types.unwrap_or(strict),
            strict_function_types_specified,
            strict_null_checks: self.strict_null_checks.unwrap_or(strict),
            strict_null_checks_specified,
            strict_property_initialization: self.strict_property_initialization.unwrap_or(strict),
            strict_property_initialization_specified,
            use_define_for_class_fields: self.use_define_for_class_fields,
            use_unknown_in_catch_variables: self.use_unknown_in_catch_variables.unwrap_or(strict),
            use_unknown_in_catch_variables_specified,
            verbatim_module_syntax: self.verbatim_module_syntax.unwrap_or(false),
            lib: self.lib,
            module,
            module_specified,
            module_resolution,
            target: self.target.unwrap_or_default(),
            jsx: self.jsx.unwrap_or_default(),
            jsx_factory: self.jsx_factory,
            jsx_fragment_factory: self.jsx_fragment_factory,
            jsx_import_source: self.jsx_import_source,
            react_namespace: self.react_namespace,
            ignore_deprecations: self.ignore_deprecations,
            max_node_module_js_depth: self.max_node_module_js_depth,
            custom_conditions: self.custom_conditions,
            module_suffixes: self.module_suffixes,
            resolve_json_module: self.resolve_json_module.unwrap_or(
                module_resolution == ModuleResolutionKind::Bundler
                    || matches!(module, ModuleKind::Node20 | ModuleKind::NodeNext),
            ),
            resolve_json_module_specified,
            resolve_package_json_exports: self.resolve_package_json_exports.unwrap_or(true),
            resolve_package_json_imports: self.resolve_package_json_imports.unwrap_or(true),
            source_map: self.source_map.unwrap_or(false),
            inline_source_map: self.inline_source_map.unwrap_or(false),
            inline_sources: self.inline_sources.unwrap_or(false),
            map_root: self.map_root,
            source_root: self.source_root,
            incremental: self.incremental.unwrap_or(composite),
            incremental_specified,
            trace_resolution: self.trace_resolution.unwrap_or(false),
            out_file: self.out_file,
            out_dir: self.out_dir,
            root_dir: self.root_dir,
            declaration_dir: self.declaration_dir,
            ts_build_info_file: self.ts_build_info_file,
            base_url: self.base_url,
            paths: self.paths.unwrap_or_default(),
            root_dirs: self.root_dirs.unwrap_or_default(),
            type_roots: self.type_roots,
            types: self.types,
        }
    }
}

const fn default_module_resolution(module: ModuleKind) -> ModuleResolutionKind {
    match module {
        ModuleKind::Amd => ModuleResolutionKind::Classic,
        ModuleKind::Node16 | ModuleKind::Node18 | ModuleKind::Node20 => {
            ModuleResolutionKind::Node16
        }
        ModuleKind::NodeNext => ModuleResolutionKind::NodeNext,
        ModuleKind::Es2015
        | ModuleKind::Es2020
        | ModuleKind::Es2022
        | ModuleKind::EsNext
        | ModuleKind::Preserve => ModuleResolutionKind::Bundler,
        _ => ModuleResolutionKind::Node10,
    }
}

fn validate_options(options: &PartialOptions, diagnostics: &mut Vec<Diagnostic>) {
    if options.check_js == Some(true) && options.allow_js == Some(false) {
        diagnostics.push(diagnostic(5052, ["checkJs", "allowJs"]));
    }
    if options.no_emit == Some(true) && options.emit_declaration_only == Some(true) {
        diagnostics.push(diagnostic(5053, ["emitDeclarationOnly", "noEmit"]));
    }
    if options.source_map == Some(true) && options.inline_source_map == Some(true) {
        diagnostics.push(diagnostic(5053, ["sourceMap", "inlineSourceMap"]));
    }
    if options.inline_sources == Some(true)
        && options.source_map != Some(true)
        && options.inline_source_map != Some(true)
    {
        diagnostics.push(diagnostic(5051, ["inlineSources"]));
    }
    if options.inline_source_map == Some(true) && options.map_root.is_some() {
        diagnostics.push(diagnostic(5053, ["mapRoot", "inlineSourceMap"]));
    }
    if options.no_lib == Some(true) && options.lib.is_some() {
        diagnostics.push(diagnostic(5053, ["lib", "noLib"]));
    }
    validate_project_and_strict_options(options, diagnostics);
    if options.allow_importing_ts_extensions == Some(true)
        && options.no_emit != Some(true)
        && options.emit_declaration_only != Some(true)
        && options.rewrite_relative_import_extensions != Some(true)
    {
        diagnostics.push(diagnostic(5096, []));
    }
    if options.custom_conditions.is_some()
        && !matches!(
            options.module_resolution.unwrap_or_else(|| {
                default_module_resolution(options.module.unwrap_or_default())
            }),
            ModuleResolutionKind::Node16
                | ModuleResolutionKind::NodeNext
                | ModuleResolutionKind::Bundler
        )
    {
        diagnostics.push(diagnostic(5098, ["customConditions"]));
    }
    if options.out_file.is_some()
        && options.module.is_some_and(|module| {
            !matches!(
                module,
                ModuleKind::None | ModuleKind::Amd | ModuleKind::System
            )
        })
    {
        diagnostics.push(diagnostic(6082, ["outFile"]));
    }

    validate_jsx_options(options, diagnostics);

    let (Some(module), Some(resolution)) = (options.module, options.module_resolution) else {
        return;
    };
    let required = match module {
        ModuleKind::Node16 | ModuleKind::Node18 | ModuleKind::Node20 => {
            Some(ModuleResolutionKind::Node16)
        }
        ModuleKind::NodeNext => Some(ModuleResolutionKind::NodeNext),
        _ => None,
    };
    if let Some(required) = required
        && resolution != required
    {
        diagnostics.push(diagnostic(
            5109,
            [module_resolution_name(required), module_name(module)],
        ));
        return;
    }
    match resolution {
        ModuleResolutionKind::Node16
            if !matches!(
                module,
                ModuleKind::Node16 | ModuleKind::Node18 | ModuleKind::Node20
            ) =>
        {
            diagnostics.push(diagnostic(5110, ["Node16", "Node16"]));
        }
        ModuleResolutionKind::NodeNext if module != ModuleKind::NodeNext => {
            diagnostics.push(diagnostic(5110, ["NodeNext", "NodeNext"]));
        }
        _ => {}
    }
}

fn validate_project_and_strict_options(
    options: &PartialOptions,
    diagnostics: &mut Vec<Diagnostic>,
) {
    if options.composite == Some(true) {
        if options.declaration == Some(false) {
            diagnostics.push(diagnostic(6304, []));
        }
        if options.incremental == Some(false) {
            diagnostics.push(diagnostic(6379, []));
        }
    }

    let strict_null_checks = options
        .strict_null_checks
        .unwrap_or(options.strict.unwrap_or(true));
    if options.strict_property_initialization == Some(true) && !strict_null_checks {
        diagnostics.push(diagnostic(
            5052,
            ["strictPropertyInitialization", "strictNullChecks"],
        ));
    }
    if options.exact_optional_property_types == Some(true) && !strict_null_checks {
        diagnostics.push(diagnostic(
            5052,
            ["exactOptionalPropertyTypes", "strictNullChecks"],
        ));
    }
}

fn validate_jsx_options(options: &PartialOptions, diagnostics: &mut Vec<Diagnostic>) {
    let Some(jsx) = options.jsx else {
        return;
    };
    let automatic = matches!(jsx, JsxEmit::ReactJsx | JsxEmit::ReactJsxDev);
    let jsx_name = match jsx {
        JsxEmit::ReactJsx => "react-jsx",
        JsxEmit::ReactJsxDev => "react-jsxdev",
        JsxEmit::React => "react",
        JsxEmit::Preserve => "preserve",
        JsxEmit::ReactNative => "react-native",
        JsxEmit::None => return,
    };

    if let Some(factory) = &options.jsx_factory {
        if options.react_namespace.is_some() {
            diagnostics.push(diagnostic(5053, ["reactNamespace", "jsxFactory"]));
        }
        if automatic {
            diagnostics.push(diagnostic(5089, ["jsxFactory", jsx_name]));
        }
        if !is_jsx_entity_name(factory, false) {
            diagnostics.push(diagnostic(5067, [factory.as_str()]));
        }
    } else if let Some(namespace) = &options.react_namespace
        && !is_jsx_identifier(namespace)
    {
        diagnostics.push(diagnostic(5059, [namespace.as_str()]));
    }

    if let Some(fragment_factory) = &options.jsx_fragment_factory {
        if options.jsx_factory.is_none() {
            diagnostics.push(diagnostic(5052, ["jsxFragmentFactory", "jsxFactory"]));
        }
        if automatic {
            diagnostics.push(diagnostic(5089, ["jsxFragmentFactory", jsx_name]));
        }
        if !is_jsx_entity_name(fragment_factory, true) {
            diagnostics.push(diagnostic(18_035, [fragment_factory.as_str()]));
        }
    }

    if automatic && options.react_namespace.is_some() {
        diagnostics.push(diagnostic(5089, ["reactNamespace", jsx_name]));
    }
    if jsx == JsxEmit::React && options.jsx_import_source.is_some() {
        diagnostics.push(diagnostic(5089, ["jsxImportSource", jsx_name]));
    }
}

fn is_jsx_entity_name(value: &str, allow_null: bool) -> bool {
    (allow_null && value == "null") || value.split('.').all(is_jsx_identifier)
}

fn is_jsx_identifier(value: &str) -> bool {
    let mut characters = value.chars();
    characters
        .next()
        .is_some_and(|character| character == '_' || character == '$' || character.is_alphabetic())
        && characters
            .all(|character| character == '_' || character == '$' || character.is_alphanumeric())
}

const fn module_name(value: ModuleKind) -> &'static str {
    match value {
        ModuleKind::Node16 => "Node16",
        ModuleKind::Node18 => "Node18",
        ModuleKind::Node20 => "Node20",
        ModuleKind::NodeNext => "NodeNext",
        _ => "",
    }
}

const fn module_resolution_name(value: ModuleResolutionKind) -> &'static str {
    match value {
        ModuleResolutionKind::Node16 => "Node16",
        ModuleResolutionKind::NodeNext => "NodeNext",
        _ => "",
    }
}

fn boolean(name: &str, value: &JsonValue, diagnostics: &mut Vec<Diagnostic>) -> Option<bool> {
    if matches!(value, JsonValue::Null) {
        return None;
    }
    if let Some(value) = value.as_bool() {
        Some(value)
    } else {
        diagnostics.push(diagnostic(5024, [name, "boolean"]));
        None
    }
}

fn string(name: &str, value: &JsonValue, diagnostics: &mut Vec<Diagnostic>) -> Option<String> {
    if matches!(value, JsonValue::Null) {
        return None;
    }
    if let Some(value) = value.as_str() {
        Some(value.to_owned())
    } else {
        diagnostics.push(diagnostic(5024, [name, "string"]));
        None
    }
}

fn number(name: &str, value: &JsonValue, diagnostics: &mut Vec<Diagnostic>) -> Option<i64> {
    if matches!(value, JsonValue::Null) {
        return None;
    }
    if let JsonValue::Number(value) = value
        && let Some(value) = value.as_i64()
    {
        Some(value)
    } else {
        diagnostics.push(diagnostic(5024, [name, "number"]));
        None
    }
}

fn string_array(
    name: &str,
    value: &JsonValue,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<Vec<String>> {
    if matches!(value, JsonValue::Null) {
        return None;
    }
    let Some(values) = value.as_array() else {
        diagnostics.push(diagnostic(5024, [name, "Array"]));
        return None;
    };
    let result = values
        .iter()
        .filter_map(JsonValue::as_str)
        .map(str::to_owned)
        .collect::<Vec<_>>();
    if result.len() != values.len() {
        diagnostics.push(diagnostic(5024, [name, "Array"]));
        return None;
    }
    Some(result)
}

fn paths(
    name: &str,
    value: &JsonValue,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<BTreeMap<String, Vec<String>>> {
    if matches!(value, JsonValue::Null) {
        return None;
    }
    let Some(object) = value.as_object() else {
        diagnostics.push(diagnostic(5024, [name, "object"]));
        return None;
    };
    let mut result = BTreeMap::new();
    for (pattern, substitutions) in object {
        if pattern.matches('*').count() > 1 {
            diagnostics.push(diagnostic(5061, [pattern.as_str()]));
        }
        let Some(substitutions) = substitutions.as_array() else {
            diagnostics.push(diagnostic(5063, [pattern.as_str()]));
            continue;
        };
        if substitutions.is_empty() {
            diagnostics.push(diagnostic(5066, [pattern.as_str()]));
        }
        let mut values = Vec::new();
        for substitution in substitutions {
            let Some(value) = substitution.as_str() else {
                let display = json_value_display(substitution);
                diagnostics.push(diagnostic(
                    5064,
                    [
                        display.as_str(),
                        pattern.as_str(),
                        json_value_type(substitution),
                    ],
                ));
                continue;
            };
            if value.matches('*').count() > 1 {
                diagnostics.push(diagnostic(5062, [value, pattern.as_str()]));
            }
            values.push(value.to_owned());
        }
        result.insert(pattern.clone(), values);
    }
    Some(result)
}

fn json_value_display(value: &JsonValue) -> String {
    match value {
        JsonValue::Null => "null".to_owned(),
        JsonValue::Bool(value) => value.to_string(),
        JsonValue::Number(value) => value.as_str().to_owned(),
        JsonValue::String(value) => value.clone(),
        JsonValue::Array(_) => "[object Array]".to_owned(),
        JsonValue::Object(_) => "[object Object]".to_owned(),
    }
}

const fn json_value_type(value: &JsonValue) -> &'static str {
    match value {
        JsonValue::Null => "null",
        JsonValue::Bool(_) => "boolean",
        JsonValue::Number(_) => "number",
        JsonValue::String(_) => "string",
        JsonValue::Array(_) => "array",
        JsonValue::Object(_) => "object",
    }
}

fn validate_plugins(name: &str, value: &JsonValue, diagnostics: &mut Vec<Diagnostic>) {
    if matches!(value, JsonValue::Null) {
        return;
    }
    if !value
        .as_array()
        .is_some_and(|plugins| plugins.iter().all(|plugin| plugin.as_object().is_some()))
    {
        diagnostics.push(diagnostic(5024, [name, "Array"]));
    }
}

fn enum_value<T>(
    name: &str,
    value: &JsonValue,
    diagnostics: &mut Vec<Diagnostic>,
    parse: fn(&str) -> Option<T>,
) -> Option<T> {
    if matches!(value, JsonValue::Null) {
        return None;
    }
    let Some(value) = value.as_str() else {
        diagnostics.push(diagnostic(5024, [name, "string"]));
        return None;
    };
    let Some(parsed) = parse(value) else {
        diagnostics.push(diagnostic(6046, [name, allowed_values(name)]));
        return None;
    };
    Some(parsed)
}

fn module(value: &str) -> Option<ModuleKind> {
    Some(match value.to_ascii_lowercase().as_str() {
        "none" => ModuleKind::None,
        "commonjs" => ModuleKind::CommonJs,
        "amd" => ModuleKind::Amd,
        "umd" => ModuleKind::Umd,
        "system" => ModuleKind::System,
        "es6" | "es2015" => ModuleKind::Es2015,
        "es2020" => ModuleKind::Es2020,
        "es2022" => ModuleKind::Es2022,
        "esnext" => ModuleKind::EsNext,
        "node16" => ModuleKind::Node16,
        "node18" => ModuleKind::Node18,
        "node20" => ModuleKind::Node20,
        "nodenext" => ModuleKind::NodeNext,
        "preserve" => ModuleKind::Preserve,
        _ => return None,
    })
}

fn module_resolution(value: &str) -> Option<ModuleResolutionKind> {
    Some(match value.to_ascii_lowercase().as_str() {
        "classic" => ModuleResolutionKind::Classic,
        "node" | "node10" => ModuleResolutionKind::Node10,
        "node16" => ModuleResolutionKind::Node16,
        "nodenext" => ModuleResolutionKind::NodeNext,
        "bundler" => ModuleResolutionKind::Bundler,
        _ => return None,
    })
}

fn module_detection(value: &str) -> Option<ModuleDetectionKind> {
    Some(match value.to_ascii_lowercase().as_str() {
        "legacy" => ModuleDetectionKind::Legacy,
        "auto" => ModuleDetectionKind::Auto,
        "force" => ModuleDetectionKind::Force,
        _ => return None,
    })
}

fn new_line(value: &str) -> Option<NewLineKind> {
    Some(match value.to_ascii_lowercase().as_str() {
        "lf" => NewLineKind::Lf,
        "crlf" => NewLineKind::Crlf,
        _ => return None,
    })
}

fn target(value: &str) -> Option<ScriptTarget> {
    Some(match value.to_ascii_lowercase().as_str() {
        "es3" => ScriptTarget::Es3,
        "es5" => ScriptTarget::Es5,
        "es6" | "es2015" => ScriptTarget::Es2015,
        "es2016" => ScriptTarget::Es2016,
        "es2017" => ScriptTarget::Es2017,
        "es2018" => ScriptTarget::Es2018,
        "es2019" => ScriptTarget::Es2019,
        "es2020" => ScriptTarget::Es2020,
        "es2021" => ScriptTarget::Es2021,
        "es2022" => ScriptTarget::Es2022,
        "es2023" => ScriptTarget::Es2023,
        "es2024" => ScriptTarget::Es2024,
        "es2025" => ScriptTarget::Es2025,
        "esnext" | "latest" => ScriptTarget::EsNext,
        _ => return None,
    })
}

fn jsx(value: &str) -> Option<JsxEmit> {
    Some(match value.to_ascii_lowercase().as_str() {
        "preserve" => JsxEmit::Preserve,
        "react" => JsxEmit::React,
        "react-native" => JsxEmit::ReactNative,
        "react-jsx" => JsxEmit::ReactJsx,
        "react-jsxdev" => JsxEmit::ReactJsxDev,
        _ => return None,
    })
}

fn allowed_values(name: &str) -> &'static str {
    match name.to_ascii_lowercase().as_str() {
        "module" => {
            "'none', 'commonjs', 'amd', 'umd', 'system', 'es2015', 'es2020', 'es2022', 'esnext', 'node16', 'node18', 'node20', 'nodenext', 'preserve'"
        }
        "moduleresolution" => "'classic', 'node10', 'node16', 'nodenext', 'bundler'",
        "moduledetection" => "'legacy', 'auto', 'force'",
        "newline" => "'crlf', 'lf'",
        "target" => {
            "'es3', 'es5', 'es2015', 'es2016', 'es2017', 'es2018', 'es2019', 'es2020', 'es2021', 'es2022', 'es2023', 'es2024', 'es2025', 'esnext'"
        }
        "jsx" => "'preserve', 'react', 'react-native', 'react-jsx', 'react-jsxdev'",
        _ => "a valid value",
    }
}

fn diagnostic<const N: usize>(code: u32, arguments: [&str; N]) -> Diagnostic {
    let message = message_by_code(code).expect("compiler option diagnostic must exist");
    Diagnostic::with_arguments(message, arguments)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use ts_config::{JsonValue, parse_config_text};
    use ts_module::{ResolutionMode, ResolutionOptions};

    use super::{
        CompilerOptions, JsxEmit, ModuleDetectionKind, ModuleKind, ModuleResolutionKind,
        NewLineKind, ScriptTarget, UnusedLabelReporting, parse_compiler_options,
        parse_project_options,
    };

    fn object(entries: impl IntoIterator<Item = (&'static str, JsonValue)>) -> JsonValue {
        JsonValue::Object(
            entries
                .into_iter()
                .map(|(name, value)| (name.to_owned(), value))
                .collect::<BTreeMap<_, _>>(),
        )
    }

    #[test]
    fn defaults_to_untransformed_modules_with_node10_resolution() {
        let direct = CompilerOptions::default();
        assert_eq!(ModuleKind::default(), ModuleKind::None);
        assert_eq!(direct.module, ModuleKind::None);
        assert!(!direct.module_specified);
        assert_eq!(direct.module_resolution, ModuleResolutionKind::Node10);

        let parsed = parse_compiler_options(&object([]));
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);
        assert_eq!(parsed.options.module, ModuleKind::None);
        assert!(!parsed.options.module_specified);
        assert_eq!(
            parsed.options.module_resolution,
            ModuleResolutionKind::Node10
        );

        let mut overridden = CompilerOptions::default();
        overridden.apply_overrides(
            &CompilerOptions::default(),
            &BTreeSet::from(["module".to_owned()]),
        );
        assert!(overridden.module_specified);
    }

    #[test]
    fn parses_names_and_enum_values_case_insensitively() {
        let result = parse_compiler_options(&object([
            ("TARGET", JsonValue::String("ES2025".into())),
            ("Module", JsonValue::String("NodeNext".into())),
            ("JsX", JsonValue::String("React-JSX".into())),
        ]));
        assert!(result.is_ok());
        assert_eq!(result.options.target, ScriptTarget::Es2025);
        assert_eq!(result.options.module, ModuleKind::NodeNext);
        assert!(result.options.module_specified);
        assert_eq!(result.options.jsx, JsxEmit::ReactJsx);
        assert_eq!(
            result.options.module_resolution,
            ModuleResolutionKind::NodeNext
        );
    }

    #[test]
    fn uses_bundler_resolution_for_explicit_ecmascript_modules() {
        for module in ["es2015", "es2020", "es2022", "esnext", "preserve"] {
            let result =
                parse_compiler_options(&object([("module", JsonValue::String(module.into()))]));
            assert!(result.is_ok(), "{module}: {:?}", result.diagnostics);
            assert_eq!(
                result.options.module_resolution,
                ModuleResolutionKind::Bundler,
                "{module}"
            );
            assert!(result.options.resolve_json_module, "{module}");
            assert!(!result.options.resolve_json_module_specified, "{module}");
        }
    }

    #[test]
    fn node_module_formats_force_detection_without_replacing_explicit_modes() {
        for (module, resolution) in [
            ("node16", ModuleResolutionKind::Node16),
            ("node18", ModuleResolutionKind::Node16),
            ("node20", ModuleResolutionKind::Node16),
            ("nodenext", ModuleResolutionKind::NodeNext),
        ] {
            let result =
                parse_compiler_options(&object([("module", JsonValue::String(module.into()))]));
            assert!(result.is_ok(), "{module}: {:?}", result.diagnostics);
            assert_eq!(result.options.module_resolution, resolution);
            assert_eq!(result.options.module_detection, ModuleDetectionKind::Force);
            assert!(!result.options.module_detection_specified);
        }

        let explicit = parse_compiler_options(&object([
            ("module", JsonValue::String("nodenext".into())),
            ("moduleDetection", JsonValue::String("legacy".into())),
            ("resolveJsonModule", JsonValue::Bool(false)),
        ]));
        assert!(explicit.is_ok(), "{:?}", explicit.diagnostics);
        assert_eq!(
            explicit.options.module_detection,
            ModuleDetectionKind::Legacy
        );
        assert!(explicit.options.module_detection_specified);
        assert!(!explicit.options.resolve_json_module);
        assert!(explicit.options.resolve_json_module_specified);
    }

    #[test]
    fn applies_jsconfig_defaults_without_overriding_explicit_settings() {
        let defaults = parse_config_text("/repo/jsconfig.json", "{}")
            .value
            .unwrap();
        let defaults = parse_project_options(&defaults);
        assert!(defaults.is_ok(), "{:?}", defaults.diagnostics);
        assert!(defaults.options.allow_js);
        assert!(!defaults.options.allow_js_specified);
        assert_eq!(defaults.options.max_node_module_js_depth, Some(2));
        assert!(defaults.options.skip_lib_check);
        assert!(defaults.options.no_emit);

        let overrides = parse_config_text(
            "/repo/JSCONFIG.JSON",
            r#"{
                "compilerOptions": {
                    "allowJs": false,
                    "maxNodeModuleJsDepth": 4,
                    "skipLibCheck": false,
                    "noEmit": false
                }
            }"#,
        )
        .value
        .unwrap();
        let overrides = parse_project_options(&overrides);
        assert!(overrides.is_ok(), "{:?}", overrides.diagnostics);
        assert!(!overrides.options.allow_js);
        assert!(overrides.options.allow_js_specified);
        assert_eq!(overrides.options.max_node_module_js_depth, Some(4));
        assert!(!overrides.options.skip_lib_check);
        assert!(!overrides.options.no_emit);

        let typescript = parse_config_text("/repo/tsconfig.json", "{}")
            .value
            .unwrap();
        let typescript = parse_project_options(&typescript);
        assert!(!typescript.options.allow_js);
        assert!(typescript.options.max_node_module_js_depth.is_none());
        assert!(!typescript.options.skip_lib_check);
        assert!(!typescript.options.no_emit);
    }

    #[test]
    fn preserves_explicit_javascript_options_across_checkjs_overrides() {
        let mut explicit =
            parse_compiler_options(&object([("allowJs", JsonValue::Bool(false))])).options;
        assert!(explicit.allow_js_specified);
        let checking =
            parse_compiler_options(&object([("checkJs", JsonValue::Bool(true))])).options;
        explicit.apply_overrides(&checking, &BTreeSet::from(["checkjs".to_owned()]));
        assert!(explicit.check_js);
        assert!(!explicit.allow_js);

        let mut implied = CompilerOptions::default();
        implied.apply_overrides(&checking, &BTreeSet::from(["checkjs".to_owned()]));
        assert!(implied.check_js);
        assert!(implied.allow_js);

        let invalid = parse_compiler_options(&object([
            ("allowJs", JsonValue::Bool(false)),
            ("checkJs", JsonValue::Bool(true)),
        ]));
        assert_eq!(invalid.diagnostics.len(), 1);
        assert_eq!(invalid.diagnostics[0].code(), 5052);
        assert_eq!(
            invalid.diagnostics[0].render().unwrap(),
            "Option 'checkJs' cannot be specified without specifying option 'allowJs'."
        );
    }

    #[test]
    fn tracks_module_default_provenance_across_overrides() {
        let node =
            parse_compiler_options(&object([("module", JsonValue::String("nodenext".into()))]))
                .options;
        let mut defaults = CompilerOptions::default();
        defaults.apply_overrides(&node, &BTreeSet::from(["module".to_owned()]));
        assert_eq!(defaults.module_resolution, ModuleResolutionKind::NodeNext);
        assert_eq!(defaults.module_detection, ModuleDetectionKind::Force);
        assert!(defaults.resolve_json_module);

        let mut explicit = parse_compiler_options(&object([
            ("moduleDetection", JsonValue::String("legacy".into())),
            ("resolveJsonModule", JsonValue::Bool(false)),
        ]))
        .options;
        explicit.apply_overrides(&node, &BTreeSet::from(["module".to_owned()]));
        assert_eq!(explicit.module_detection, ModuleDetectionKind::Legacy);
        assert!(!explicit.resolve_json_module);
    }

    #[test]
    fn applies_boolean_implications_and_emission_settings() {
        let result = parse_compiler_options(&object([
            ("checkJs", JsonValue::Bool(true)),
            ("composite", JsonValue::Bool(true)),
            ("emitDeclarationOnly", JsonValue::Bool(true)),
            ("incremental", JsonValue::Bool(true)),
            ("noCheck", JsonValue::Bool(true)),
            ("noEmitOnError", JsonValue::Bool(true)),
        ]));
        assert!(result.options.allow_js);
        assert!(result.options.declaration);
        assert!(result.options.composite);
        assert!(result.options.incremental);
        assert!(result.options.no_check);
        assert!(result.options.no_emit_on_error);
        let settings = result.options.printer_settings();
        assert!(!settings.emit_javascript);
        assert!(settings.emit_declarations);

        let no_emit = CompilerOptions {
            no_emit: true,
            declaration: true,
            ..CompilerOptions::default()
        }
        .printer_settings();
        assert!(!no_emit.emit_javascript);
        assert!(!no_emit.emit_declarations);
    }

    #[test]
    fn composite_projects_infer_declarations_and_incremental_builds() {
        let composite = parse_compiler_options(&object([("composite", JsonValue::Bool(true))]));
        assert!(composite.is_ok(), "{:?}", composite.diagnostics);
        assert!(composite.options.declaration);
        assert!(composite.options.incremental);
        assert!(!composite.options.declaration_specified);
        assert!(!composite.options.incremental_specified);
        assert!(composite.options.printer_settings().emit_declarations);

        let direct = CompilerOptions {
            composite: true,
            ..CompilerOptions::default()
        };
        assert!(direct.printer_settings().emit_declarations);

        let invalid = parse_compiler_options(&object([
            ("composite", JsonValue::Bool(true)),
            ("declaration", JsonValue::Bool(false)),
            ("incremental", JsonValue::Bool(false)),
        ]));
        assert_eq!(
            invalid
                .diagnostics
                .iter()
                .map(ts_diagnostics::Diagnostic::code)
                .collect::<Vec<_>>(),
            [6304, 6379]
        );
        assert!(!invalid.options.declaration);
        assert!(!invalid.options.incremental);
        assert!(invalid.options.declaration_specified);
        assert!(invalid.options.incremental_specified);
    }

    #[test]
    fn composite_overrides_preserve_explicit_declaration_and_incremental_options() {
        let enabled =
            parse_compiler_options(&object([("composite", JsonValue::Bool(true))])).options;
        let mut inferred = CompilerOptions::default();
        inferred.apply_overrides(&enabled, &BTreeSet::from(["composite".to_owned()]));
        assert!(inferred.composite);
        assert!(inferred.declaration);
        assert!(inferred.incremental);

        let mut explicit = parse_compiler_options(&object([
            ("declaration", JsonValue::Bool(false)),
            ("incremental", JsonValue::Bool(false)),
        ]))
        .options;
        explicit.apply_overrides(&enabled, &BTreeSet::from(["composite".to_owned()]));
        assert!(explicit.composite);
        assert!(!explicit.declaration);
        assert!(!explicit.incremental);
    }

    #[test]
    fn explicit_strict_property_initialization_requires_strict_null_checks() {
        let invalid = parse_compiler_options(&object([
            ("strict", JsonValue::Bool(false)),
            ("strictPropertyInitialization", JsonValue::Bool(true)),
        ]));
        assert_eq!(invalid.diagnostics.len(), 1);
        assert_eq!(invalid.diagnostics[0].code(), 5052);
        assert_eq!(
            invalid.diagnostics[0].render().unwrap(),
            "Option 'strictPropertyInitialization' cannot be specified without specifying option 'strictNullChecks'."
        );

        let valid = parse_compiler_options(&object([
            ("strict", JsonValue::Bool(false)),
            ("strictNullChecks", JsonValue::Bool(true)),
            ("strictPropertyInitialization", JsonValue::Bool(true)),
        ]));
        assert!(valid.is_ok(), "{:?}", valid.diagnostics);
    }

    #[test]
    fn compiler_defaults_match_pinned_interoperability_and_casing_options() {
        let defaults = CompilerOptions::default();
        assert!(defaults.allow_synthetic_default_imports);
        assert!(defaults.force_consistent_casing_in_file_names);

        let parsed = parse_compiler_options(&object([]));
        assert!(parsed.options.allow_synthetic_default_imports);
        assert!(parsed.options.force_consistent_casing_in_file_names);

        let disabled = parse_compiler_options(&object([(
            "forceConsistentCasingInFileNames",
            JsonValue::Bool(false),
        )]));
        assert!(disabled.is_ok(), "{:?}", disabled.diagnostics);
        assert!(!disabled.options.force_consistent_casing_in_file_names);
    }

    #[test]
    fn side_effect_import_checking_defaults_on_and_retains_explicit_false() {
        let defaults = CompilerOptions::default();
        assert!(defaults.no_unchecked_side_effect_imports);
        assert!(!defaults.no_unchecked_side_effect_imports_specified);

        let parsed = parse_compiler_options(&object([]));
        assert!(parsed.options.no_unchecked_side_effect_imports);
        assert!(!parsed.options.no_unchecked_side_effect_imports_specified);

        let disabled = parse_compiler_options(&object([(
            "noUncheckedSideEffectImports",
            JsonValue::Bool(false),
        )]));
        assert!(disabled.is_ok(), "{:?}", disabled.diagnostics);
        assert!(!disabled.options.no_unchecked_side_effect_imports);
        assert!(disabled.options.no_unchecked_side_effect_imports_specified);

        let mut overridden = defaults;
        overridden.apply_overrides(
            &disabled.options,
            &BTreeSet::from(["nouncheckedsideeffectimports".to_owned()]),
        );
        assert!(!overridden.no_unchecked_side_effect_imports);
        assert!(overridden.no_unchecked_side_effect_imports_specified);
    }

    #[test]
    fn unused_label_reporting_preserves_type_scripts_three_states() {
        assert_eq!(
            CompilerOptions::default().unused_label_reporting(),
            UnusedLabelReporting::Suggestion
        );
        let ignored =
            parse_compiler_options(&object([("allowUnusedLabels", JsonValue::Bool(true))]));
        assert_eq!(
            ignored.options.unused_label_reporting(),
            UnusedLabelReporting::Ignore
        );
        let errors =
            parse_compiler_options(&object([("allowUnusedLabels", JsonValue::Bool(false))]));
        assert_eq!(
            errors.options.unused_label_reporting(),
            UnusedLabelReporting::Error
        );
    }

    #[test]
    fn skip_library_options_only_suppress_their_matching_source_categories() {
        let defaults = CompilerOptions::default();
        assert!(!defaults.skips_type_checking(false, false));
        assert!(!defaults.skips_type_checking(true, true));

        let default_only =
            parse_compiler_options(&object([("skipDefaultLibCheck", JsonValue::Bool(true))]));
        assert!(default_only.options.skips_type_checking(true, true));
        assert!(!default_only.options.skips_type_checking(true, false));
        assert!(!default_only.options.skips_type_checking(false, false));

        let all_declarations =
            parse_compiler_options(&object([("skipLibCheck", JsonValue::Bool(true))]));
        assert!(all_declarations.options.skips_type_checking(true, true));
        assert!(all_declarations.options.skips_type_checking(true, false));
        assert!(!all_declarations.options.skips_type_checking(false, false));

        let unchecked = parse_compiler_options(&object([("noCheck", JsonValue::Bool(true))]));
        assert!(unchecked.options.skips_type_checking(false, false));
    }

    #[test]
    fn declaration_sources_and_rewritten_imports_allow_typescript_extensions() {
        let defaults = CompilerOptions::default();
        assert!(!defaults.allows_importing_typescript_extensions_from("/project/main.ts"));
        assert!(defaults.allows_importing_typescript_extensions_from("/project/main.d.ts"));
        assert!(defaults.allows_importing_typescript_extensions_from("/project/main.d.mts"));

        let rewritten = parse_compiler_options(&object([(
            "rewriteRelativeImportExtensions",
            JsonValue::Bool(true),
        )]));
        assert!(
            rewritten
                .options
                .allows_importing_typescript_extensions_from("/project/main.ts")
        );

        let explicit = parse_compiler_options(&object([
            ("allowImportingTsExtensions", JsonValue::Bool(true)),
            ("noEmit", JsonValue::Bool(true)),
        ]));
        assert!(explicit.is_ok(), "{:?}", explicit.diagnostics);
        assert!(
            explicit
                .options
                .allows_importing_typescript_extensions_from("/project/main.ts")
        );
    }

    #[test]
    fn parses_trace_resolution_and_preserves_command_line_overrides() {
        let enabled = parse_compiler_options(&object([("traceResolution", JsonValue::Bool(true))]));
        assert!(enabled.is_ok(), "{:?}", enabled.diagnostics);
        assert!(enabled.options.trace_resolution);

        let mut options = CompilerOptions::default();
        options.apply_overrides(
            &enabled.options,
            &BTreeSet::from(["traceresolution".to_owned()]),
        );
        assert!(options.trace_resolution);
    }

    #[test]
    fn threads_no_emit_helpers_to_the_printer() {
        let result = parse_compiler_options(&object([("noEmitHelpers", JsonValue::Bool(true))]));
        assert!(result.is_ok(), "{:?}", result.diagnostics);
        assert!(result.options.no_emit_helpers);
        assert!(result.options.printer_settings().no_emit_helpers);
    }

    #[test]
    fn parses_emit_decorator_metadata() {
        let result =
            parse_compiler_options(&object([("emitDecoratorMetadata", JsonValue::Bool(true))]));
        assert!(result.is_ok(), "{:?}", result.diagnostics);
        assert!(result.options.emit_decorator_metadata);
    }

    #[test]
    fn threads_experimental_decorators_to_the_printer() {
        let result =
            parse_compiler_options(&object([("experimentalDecorators", JsonValue::Bool(true))]));
        assert!(result.is_ok(), "{:?}", result.diagnostics);
        assert!(result.options.experimental_decorators);
        assert!(result.options.printer_settings().experimental_decorators);
    }

    #[test]
    fn threads_import_helpers_to_the_printer() {
        let result = parse_compiler_options(&object([("importHelpers", JsonValue::Bool(true))]));
        assert!(result.is_ok(), "{:?}", result.diagnostics);
        assert!(result.options.import_helpers);
        assert!(result.options.printer_settings().import_helpers);
    }

    #[test]
    fn threads_remove_comments_to_the_printer() {
        let result = parse_compiler_options(&object([("removeComments", JsonValue::Bool(true))]));
        assert!(result.is_ok(), "{:?}", result.diagnostics);
        assert!(result.options.remove_comments);
        assert!(result.options.printer_settings().remove_comments);
    }

    #[test]
    fn parses_strip_internal() {
        let result = parse_compiler_options(&object([("stripInternal", JsonValue::Bool(true))]));
        assert!(result.is_ok(), "{:?}", result.diagnostics);
        assert!(result.options.strip_internal);
    }

    #[test]
    fn normalizes_strict_and_interoperability_options() {
        let result = parse_compiler_options(&object([
            ("strict", JsonValue::Bool(true)),
            ("strictFunctionTypes", JsonValue::Bool(false)),
            ("strictNullChecks", JsonValue::Bool(false)),
            ("allowUnreachableCode", JsonValue::Bool(false)),
            ("noImplicitReturns", JsonValue::Bool(true)),
            ("noFallthroughCasesInSwitch", JsonValue::Bool(true)),
            ("esModuleInterop", JsonValue::Bool(true)),
            ("noUnusedLocals", JsonValue::Bool(true)),
            ("noUnusedParameters", JsonValue::Bool(true)),
            ("noUncheckedSideEffectImports", JsonValue::Bool(true)),
            ("skipLibCheck", JsonValue::Bool(true)),
            ("verbatimModuleSyntax", JsonValue::Bool(true)),
            ("isolatedModules", JsonValue::Bool(true)),
            ("forceConsistentCasingInFileNames", JsonValue::Bool(true)),
            ("moduleDetection", JsonValue::String("force".into())),
        ]));
        assert!(result.is_ok());
        assert!(result.options.strict);
        assert!(result.options.always_strict);
        assert!(result.options.no_implicit_any);
        assert!(!result.options.strict_function_types);
        assert!(result.options.strict_function_types_specified);
        assert!(!result.options.strict_null_checks);
        assert_eq!(result.options.allow_unreachable_code, Some(false));
        assert!(result.options.no_implicit_returns);
        assert!(result.options.no_fallthrough_cases_in_switch);
        assert!(result.options.use_unknown_in_catch_variables);
        assert!(result.options.es_module_interop);
        assert!(result.options.allow_synthetic_default_imports);
        assert!(result.options.no_unused_locals);
        assert!(result.options.no_unused_parameters);
        assert!(result.options.no_unchecked_side_effect_imports);
        assert!(result.options.skip_lib_check);
        assert!(result.options.verbatim_module_syntax);
        assert!(result.options.isolated_modules);
        assert!(result.options.force_consistent_casing_in_file_names);
        assert_eq!(result.options.module_detection, ModuleDetectionKind::Force);
    }

    #[test]
    fn parses_pinned_semantic_module_and_project_options() {
        let config = parse_config_text(
            "/repo/tsconfig.json",
            r#"{
                "compilerOptions": {
                    "allowImportingTsExtensions": true,
                    "allowUmdGlobalAccess": true,
                    "allowUnusedLabels": false,
                    "assumeChangesOnlyAffectDirectDependencies": true,
                    "customConditions": ["development", "browser"],
                    "deduplicatePackages": false,
                    "disableSizeLimit": true,
                    "erasableSyntaxOnly": true,
                    "ignoreDeprecations": "6.0",
                    "libReplacement": true,
                    "maxNodeModuleJsDepth": 2,
                    "moduleResolution": "bundler",
                    "moduleSuffixes": [".native", ""],
                    "newLine": "CRLF",
                    "noEmit": true,
                    "noErrorTruncation": true,
                    "noImplicitOverride": true,
                    "noImplicitThis": false,
                    "noPropertyAccessFromIndexSignature": true,
                    "noResolve": true,
                    "noUncheckedIndexedAccess": true,
                    "plugins": [{ "name": "example-plugin" }],
                    "preserveSymlinks": true,
                    "skipDefaultLibCheck": true,
                    "stableTypeOrdering": false
                }
            }"#,
        )
        .value
        .unwrap();
        let result = parse_project_options(&config);
        assert!(result.is_ok(), "{:?}", result.diagnostics);
        let options = result.options;
        assert!(options.allow_importing_ts_extensions);
        assert!(options.allow_umd_global_access);
        assert_eq!(options.allow_unused_labels, Some(false));
        assert!(options.assume_changes_only_affect_direct_dependencies);
        assert_eq!(
            options.custom_conditions,
            Some(vec!["development".into(), "browser".into()])
        );
        assert!(!options.deduplicate_packages);
        assert!(options.disable_size_limit);
        assert!(options.erasable_syntax_only);
        assert_eq!(options.ignore_deprecations.as_deref(), Some("6.0"));
        assert!(options.lib_replacement);
        assert_eq!(options.max_node_module_js_depth, Some(2));
        assert_eq!(
            options.module_suffixes,
            Some(vec![".native".into(), String::new()])
        );
        assert_eq!(options.new_line, NewLineKind::Crlf);
        assert!(options.no_error_truncation);
        assert!(options.no_implicit_override);
        assert!(!options.no_implicit_this);
        assert!(options.no_implicit_this_specified);
        assert!(options.no_property_access_from_index_signature);
        assert!(options.no_resolve);
        assert!(options.no_unchecked_indexed_access);
        assert!(options.preserve_symlinks);
        assert!(options.skip_default_lib_check);
        assert!(!options.stable_type_ordering);
        assert!(options.resolve_json_module);
    }

    #[test]
    fn validates_pinned_module_options() {
        let importing = parse_compiler_options(&object([(
            "allowImportingTsExtensions",
            JsonValue::Bool(true),
        )]));
        assert_eq!(importing.diagnostics.len(), 1);
        assert_eq!(importing.diagnostics[0].code(), 5096);

        let rewritten = parse_compiler_options(&object([
            ("allowImportingTsExtensions", JsonValue::Bool(true)),
            ("rewriteRelativeImportExtensions", JsonValue::Bool(true)),
        ]));
        assert!(rewritten.is_ok(), "{:?}", rewritten.diagnostics);

        let conditions = parse_compiler_options(&object([(
            "customConditions",
            JsonValue::Array(vec![JsonValue::String("development".into())]),
        )]));
        assert_eq!(conditions.diagnostics.len(), 1);
        assert_eq!(conditions.diagnostics[0].code(), 5098);

        let plugins = parse_compiler_options(&object([(
            "plugins",
            JsonValue::Array(vec![JsonValue::String("invalid".into())]),
        )]));
        assert_eq!(plugins.diagnostics.len(), 1);
        assert_eq!(plugins.diagnostics[0].code(), 5024);
    }

    #[test]
    fn null_values_clear_inherited_options_without_type_diagnostics() {
        let result = parse_compiler_options(&object([
            ("allowJs", JsonValue::Null),
            ("customConditions", JsonValue::Null),
            ("lib", JsonValue::Null),
            ("maxNodeModuleJsDepth", JsonValue::Null),
            ("module", JsonValue::Null),
            ("outDir", JsonValue::Null),
            ("paths", JsonValue::Null),
            ("plugins", JsonValue::Null),
            ("typeRoots", JsonValue::Null),
            ("types", JsonValue::Null),
        ]));
        assert!(result.is_ok(), "{:?}", result.diagnostics);
        assert!(!result.options.allow_js);
        assert!(result.options.custom_conditions.is_none());
        assert!(result.options.lib.is_none());
        assert!(result.options.max_node_module_js_depth.is_none());
        assert!(result.options.out_dir.is_none());
        assert!(result.options.paths.is_empty());
        assert!(result.options.type_roots.is_none());
        assert!(result.options.types.is_none());
    }

    #[test]
    fn applies_previously_omitted_project_option_overrides() {
        let overrides = parse_compiler_options(&object([
            ("allowJs", JsonValue::Bool(true)),
            ("baseUrl", JsonValue::String("/override".into())),
            ("composite", JsonValue::Bool(true)),
            ("declarationMap", JsonValue::Bool(true)),
            ("incremental", JsonValue::Bool(true)),
            ("noImplicitThis", JsonValue::Bool(false)),
            ("noUncheckedIndexedAccess", JsonValue::Bool(true)),
            ("resolveJsonModule", JsonValue::Bool(true)),
            (
                "rootDirs",
                JsonValue::Array(vec![JsonValue::String("/override/src".into())]),
            ),
            (
                "types",
                JsonValue::Array(vec![JsonValue::String("node".into())]),
            ),
        ]));
        assert!(overrides.is_ok(), "{:?}", overrides.diagnostics);

        let mut options = CompilerOptions::default();
        options.apply_overrides(
            &overrides.options,
            &BTreeSet::from([
                "allowjs".to_owned(),
                "baseurl".to_owned(),
                "composite".to_owned(),
                "declarationmap".to_owned(),
                "incremental".to_owned(),
                "noimplicitthis".to_owned(),
                "nouncheckedindexedaccess".to_owned(),
                "resolvejsonmodule".to_owned(),
                "rootdirs".to_owned(),
                "types".to_owned(),
            ]),
        );

        assert!(options.allow_js);
        assert_eq!(options.base_url.as_deref(), Some("/override"));
        assert!(options.composite);
        assert!(options.declaration);
        assert!(options.declaration_map);
        assert!(options.incremental);
        assert!(!options.no_implicit_this);
        assert!(options.no_implicit_this_specified);
        assert!(options.no_unchecked_indexed_access);
        assert!(options.resolve_json_module);
        assert_eq!(options.root_dirs, ["/override/src"]);
        assert_eq!(options.types, Some(vec!["node".into()]));
    }

    #[test]
    fn parses_and_validates_exact_optional_property_types() {
        let enabled = parse_compiler_options(&object([
            ("strictNullChecks", JsonValue::Bool(true)),
            ("exactOptionalPropertyTypes", JsonValue::Bool(true)),
        ]));
        assert!(enabled.is_ok(), "{:?}", enabled.diagnostics);
        assert!(enabled.options.exact_optional_property_types);

        let implied_by_strict = parse_compiler_options(&object([
            ("strict", JsonValue::Bool(true)),
            ("exactOptionalPropertyTypes", JsonValue::Bool(true)),
        ]));
        assert!(
            implied_by_strict.is_ok(),
            "{:?}",
            implied_by_strict.diagnostics
        );

        let defaults = parse_compiler_options(&object([(
            "exactOptionalPropertyTypes",
            JsonValue::Bool(true),
        )]));
        assert!(defaults.is_ok(), "{:?}", defaults.diagnostics);

        let invalid = parse_compiler_options(&object([
            ("strict", JsonValue::Bool(false)),
            ("exactOptionalPropertyTypes", JsonValue::Bool(true)),
        ]));
        assert_eq!(
            invalid
                .diagnostics
                .iter()
                .map(ts_diagnostics::Diagnostic::code)
                .collect::<Vec<_>>(),
            [5052]
        );

        let explicitly_disabled = parse_compiler_options(&object([
            ("strict", JsonValue::Bool(true)),
            ("strictNullChecks", JsonValue::Bool(false)),
            ("exactOptionalPropertyTypes", JsonValue::Bool(true)),
        ]));
        assert_eq!(
            explicitly_disabled
                .diagnostics
                .iter()
                .map(ts_diagnostics::Diagnostic::code)
                .collect::<Vec<_>>(),
            [5052]
        );
    }

    #[test]
    fn preserves_strict_option_provenance_across_overrides() {
        let defaults = parse_compiler_options(&object([])).options;
        assert!(defaults.strict);
        assert!(defaults.no_implicit_any);
        assert!(defaults.no_implicit_this);
        assert!(defaults.strict_bind_call_apply);
        assert!(defaults.strict_builtin_iterator_return);
        assert!(defaults.strict_function_types);
        assert!(defaults.strict_null_checks);
        assert!(defaults.strict_property_initialization);
        assert!(defaults.use_unknown_in_catch_variables);
        assert!(!defaults.strict_specified);
        assert!(!defaults.no_implicit_any_specified);
        assert!(!defaults.no_implicit_this_specified);
        assert!(!defaults.strict_bind_call_apply_specified);
        assert!(!defaults.strict_builtin_iterator_return_specified);
        assert!(!defaults.strict_function_types_specified);
        assert!(!defaults.strict_null_checks_specified);
        assert!(!defaults.strict_property_initialization_specified);
        assert!(!defaults.use_unknown_in_catch_variables_specified);

        let disabled =
            parse_compiler_options(&object([("strict", JsonValue::Bool(false))])).options;
        assert!(!disabled.strict);
        assert!(!disabled.no_implicit_any);
        assert!(!disabled.no_implicit_this);
        assert!(!disabled.strict_bind_call_apply);
        assert!(!disabled.strict_builtin_iterator_return);
        assert!(!disabled.strict_function_types);
        assert!(!disabled.strict_null_checks);
        assert!(!disabled.strict_property_initialization);
        assert!(!disabled.use_unknown_in_catch_variables);

        let mut inherited = parse_compiler_options(&object([
            ("strictBindCallApply", JsonValue::Bool(true)),
            ("strictBuiltinIteratorReturn", JsonValue::Bool(true)),
            ("strictFunctionTypes", JsonValue::Bool(true)),
            ("strictNullChecks", JsonValue::Bool(true)),
            ("strictPropertyInitialization", JsonValue::Bool(true)),
        ]))
        .options;
        inherited.apply_overrides(&disabled, &BTreeSet::from(["strict".to_owned()]));
        assert!(!inherited.strict);
        assert!(inherited.strict_bind_call_apply);
        assert!(inherited.strict_bind_call_apply_specified);
        assert!(inherited.strict_builtin_iterator_return);
        assert!(inherited.strict_builtin_iterator_return_specified);
        assert!(inherited.strict_function_types);
        assert!(inherited.strict_function_types_specified);
        assert!(inherited.strict_null_checks);
        assert!(inherited.strict_property_initialization);

        let mut implied = defaults;
        implied.apply_overrides(&disabled, &BTreeSet::from(["strict".to_owned()]));
        assert!(!implied.no_implicit_any);
        assert!(!implied.no_implicit_this);
        assert!(!implied.strict_bind_call_apply);
        assert!(!implied.strict_builtin_iterator_return);
        assert!(!implied.strict_function_types);
        assert!(!implied.strict_null_checks);
        assert!(!implied.strict_property_initialization);
        assert!(!implied.use_unknown_in_catch_variables);

        let explicit_false = parse_compiler_options(&object([
            ("strict", JsonValue::Bool(true)),
            ("strictBindCallApply", JsonValue::Bool(false)),
            ("strictFunctionTypes", JsonValue::Bool(false)),
        ]));
        assert!(explicit_false.is_ok(), "{:?}", explicit_false.diagnostics);
        assert!(!explicit_false.options.strict_bind_call_apply);
        assert!(explicit_false.options.strict_bind_call_apply_specified);
        assert!(!explicit_false.options.strict_function_types);
        assert!(explicit_false.options.strict_function_types_specified);

        let mut iterator_explicit_false = parse_compiler_options(&object([
            ("strict", JsonValue::Bool(false)),
            ("strictBuiltinIteratorReturn", JsonValue::Bool(false)),
        ]))
        .options;
        iterator_explicit_false.apply_overrides(
            &CompilerOptions::default(),
            &BTreeSet::from(["strict".to_owned()]),
        );
        assert!(iterator_explicit_false.strict);
        assert!(!iterator_explicit_false.strict_builtin_iterator_return);
        assert!(iterator_explicit_false.strict_builtin_iterator_return_specified);

        let mut function_types_explicit_false = parse_compiler_options(&object([
            ("strict", JsonValue::Bool(false)),
            ("strictFunctionTypes", JsonValue::Bool(false)),
        ]))
        .options;
        function_types_explicit_false.apply_overrides(
            &CompilerOptions::default(),
            &BTreeSet::from(["strict".to_owned()]),
        );
        assert!(function_types_explicit_false.strict);
        assert!(!function_types_explicit_false.strict_function_types);
        assert!(function_types_explicit_false.strict_function_types_specified);
    }

    #[test]
    fn preserves_explicit_no_implicit_this_when_strict_changes() {
        let mut implicit_this_explicit_false = parse_compiler_options(&object([
            ("strict", JsonValue::Bool(false)),
            ("noImplicitThis", JsonValue::Bool(false)),
        ]))
        .options;
        implicit_this_explicit_false.apply_overrides(
            &CompilerOptions::default(),
            &BTreeSet::from(["strict".to_owned()]),
        );
        assert!(implicit_this_explicit_false.strict);
        assert!(!implicit_this_explicit_false.no_implicit_this);
        assert!(implicit_this_explicit_false.no_implicit_this_specified);
    }

    #[test]
    fn normalizes_directly_constructed_strict_false_options() {
        let mut options = CompilerOptions {
            strict: false,
            ..CompilerOptions::default()
        };

        options.normalize_strict_flags();

        assert!(!options.no_implicit_any);
        assert!(!options.no_implicit_this);
        assert!(!options.strict_bind_call_apply);
        assert!(!options.strict_builtin_iterator_return);
        assert!(!options.strict_function_types);
        assert!(!options.strict_null_checks);
        assert!(!options.strict_property_initialization);
        assert!(!options.use_unknown_in_catch_variables);
    }

    #[test]
    fn strict_flag_normalization_preserves_explicit_individual_overrides() {
        let mut disabled = parse_compiler_options(&object([
            ("strict", JsonValue::Bool(false)),
            ("noImplicitThis", JsonValue::Bool(true)),
            ("strictNullChecks", JsonValue::Bool(true)),
            ("strictPropertyInitialization", JsonValue::Bool(true)),
        ]))
        .options;
        disabled.normalize_strict_flags();
        assert!(!disabled.no_implicit_any);
        assert!(disabled.no_implicit_this);
        assert!(disabled.strict_null_checks);
        assert!(disabled.strict_property_initialization);

        let mut enabled = parse_compiler_options(&object([
            ("strict", JsonValue::Bool(true)),
            ("strictFunctionTypes", JsonValue::Bool(false)),
            ("useUnknownInCatchVariables", JsonValue::Bool(false)),
        ]))
        .options;
        enabled.normalize_strict_flags();
        assert!(enabled.no_implicit_any);
        assert!(!enabled.strict_function_types);
        assert!(!enabled.use_unknown_in_catch_variables);
    }

    #[test]
    fn always_strict_defaults_true_and_accepts_an_explicit_false() {
        let defaults = parse_compiler_options(&object([]));
        assert!(defaults.is_ok());
        assert!(defaults.options.always_strict);
        assert!(defaults.options.printer_settings().always_strict);

        let disabled = parse_compiler_options(&object([("alwaysStrict", JsonValue::Bool(false))]));
        assert!(disabled.is_ok());
        assert!(!disabled.options.always_strict);
    }

    #[test]
    fn distinguishes_an_unspecified_jsx_mode_from_explicit_preserve() {
        let defaults = parse_compiler_options(&object([]));
        assert_eq!(defaults.options.jsx, JsxEmit::None);

        let preserve =
            parse_compiler_options(&object([("jsx", JsonValue::String("preserve".into()))]));
        assert_eq!(preserve.options.jsx, JsxEmit::Preserve);
    }

    #[test]
    fn selects_automatic_jsx_runtime_and_classic_factory_namespaces() {
        let automatic =
            parse_compiler_options(&object([("jsx", JsonValue::String("react-jsx".into()))]));
        assert!(automatic.is_ok(), "{:?}", automatic.diagnostics);
        assert_eq!(
            automatic.options.jsx_runtime_module_specifier().as_deref(),
            Some("react/jsx-runtime")
        );

        let development = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react-jsxdev".into())),
            ("jsxImportSource", JsonValue::String("preact".into())),
        ]));
        assert!(development.is_ok(), "{:?}", development.diagnostics);
        assert_eq!(
            development
                .options
                .jsx_runtime_module_specifier()
                .as_deref(),
            Some("preact/jsx-dev-runtime")
        );

        let classic = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react".into())),
            (
                "jsxFactory",
                JsonValue::String("MyLibrary.createElement".into()),
            ),
        ]));
        assert!(classic.is_ok(), "{:?}", classic.diagnostics);
        assert!(classic.options.jsx_runtime_module_specifier().is_none());
        assert_eq!(classic.options.jsx_factory_namespace(), "MyLibrary");

        let namespace = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react".into())),
            ("reactNamespace", JsonValue::String("Preact".into())),
        ]));
        assert!(namespace.is_ok(), "{:?}", namespace.diagnostics);
        assert_eq!(namespace.options.jsx_factory_namespace(), "Preact");
        assert_eq!(CompilerOptions::default().jsx_factory_namespace(), "React");
    }

    #[test]
    fn source_jsx_pragmas_override_configured_runtime_and_import_source() {
        let classic =
            parse_compiler_options(&object([("jsx", JsonValue::String("react".into()))])).options;
        assert_eq!(
            classic
                .jsx_runtime_module_specifier_for_source(Some("automatic"), None)
                .as_deref(),
            Some("react/jsx-runtime")
        );
        assert_eq!(
            classic
                .jsx_runtime_module_specifier_for_source(None, Some("@emotion/react"))
                .as_deref(),
            Some("@emotion/react/jsx-runtime")
        );

        let automatic = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react-jsx".into())),
            ("jsxImportSource", JsonValue::String("preact".into())),
        ]))
        .options;
        assert!(
            automatic
                .jsx_runtime_module_specifier_for_source(Some("classic"), None)
                .is_none()
        );
        assert_eq!(
            automatic
                .jsx_runtime_module_specifier_for_source(None, Some("solid-js"))
                .as_deref(),
            Some("solid-js/jsx-runtime")
        );

        let development =
            parse_compiler_options(&object([("jsx", JsonValue::String("react-jsxdev".into()))]))
                .options;
        assert_eq!(
            development
                .jsx_runtime_module_specifier_for_source(Some("automatic"), Some("custom"))
                .as_deref(),
            Some("custom/jsx-dev-runtime")
        );

        let preserved = parse_compiler_options(&object([
            ("jsx", JsonValue::String("preserve".into())),
            (
                "jsxImportSource",
                JsonValue::String("@emotion/react".into()),
            ),
        ]))
        .options;
        assert_eq!(
            preserved.jsx_runtime_module_specifier().as_deref(),
            Some("@emotion/react/jsx-runtime")
        );
    }

    #[test]
    fn source_jsx_factory_pragmas_select_element_and_fragment_namespaces() {
        let configured = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react".into())),
            (
                "jsxFactory",
                JsonValue::String("Configured.createElement".into()),
            ),
            (
                "jsxFragmentFactory",
                JsonValue::String("ConfiguredFragment.Fragment".into()),
            ),
        ]))
        .options;

        assert_eq!(configured.jsx_factory_namespace(), "Configured");
        assert_eq!(
            configured.jsx_factory_namespace_for_source(Some("Local.createElement"), None, false),
            "Local"
        );
        assert_eq!(
            configured.jsx_factory_namespace_for_source(None, None, true),
            "ConfiguredFragment"
        );
        assert_eq!(
            configured.jsx_factory_namespace_for_source(
                Some("Local.createElement"),
                Some("LocalFragment.Fragment"),
                true
            ),
            "LocalFragment"
        );

        let null_fragment = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react".into())),
            ("jsxFactory", JsonValue::String("h".into())),
            ("jsxFragmentFactory", JsonValue::String("null".into())),
        ]))
        .options;
        assert_eq!(
            null_fragment.jsx_factory_namespace_for_source(None, None, true),
            "null"
        );
    }

    #[test]
    fn invalid_fragment_factories_fall_back_to_the_valid_classic_factory() {
        let invalid = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react".into())),
            ("jsxFactory", JsonValue::String("h".into())),
            ("jsxFragmentFactory", JsonValue::String("234".into())),
        ]));
        assert_eq!(invalid.diagnostics.len(), 1);
        assert_eq!(invalid.diagnostics[0].code(), 18_035);
        assert_eq!(
            invalid
                .options
                .jsx_factory_namespace_for_source(None, None, true),
            "h"
        );

        let valid = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react".into())),
            ("jsxFactory", JsonValue::String("h".into())),
            (
                "jsxFragmentFactory",
                JsonValue::String("Fragments.Fragment".into()),
            ),
        ]));
        assert!(valid.is_ok(), "{:?}", valid.diagnostics);
        assert_eq!(
            valid
                .options
                .jsx_factory_namespace_for_source(None, None, true),
            "Fragments"
        );
        assert_eq!(
            valid
                .options
                .jsx_factory_namespace_for_source(None, Some("234"), true),
            "Fragments"
        );
    }

    #[test]
    fn validates_classic_jsx_factories_and_preserves_null_fragment_factories() {
        let invalid_factory = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react".into())),
            ("jsxFactory", JsonValue::String("234".into())),
        ]));
        assert_eq!(invalid_factory.diagnostics.len(), 1);
        assert_eq!(invalid_factory.diagnostics[0].code(), 5067);

        let invalid_fragment = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react".into())),
            ("jsxFactory", JsonValue::String("h".into())),
            ("jsxFragmentFactory", JsonValue::String("234".into())),
        ]));
        assert_eq!(invalid_fragment.diagnostics.len(), 1);
        assert_eq!(invalid_fragment.diagnostics[0].code(), 18_035);

        let null_fragment = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react".into())),
            ("jsxFactory", JsonValue::String("h".into())),
            ("jsxFragmentFactory", JsonValue::String("null".into())),
        ]));
        assert!(null_fragment.is_ok(), "{:?}", null_fragment.diagnostics);

        let invalid_namespace = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react".into())),
            ("reactNamespace", JsonValue::String("React.Factory".into())),
        ]));
        assert_eq!(invalid_namespace.diagnostics.len(), 1);
        assert_eq!(invalid_namespace.diagnostics[0].code(), 5059);
    }

    #[test]
    fn rejects_conflicting_classic_and_automatic_jsx_options() {
        let fragment_without_factory = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react".into())),
            ("jsxFragmentFactory", JsonValue::String("Fragment".into())),
        ]));
        assert_eq!(fragment_without_factory.diagnostics.len(), 1);
        assert_eq!(fragment_without_factory.diagnostics[0].code(), 5052);

        let automatic_factory = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react-jsx".into())),
            ("jsxFactory", JsonValue::String("h".into())),
        ]));
        assert_eq!(automatic_factory.diagnostics.len(), 1);
        assert_eq!(automatic_factory.diagnostics[0].code(), 5089);

        let classic_import_source = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react".into())),
            ("jsxImportSource", JsonValue::String("preact".into())),
        ]));
        assert_eq!(classic_import_source.diagnostics.len(), 1);
        assert_eq!(classic_import_source.diagnostics[0].code(), 5089);

        let duplicate_classic_factories = parse_compiler_options(&object([
            ("jsx", JsonValue::String("react".into())),
            ("jsxFactory", JsonValue::String("h".into())),
            ("reactNamespace", JsonValue::String("React".into())),
        ]));
        assert_eq!(duplicate_classic_factories.diagnostics.len(), 1);
        assert_eq!(duplicate_classic_factories.diagnostics[0].code(), 5053);
    }

    #[test]
    fn parses_and_applies_preserve_const_enums() {
        let defaults = parse_compiler_options(&object([]));
        assert!(!defaults.options.preserve_const_enums);

        let enabled =
            parse_compiler_options(&object([("PreserveConstEnums", JsonValue::Bool(true))]));
        assert!(enabled.is_ok(), "{:?}", enabled.diagnostics);
        assert!(enabled.options.preserve_const_enums);

        let mut applied = CompilerOptions::default();
        applied.apply_overrides(
            &enabled.options,
            &BTreeSet::from(["preserveconstenums".to_owned()]),
        );
        assert!(applied.preserve_const_enums);

        let invalid = parse_compiler_options(&object([(
            "preserveConstEnums",
            JsonValue::String("yes".into()),
        )]));
        assert_eq!(
            invalid
                .diagnostics
                .iter()
                .map(ts_diagnostics::Diagnostic::code)
                .collect::<Vec<_>>(),
            [5024]
        );
    }

    #[test]
    fn reports_catalog_diagnostics_and_keeps_defaults() {
        let result = parse_compiler_options(&object([
            ("allowJs", JsonValue::String("yes".into())),
            ("target", JsonValue::String("future".into())),
            ("mystery", JsonValue::Bool(true)),
        ]));
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(ts_diagnostics::Diagnostic::code)
                .collect::<Vec<_>>(),
            [5024, 5023, 6046]
        );
        assert_eq!(result.options.target, ScriptTarget::Es5);
        assert!(!result.options.allow_js);
    }

    #[test]
    fn parses_project_config_and_converts_resolution_settings() {
        let config = parse_config_text(
            "/repo/tsconfig.json",
            r#"{"compilerOptions":{"allowArbitraryExtensions":true,"allowJs":true,"resolveJsonModule":true,"moduleResolution":"Bundler","baseUrl":".","paths":{"@app/*":["src/*"]},"rootDirs":["src","generated"],"typeRoots":["types","/shared/types"],"types":["node","jest"]}}"#,
        )
        .value
        .unwrap();
        let result = parse_project_options(&config);
        assert_eq!(
            result.options.module_resolution_options(),
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                allow_arbitrary_extensions: true,
                allow_javascript: true,
                resolve_json: true,
                base_url: Some("/repo".into()),
                paths: BTreeMap::from([("@app/*".into(), vec!["src/*".into()])]),
                root_dirs: vec!["/repo/src".into(), "/repo/generated".into()],
                type_roots: Some(vec!["/repo/types".into(), "/shared/types".into()]),
                types: Some(vec!["node".into(), "jest".into()]),
                ..ResolutionOptions::default()
            }
        );
    }

    #[test]
    fn validates_path_mapping_patterns_and_substitutions_with_upstream_codes() {
        let config = parse_config_text(
            "/repo/tsconfig.json",
            r#"{
                "compilerOptions": {
                    "paths": {
                        "*broken*": ["./src/*/nested/*"],
                        "empty": [],
                        "number": [1],
                        "scalar": "./src/*",
                        "valid/*": ["./src/*"]
                    }
                }
            }"#,
        )
        .value
        .unwrap();
        let result = parse_project_options(&config);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(ts_diagnostics::Diagnostic::code)
                .collect::<Vec<_>>(),
            [5061, 5062, 5066, 5064, 5063]
        );
        assert_eq!(
            result.diagnostics[0].render().unwrap(),
            "Pattern '*broken*' can have at most one '*' character."
        );
        assert_eq!(
            result.diagnostics[1].render().unwrap(),
            "Substitution './src/*/nested/*' in pattern '*broken*' can have at most one '*' character."
        );
        assert_eq!(
            result.diagnostics[2].render().unwrap(),
            "Substitutions for pattern 'empty' shouldn't be an empty array."
        );
        assert_eq!(
            result.diagnostics[3].render().unwrap(),
            "Substitution '1' for pattern 'number' has incorrect type, expected 'string', got 'number'."
        );
        assert_eq!(
            result.diagnostics[4].render().unwrap(),
            "Substitutions for pattern 'scalar' should be an array."
        );
        assert_eq!(
            result.options.paths.get("valid/*"),
            Some(&vec!["./src/*".to_owned()])
        );
        assert!(!result.options.paths.contains_key("scalar"));
    }

    #[test]
    fn path_mapping_type_diagnostics_preserve_valid_sibling_entries() {
        let config = parse_config_text(
            "/repo/tsconfig.json",
            r#"{
                "compilerOptions": {
                    "paths": {
                        "mixed": [true, "./valid.ts", null],
                        "valid": ["./other.ts"]
                    }
                }
            }"#,
        )
        .value
        .unwrap();
        let result = parse_project_options(&config);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(ts_diagnostics::Diagnostic::code)
                .collect::<Vec<_>>(),
            [5064, 5064]
        );
        assert_eq!(
            result.options.paths.get("mixed"),
            Some(&vec!["./valid.ts".to_owned()])
        );
        assert_eq!(
            result.options.paths.get("valid"),
            Some(&vec!["./other.ts".to_owned()])
        );
    }

    #[test]
    fn preserves_explicit_package_json_resolution_options() {
        let disabled = parse_compiler_options(&object([
            ("moduleResolution", JsonValue::String("bundler".into())),
            ("resolvePackageJsonExports", JsonValue::Bool(false)),
            ("resolvePackageJsonImports", JsonValue::Bool(false)),
        ]));
        assert!(disabled.is_ok(), "{:?}", disabled.diagnostics);
        assert!(!disabled.options.resolve_package_json_exports);
        assert!(!disabled.options.resolve_package_json_imports);
        assert!(
            !disabled
                .options
                .module_resolution_options()
                .resolve_package_json_exports
        );
        assert!(
            !disabled
                .options
                .module_resolution_options()
                .resolve_package_json_imports
        );

        let mut defaults = CompilerOptions::default();
        defaults.apply_overrides(
            &disabled.options,
            &BTreeSet::from([
                "resolvepackagejsonexports".to_owned(),
                "resolvepackagejsonimports".to_owned(),
            ]),
        );
        assert!(!defaults.resolve_package_json_exports);
        assert!(!defaults.resolve_package_json_imports);
    }

    #[test]
    fn passes_custom_conditions_and_ordered_suffixes_to_module_resolution() {
        let config = parse_config_text(
            "/repo/tsconfig.json",
            r#"{
                "compilerOptions": {
                    "moduleResolution": "bundler",
                    "customConditions": ["development", "browser"],
                    "moduleSuffixes": [".native", ""]
                }
            }"#,
        )
        .value
        .unwrap();
        let parsed = parse_project_options(&config);
        assert!(parsed.is_ok(), "{:?}", parsed.diagnostics);

        let resolution = parsed.options.module_resolution_options();
        assert_eq!(resolution.custom_conditions, ["development", "browser"]);
        assert_eq!(resolution.module_suffixes, [".native", ""]);

        let defaults = CompilerOptions::default().module_resolution_options();
        assert!(defaults.custom_conditions.is_empty());
        assert!(defaults.module_suffixes.is_empty());
    }

    #[test]
    fn validates_conflicting_and_paired_options() {
        let result = parse_compiler_options(&object([
            ("module", JsonValue::String("NodeNext".into())),
            ("moduleResolution", JsonValue::String("Node16".into())),
            ("noEmit", JsonValue::Bool(true)),
            ("emitDeclarationOnly", JsonValue::Bool(true)),
        ]));
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(ts_diagnostics::Diagnostic::code)
                .collect::<Vec<_>>(),
            [5053, 5109]
        );
    }

    #[test]
    fn parses_and_normalizes_emit_path_options() {
        let config = parse_config_text(
            "/repo/tsconfig.json",
            r#"{
                "compilerOptions": {
                    "outDir": "dist",
                    "rootDir": "src",
                    "declarationDir": "types",
                    "declarationMap": true,
                    "inlineSourceMap": true,
                    "tsBuildInfoFile": ".cache/project.tsbuildinfo"
                }
            }"#,
        )
        .value
        .unwrap();
        let result = parse_project_options(&config);
        assert!(result.diagnostics.is_empty());
        assert_eq!(result.options.out_dir.as_deref(), Some("/repo/dist"));
        assert_eq!(result.options.root_dir.as_deref(), Some("/repo/src"));
        assert_eq!(
            result.options.declaration_dir.as_deref(),
            Some("/repo/types")
        );
        assert!(result.options.declaration_map);
        assert!(result.options.inline_source_map);
        assert_eq!(
            result.options.ts_build_info_file.as_deref(),
            Some("/repo/.cache/project.tsbuildinfo")
        );
        assert!(result.options.printer_settings().source_map);
    }

    #[test]
    fn normalizes_map_roots_and_declaration_selection_options() {
        let config = parse_config_text(
            "/repo/tsconfig.json",
            r#"{
                "compilerOptions": {
                    "composite": true,
                    "isolatedDeclarations": true,
                    "mapRoot": "maps",
                    "sourceRoot": "sources"
                }
            }"#,
        )
        .value
        .unwrap();
        let result = parse_project_options(&config);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert!(result.options.declaration);
        assert!(result.options.isolated_declarations);
        assert_eq!(result.options.map_root.as_deref(), Some("/repo/maps"));
        assert_eq!(result.options.source_root.as_deref(), Some("sources"));
    }

    #[test]
    fn parses_and_resolves_out_file() {
        let config = parse_config_text(
            "/repo/tsconfig.json",
            r#"{
                "compilerOptions": {
                    "module": "amd",
                    "outFile": "dist/bundle.js"
                }
            }"#,
        )
        .value
        .unwrap();
        let result = parse_project_options(&config);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert_eq!(
            result.options.out_file.as_deref(),
            Some("/repo/dist/bundle.js")
        );
        assert_eq!(result.options.module, ModuleKind::Amd);

        let invalid = parse_compiler_options(&object([
            ("module", JsonValue::String("commonjs".into())),
            ("outFile", JsonValue::String("bundle.js".into())),
        ]));
        assert_eq!(
            invalid
                .diagnostics
                .iter()
                .map(ts_diagnostics::Diagnostic::code)
                .collect::<Vec<_>>(),
            [6082]
        );
    }

    #[test]
    fn rejects_external_and_inline_source_maps_together() {
        let result = parse_compiler_options(&object([
            ("sourceMap", JsonValue::Bool(true)),
            ("inlineSourceMap", JsonValue::Bool(true)),
        ]));
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(result.diagnostics[0].code(), 5053);
    }

    #[test]
    fn parses_default_library_controls() {
        let result = parse_compiler_options(&object([(
            "lib",
            JsonValue::Array(vec![
                JsonValue::String("ES2015".into()),
                JsonValue::String("DOM".into()),
            ]),
        )]));
        assert_eq!(
            result.options.lib,
            Some(vec!["ES2015".into(), "DOM".into()])
        );
        let conflict = parse_compiler_options(&object([
            ("noLib", JsonValue::Bool(true)),
            (
                "lib",
                JsonValue::Array(vec![JsonValue::String("ES5".into())]),
            ),
        ]));
        assert_eq!(conflict.diagnostics.len(), 1);
        assert_eq!(conflict.diagnostics[0].code(), 5053);
    }
}
