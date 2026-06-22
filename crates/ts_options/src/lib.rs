//! Typed compiler option parsing and normalization.

use std::collections::{BTreeMap, BTreeSet};

use ts_config::{JsonValue, ProjectConfig};
use ts_diagnostics::{Diagnostic, message_by_code};
use ts_module::{ResolutionMode, ResolutionOptions};

/// JavaScript module format used by the emitter.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ModuleKind {
    None,
    #[default]
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

/// Normalized compiler options consumed by compiler subsystems.
#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(clippy::struct_excessive_bools)]
pub struct CompilerOptions {
    pub always_strict: bool,
    pub allow_js: bool,
    pub allow_unreachable_code: Option<bool>,
    pub allow_synthetic_default_imports: bool,
    pub check_js: bool,
    pub composite: bool,
    pub declaration: bool,
    pub declaration_map: bool,
    pub emit_declaration_only: bool,
    pub es_module_interop: bool,
    pub force_consistent_casing_in_file_names: bool,
    pub isolated_modules: bool,
    pub module_detection: ModuleDetectionKind,
    pub no_check: bool,
    pub no_emit: bool,
    pub no_emit_on_error: bool,
    pub no_implicit_any: bool,
    pub no_implicit_returns: bool,
    pub no_lib: bool,
    pub no_fallthrough_cases_in_switch: bool,
    pub no_unused_locals: bool,
    pub no_unused_parameters: bool,
    pub skip_lib_check: bool,
    pub strict: bool,
    pub strict_null_checks: bool,
    pub use_unknown_in_catch_variables: bool,
    pub verbatim_module_syntax: bool,
    pub lib: Option<Vec<String>>,
    pub module: ModuleKind,
    pub module_resolution: ModuleResolutionKind,
    pub target: ScriptTarget,
    pub jsx: JsxEmit,
    pub resolve_json_module: bool,
    pub source_map: bool,
    pub inline_source_map: bool,
    pub incremental: bool,
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
    fn default() -> Self {
        Self {
            always_strict: true,
            allow_js: false,
            allow_unreachable_code: None,
            allow_synthetic_default_imports: false,
            check_js: false,
            composite: false,
            declaration: false,
            declaration_map: false,
            emit_declaration_only: false,
            es_module_interop: false,
            force_consistent_casing_in_file_names: false,
            isolated_modules: false,
            module_detection: ModuleDetectionKind::Auto,
            no_check: false,
            no_emit: false,
            no_emit_on_error: false,
            no_implicit_any: false,
            no_implicit_returns: false,
            no_lib: false,
            no_fallthrough_cases_in_switch: false,
            no_unused_locals: false,
            no_unused_parameters: false,
            skip_lib_check: false,
            strict: false,
            strict_null_checks: false,
            use_unknown_in_catch_variables: false,
            verbatim_module_syntax: false,
            lib: None,
            module: ModuleKind::CommonJs,
            module_resolution: ModuleResolutionKind::Node10,
            target: ScriptTarget::Es5,
            jsx: JsxEmit::Preserve,
            resolve_json_module: false,
            source_map: false,
            inline_source_map: false,
            incremental: false,
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
    pub fn apply_overrides(&mut self, overrides: &Self, names: &BTreeSet<String>) {
        for name in names {
            match name.as_str() {
                "alwaysstrict" => self.always_strict = overrides.always_strict,
                "allowjs" => self.allow_js = overrides.allow_js,
                "allowunreachablecode" => {
                    self.allow_unreachable_code = overrides.allow_unreachable_code;
                }
                "allowsyntheticdefaultimports" => {
                    self.allow_synthetic_default_imports =
                        overrides.allow_synthetic_default_imports;
                }
                "checkjs" => {
                    self.check_js = overrides.check_js;
                    if !names.contains("allowjs") {
                        self.allow_js = overrides.allow_js;
                    }
                }
                "declaration" => self.declaration = overrides.declaration,
                "esmoduleinterop" => {
                    self.es_module_interop = overrides.es_module_interop;
                    if !names.contains("allowsyntheticdefaultimports") {
                        self.allow_synthetic_default_imports =
                            overrides.allow_synthetic_default_imports;
                    }
                }
                "forceconsistentcasinginfilenames" => {
                    self.force_consistent_casing_in_file_names =
                        overrides.force_consistent_casing_in_file_names;
                }
                "isolatedmodules" => self.isolated_modules = overrides.isolated_modules,
                "jsx" => self.jsx = overrides.jsx,
                "module" => {
                    self.module = overrides.module;
                    if !names.contains("moduleresolution") {
                        self.module_resolution = overrides.module_resolution;
                    }
                }
                "moduledetection" => self.module_detection = overrides.module_detection,
                "moduleresolution" => self.module_resolution = overrides.module_resolution,
                "nocheck" => self.no_check = overrides.no_check,
                "noemit" => self.no_emit = overrides.no_emit,
                "noemitonerror" => self.no_emit_on_error = overrides.no_emit_on_error,
                "noimplicitany" => self.no_implicit_any = overrides.no_implicit_any,
                "noimplicitreturns" => self.no_implicit_returns = overrides.no_implicit_returns,
                "nolib" => self.no_lib = overrides.no_lib,
                "nofallthroughcasesinswitch" => {
                    self.no_fallthrough_cases_in_switch = overrides.no_fallthrough_cases_in_switch;
                }
                "nounusedlocals" => self.no_unused_locals = overrides.no_unused_locals,
                "nounusedparameters" => self.no_unused_parameters = overrides.no_unused_parameters,
                "outdir" => self.out_dir.clone_from(&overrides.out_dir),
                "rootdir" => self.root_dir.clone_from(&overrides.root_dir),
                "skiplibcheck" => self.skip_lib_check = overrides.skip_lib_check,
                "sourcemap" => self.source_map = overrides.source_map,
                "strict" => {
                    self.strict = overrides.strict;
                    if !names.contains("noimplicitany") {
                        self.no_implicit_any = overrides.no_implicit_any;
                    }
                    if !names.contains("strictnullchecks") {
                        self.strict_null_checks = overrides.strict_null_checks;
                    }
                    if !names.contains("useunknownincatchvariables") {
                        self.use_unknown_in_catch_variables =
                            overrides.use_unknown_in_catch_variables;
                    }
                }
                "strictnullchecks" => self.strict_null_checks = overrides.strict_null_checks,
                "target" => self.target = overrides.target,
                "useunknownincatchvariables" => {
                    self.use_unknown_in_catch_variables = overrides.use_unknown_in_catch_variables;
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
            allow_javascript: self.allow_js,
            resolve_json: self.resolve_json_module,
            prefer_types: true,
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
            emit_declarations: !self.no_emit && self.declaration,
            source_map: (self.source_map || self.inline_source_map)
                && !self.no_emit
                && !self.emit_declaration_only,
            inline_source_map: self.inline_source_map,
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
    let directory = config.path.rsplit_once('/').map_or(".", |(path, _)| path);
    if let Some(base_url) = &mut result.options.base_url
        && !ts_path::is_absolute(base_url)
    {
        *base_url = ts_path::resolve_path(directory, &[base_url]);
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
            "allowjs" => parsed.allow_js = boolean(original_name, value, &mut diagnostics),
            "allowunreachablecode" => {
                parsed.allow_unreachable_code = boolean(original_name, value, &mut diagnostics);
            }
            "allowsyntheticdefaultimports" => {
                parsed.allow_synthetic_default_imports =
                    boolean(original_name, value, &mut diagnostics);
            }
            "checkjs" => parsed.check_js = boolean(original_name, value, &mut diagnostics),
            "composite" => parsed.composite = boolean(original_name, value, &mut diagnostics),
            "declaration" => {
                parsed.declaration = boolean(original_name, value, &mut diagnostics);
            }
            "declarationmap" => {
                parsed.declaration_map = boolean(original_name, value, &mut diagnostics);
            }
            "emitdeclarationonly" => {
                parsed.emit_declaration_only = boolean(original_name, value, &mut diagnostics);
            }
            "esmoduleinterop" => {
                parsed.es_module_interop = boolean(original_name, value, &mut diagnostics);
            }
            "forceconsistentcasinginfilenames" => {
                parsed.force_consistent_casing_in_file_names =
                    boolean(original_name, value, &mut diagnostics);
            }
            "isolatedmodules" => {
                parsed.isolated_modules = boolean(original_name, value, &mut diagnostics);
            }
            "moduledetection" => {
                parsed.module_detection =
                    enum_value(original_name, value, &mut diagnostics, module_detection);
            }
            "nocheck" => parsed.no_check = boolean(original_name, value, &mut diagnostics),
            "noemit" => parsed.no_emit = boolean(original_name, value, &mut diagnostics),
            "noemitonerror" => {
                parsed.no_emit_on_error = boolean(original_name, value, &mut diagnostics);
            }
            "noimplicitany" => {
                parsed.no_implicit_any = boolean(original_name, value, &mut diagnostics);
            }
            "noimplicitreturns" => {
                parsed.no_implicit_returns = boolean(original_name, value, &mut diagnostics);
            }
            "nolib" => parsed.no_lib = boolean(original_name, value, &mut diagnostics),
            "nofallthroughcasesinswitch" => {
                parsed.no_fallthrough_cases_in_switch =
                    boolean(original_name, value, &mut diagnostics);
            }
            "nounusedlocals" => {
                parsed.no_unused_locals = boolean(original_name, value, &mut diagnostics);
            }
            "nounusedparameters" => {
                parsed.no_unused_parameters = boolean(original_name, value, &mut diagnostics);
            }
            "skiplibcheck" => {
                parsed.skip_lib_check = boolean(original_name, value, &mut diagnostics);
            }
            "strict" => parsed.strict = boolean(original_name, value, &mut diagnostics),
            "strictnullchecks" => {
                parsed.strict_null_checks = boolean(original_name, value, &mut diagnostics);
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
            "sourcemap" => parsed.source_map = boolean(original_name, value, &mut diagnostics),
            "inlinesourcemap" => {
                parsed.inline_source_map = boolean(original_name, value, &mut diagnostics);
            }
            "incremental" => parsed.incremental = boolean(original_name, value, &mut diagnostics),
            "outdir" => parsed.out_dir = string(original_name, value, &mut diagnostics),
            "rootdir" => parsed.root_dir = string(original_name, value, &mut diagnostics),
            "declarationdir" => {
                parsed.declaration_dir = string(original_name, value, &mut diagnostics);
            }
            "tsbuildinfofile" => {
                parsed.ts_build_info_file = string(original_name, value, &mut diagnostics);
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
    allow_js: Option<bool>,
    allow_unreachable_code: Option<bool>,
    allow_synthetic_default_imports: Option<bool>,
    check_js: Option<bool>,
    composite: Option<bool>,
    declaration: Option<bool>,
    declaration_map: Option<bool>,
    emit_declaration_only: Option<bool>,
    es_module_interop: Option<bool>,
    force_consistent_casing_in_file_names: Option<bool>,
    isolated_modules: Option<bool>,
    module_detection: Option<ModuleDetectionKind>,
    no_check: Option<bool>,
    no_emit: Option<bool>,
    no_emit_on_error: Option<bool>,
    no_implicit_any: Option<bool>,
    no_implicit_returns: Option<bool>,
    no_lib: Option<bool>,
    no_fallthrough_cases_in_switch: Option<bool>,
    no_unused_locals: Option<bool>,
    no_unused_parameters: Option<bool>,
    skip_lib_check: Option<bool>,
    strict: Option<bool>,
    strict_null_checks: Option<bool>,
    use_unknown_in_catch_variables: Option<bool>,
    verbatim_module_syntax: Option<bool>,
    lib: Option<Vec<String>>,
    module: Option<ModuleKind>,
    module_resolution: Option<ModuleResolutionKind>,
    target: Option<ScriptTarget>,
    jsx: Option<JsxEmit>,
    resolve_json_module: Option<bool>,
    source_map: Option<bool>,
    inline_source_map: Option<bool>,
    incremental: Option<bool>,
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
    fn normalize(self) -> CompilerOptions {
        let check_js = self.check_js.unwrap_or(false);
        let strict = self.strict.unwrap_or(false);
        let emit_declaration_only = self.emit_declaration_only.unwrap_or(false);
        let module = self.module.unwrap_or_default();
        let module_resolution = self
            .module_resolution
            .unwrap_or_else(|| default_module_resolution(module));
        let es_module_interop = self.es_module_interop.unwrap_or(false);
        CompilerOptions {
            always_strict: self.always_strict.unwrap_or(true),
            allow_js: self.allow_js.unwrap_or(check_js),
            allow_unreachable_code: self.allow_unreachable_code,
            allow_synthetic_default_imports: self.allow_synthetic_default_imports.unwrap_or(
                es_module_interop
                    || module == ModuleKind::System
                    || module_resolution == ModuleResolutionKind::Bundler,
            ),
            check_js,
            composite: self.composite.unwrap_or(false),
            declaration: self.declaration.unwrap_or(emit_declaration_only),
            declaration_map: self.declaration_map.unwrap_or(false),
            emit_declaration_only,
            es_module_interop,
            force_consistent_casing_in_file_names: self
                .force_consistent_casing_in_file_names
                .unwrap_or(false),
            isolated_modules: self.isolated_modules.unwrap_or(false),
            module_detection: self.module_detection.unwrap_or_default(),
            no_check: self.no_check.unwrap_or(false),
            no_emit: self.no_emit.unwrap_or(false),
            no_emit_on_error: self.no_emit_on_error.unwrap_or(false),
            no_implicit_any: self.no_implicit_any.unwrap_or(strict),
            no_implicit_returns: self.no_implicit_returns.unwrap_or(false),
            no_lib: self.no_lib.unwrap_or(false),
            no_fallthrough_cases_in_switch: self.no_fallthrough_cases_in_switch.unwrap_or(false),
            no_unused_locals: self.no_unused_locals.unwrap_or(false),
            no_unused_parameters: self.no_unused_parameters.unwrap_or(false),
            skip_lib_check: self.skip_lib_check.unwrap_or(false),
            strict,
            strict_null_checks: self.strict_null_checks.unwrap_or(strict),
            use_unknown_in_catch_variables: self.use_unknown_in_catch_variables.unwrap_or(strict),
            verbatim_module_syntax: self.verbatim_module_syntax.unwrap_or(false),
            lib: self.lib,
            module,
            module_resolution,
            target: self.target.unwrap_or_default(),
            jsx: self.jsx.unwrap_or_default(),
            resolve_json_module: self.resolve_json_module.unwrap_or(false),
            source_map: self.source_map.unwrap_or(false),
            inline_source_map: self.inline_source_map.unwrap_or(false),
            incremental: self.incremental.unwrap_or(false),
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
        ModuleKind::Node16 | ModuleKind::Node18 | ModuleKind::Node20 => {
            ModuleResolutionKind::Node16
        }
        ModuleKind::NodeNext => ModuleResolutionKind::NodeNext,
        ModuleKind::Preserve => ModuleResolutionKind::Bundler,
        _ => ModuleResolutionKind::Node10,
    }
}

fn validate_options(options: &PartialOptions, diagnostics: &mut Vec<Diagnostic>) {
    if options.no_emit == Some(true) && options.emit_declaration_only == Some(true) {
        diagnostics.push(diagnostic(5053, ["emitDeclarationOnly", "noEmit"]));
    }
    if options.source_map == Some(true) && options.inline_source_map == Some(true) {
        diagnostics.push(diagnostic(5053, ["sourceMap", "inlineSourceMap"]));
    }
    if options.no_lib == Some(true) && options.lib.is_some() {
        diagnostics.push(diagnostic(5053, ["lib", "noLib"]));
    }

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
    if let Some(value) = value.as_bool() {
        Some(value)
    } else {
        diagnostics.push(diagnostic(5024, [name, "boolean"]));
        None
    }
}

fn string(name: &str, value: &JsonValue, diagnostics: &mut Vec<Diagnostic>) -> Option<String> {
    if let Some(value) = value.as_str() {
        Some(value.to_owned())
    } else {
        diagnostics.push(diagnostic(5024, [name, "string"]));
        None
    }
}

fn string_array(
    name: &str,
    value: &JsonValue,
    diagnostics: &mut Vec<Diagnostic>,
) -> Option<Vec<String>> {
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
    let Some(object) = value.as_object() else {
        diagnostics.push(diagnostic(5024, [name, "object"]));
        return None;
    };
    let mut result = BTreeMap::new();
    for (pattern, substitutions) in object {
        let Some(substitutions) = substitutions.as_array() else {
            diagnostics.push(diagnostic(5024, [name, "object"]));
            return None;
        };
        let values = substitutions
            .iter()
            .filter_map(JsonValue::as_str)
            .map(str::to_owned)
            .collect::<Vec<_>>();
        if values.len() != substitutions.len() {
            diagnostics.push(diagnostic(5024, [name, "object"]));
            return None;
        }
        result.insert(pattern.clone(), values);
    }
    Some(result)
}

fn enum_value<T>(
    name: &str,
    value: &JsonValue,
    diagnostics: &mut Vec<Diagnostic>,
    parse: fn(&str) -> Option<T>,
) -> Option<T> {
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
        "target" => {
            "'es3', 'es5', 'es2015', 'es2016', 'es2017', 'es2018', 'es2019', 'es2020', 'es2021', 'es2022', 'es2023', 'es2024', 'esnext'"
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
    use std::collections::BTreeMap;

    use ts_config::{JsonValue, parse_config_text};
    use ts_module::{ResolutionMode, ResolutionOptions};

    use super::{
        CompilerOptions, JsxEmit, ModuleDetectionKind, ModuleKind, ModuleResolutionKind,
        ScriptTarget, parse_compiler_options, parse_project_options,
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
    fn parses_names_and_enum_values_case_insensitively() {
        let result = parse_compiler_options(&object([
            ("TARGET", JsonValue::String("ES2025".into())),
            ("Module", JsonValue::String("NodeNext".into())),
            ("JsX", JsonValue::String("React-JSX".into())),
        ]));
        assert!(result.is_ok());
        assert_eq!(result.options.target, ScriptTarget::Es2025);
        assert_eq!(result.options.module, ModuleKind::NodeNext);
        assert_eq!(result.options.jsx, JsxEmit::ReactJsx);
        assert_eq!(
            result.options.module_resolution,
            ModuleResolutionKind::NodeNext
        );
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
    fn normalizes_strict_and_interoperability_options() {
        let result = parse_compiler_options(&object([
            ("strict", JsonValue::Bool(true)),
            ("strictNullChecks", JsonValue::Bool(false)),
            ("allowUnreachableCode", JsonValue::Bool(false)),
            ("noImplicitReturns", JsonValue::Bool(true)),
            ("noFallthroughCasesInSwitch", JsonValue::Bool(true)),
            ("esModuleInterop", JsonValue::Bool(true)),
            ("noUnusedLocals", JsonValue::Bool(true)),
            ("noUnusedParameters", JsonValue::Bool(true)),
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
        assert!(!result.options.strict_null_checks);
        assert_eq!(result.options.allow_unreachable_code, Some(false));
        assert!(result.options.no_implicit_returns);
        assert!(result.options.no_fallthrough_cases_in_switch);
        assert!(result.options.use_unknown_in_catch_variables);
        assert!(result.options.es_module_interop);
        assert!(result.options.allow_synthetic_default_imports);
        assert!(result.options.no_unused_locals);
        assert!(result.options.no_unused_parameters);
        assert!(result.options.skip_lib_check);
        assert!(result.options.verbatim_module_syntax);
        assert!(result.options.isolated_modules);
        assert!(result.options.force_consistent_casing_in_file_names);
        assert_eq!(result.options.module_detection, ModuleDetectionKind::Force);
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
            r#"{"compilerOptions":{"allowJs":true,"resolveJsonModule":true,"moduleResolution":"Bundler","baseUrl":".","paths":{"@app/*":["src/*"]},"rootDirs":["src","generated"],"typeRoots":["types","/shared/types"],"types":["node","jest"]}}"#,
        )
        .value
        .unwrap();
        let result = parse_project_options(&config);
        assert_eq!(
            result.options.module_resolution_options(),
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
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
