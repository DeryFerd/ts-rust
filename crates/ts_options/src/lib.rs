//! Typed compiler option parsing and normalization.

use std::collections::BTreeMap;

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

/// Normalized compiler options consumed by compiler subsystems.
#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(clippy::struct_excessive_bools)]
pub struct CompilerOptions {
    pub allow_js: bool,
    pub check_js: bool,
    pub declaration: bool,
    pub emit_declaration_only: bool,
    pub no_emit: bool,
    pub module: ModuleKind,
    pub module_resolution: ModuleResolutionKind,
    pub target: ScriptTarget,
    pub jsx: JsxEmit,
    pub resolve_json_module: bool,
}

impl Default for CompilerOptions {
    fn default() -> Self {
        Self {
            allow_js: false,
            check_js: false,
            declaration: false,
            emit_declaration_only: false,
            no_emit: false,
            module: ModuleKind::CommonJs,
            module_resolution: ModuleResolutionKind::Node10,
            target: ScriptTarget::Es5,
            jsx: JsxEmit::Preserve,
            resolve_json_module: false,
        }
    }
}

/// Emitter-facing settings derived from normalized compiler options.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PrinterSettings {
    pub target: ScriptTarget,
    pub module: ModuleKind,
    pub jsx: JsxEmit,
    pub emit_javascript: bool,
    pub emit_declarations: bool,
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
    /// Converts these options to the module resolver's settings.
    #[must_use]
    pub const fn module_resolution_options(&self) -> ResolutionOptions {
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
        }
    }

    /// Converts these options to settings used when invoking the printer.
    #[must_use]
    pub const fn printer_settings(&self) -> PrinterSettings {
        PrinterSettings {
            target: self.target,
            module: self.module,
            jsx: self.jsx,
            emit_javascript: !self.no_emit && !self.emit_declaration_only,
            emit_declarations: !self.no_emit && self.declaration,
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
    parse_compiler_options_map(&config.compiler_options)
}

/// Parses and normalizes a map of compiler option values.
#[must_use]
pub fn parse_compiler_options_map(options: &BTreeMap<String, JsonValue>) -> ParseOptionsResult {
    let mut parsed = PartialOptions::default();
    let mut diagnostics = Vec::new();
    for (original_name, value) in options {
        let name = original_name.to_ascii_lowercase();
        match name.as_str() {
            "allowjs" => parsed.allow_js = boolean(original_name, value, &mut diagnostics),
            "checkjs" => parsed.check_js = boolean(original_name, value, &mut diagnostics),
            "declaration" => {
                parsed.declaration = boolean(original_name, value, &mut diagnostics);
            }
            "emitdeclarationonly" => {
                parsed.emit_declaration_only = boolean(original_name, value, &mut diagnostics);
            }
            "noemit" => parsed.no_emit = boolean(original_name, value, &mut diagnostics),
            "resolvejsonmodule" => {
                parsed.resolve_json_module = boolean(original_name, value, &mut diagnostics);
            }
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
    allow_js: Option<bool>,
    check_js: Option<bool>,
    declaration: Option<bool>,
    emit_declaration_only: Option<bool>,
    no_emit: Option<bool>,
    module: Option<ModuleKind>,
    module_resolution: Option<ModuleResolutionKind>,
    target: Option<ScriptTarget>,
    jsx: Option<JsxEmit>,
    resolve_json_module: Option<bool>,
}

impl PartialOptions {
    fn normalize(self) -> CompilerOptions {
        let check_js = self.check_js.unwrap_or(false);
        let emit_declaration_only = self.emit_declaration_only.unwrap_or(false);
        let module = self.module.unwrap_or_default();
        CompilerOptions {
            allow_js: self.allow_js.unwrap_or(check_js),
            check_js,
            declaration: self.declaration.unwrap_or(emit_declaration_only),
            emit_declaration_only,
            no_emit: self.no_emit.unwrap_or(false),
            module,
            module_resolution: self
                .module_resolution
                .unwrap_or_else(|| default_module_resolution(module)),
            target: self.target.unwrap_or_default(),
            jsx: self.jsx.unwrap_or_default(),
            resolve_json_module: self.resolve_json_module.unwrap_or(false),
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
        CompilerOptions, JsxEmit, ModuleKind, ModuleResolutionKind, ScriptTarget,
        parse_compiler_options, parse_project_options,
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
            ("TARGET", JsonValue::String("ES2022".into())),
            ("Module", JsonValue::String("NodeNext".into())),
            ("JsX", JsonValue::String("React-JSX".into())),
        ]));
        assert!(result.is_ok());
        assert_eq!(result.options.target, ScriptTarget::Es2022);
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
            ("emitDeclarationOnly", JsonValue::Bool(true)),
        ]));
        assert!(result.options.allow_js);
        assert!(result.options.declaration);
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
            r#"{"compilerOptions":{"allowJs":true,"resolveJsonModule":true,"moduleResolution":"Bundler"}}"#,
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
                prefer_types: true,
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
}
