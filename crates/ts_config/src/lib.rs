//! JSONC and project configuration foundations for tsconfig files.

mod jsonc;

use std::{collections::BTreeMap, path::Path};

use ts_diagnostics::{Diagnostic, message_by_code};
use ts_vfs::{FileSystem, normalize_path};

pub use jsonc::parse_jsonc;

/// A JSON value which retains compiler option values without interpreting them.
#[derive(Clone, Debug, PartialEq)]
pub enum JsonValue {
    Null,
    Bool(bool),
    Number(JsonNumber),
    String(String),
    Array(Vec<Self>),
    Object(BTreeMap<String, Self>),
}

impl JsonValue {
    #[must_use]
    pub const fn as_object(&self) -> Option<&BTreeMap<String, Self>> {
        if let Self::Object(value) = self {
            Some(value)
        } else {
            None
        }
    }

    #[must_use]
    pub fn as_array(&self) -> Option<&[Self]> {
        if let Self::Array(value) = self {
            Some(value)
        } else {
            None
        }
    }

    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        if let Self::String(value) = self {
            Some(value)
        } else {
            None
        }
    }

    #[must_use]
    pub const fn as_bool(&self) -> Option<bool> {
        if let Self::Bool(value) = self {
            Some(*value)
        } else {
            None
        }
    }
}

/// A JSON number retaining its exact source spelling.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JsonNumber(String);

impl JsonNumber {
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    #[must_use]
    pub fn as_i64(&self) -> Option<i64> {
        self.0.parse().ok()
    }

    #[must_use]
    pub fn as_f64(&self) -> Option<f64> {
        self.0.parse().ok()
    }

    pub(crate) fn new(raw: String) -> Self {
        Self(raw)
    }
}

/// A diagnostic tied to a position in a configuration file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ConfigDiagnostic {
    pub file_name: String,
    pub byte_offset: usize,
    pub diagnostic: Diagnostic,
}

impl ConfigDiagnostic {
    #[must_use]
    pub fn code(&self) -> u32 {
        self.diagnostic.code()
    }

    #[must_use]
    pub fn render(&self) -> String {
        self.diagnostic
            .render()
            .unwrap_or_else(|error| error.to_string())
    }
}

/// Result of parsing JSONC or a project configuration.
#[derive(Clone, Debug, PartialEq)]
pub struct ParseResult<T> {
    pub value: Option<T>,
    pub diagnostics: Vec<ConfigDiagnostic>,
}

impl<T> ParseResult<T> {
    #[must_use]
    pub const fn is_ok(&self) -> bool {
        self.value.is_some() && self.diagnostics.is_empty()
    }
}

/// The shape of the top-level extends property.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Extends {
    Single(String),
    Multiple(Vec<String>),
}

impl Extends {
    pub fn paths(&self) -> impl Iterator<Item = &str> {
        match self {
            Self::Single(path) => std::slice::from_ref(path),
            Self::Multiple(paths) => paths.as_slice(),
        }
        .iter()
        .map(String::as_str)
    }
}

/// One project reference from the references array.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectReference {
    pub path: String,
    pub prepend: Option<bool>,
    pub circular: Option<bool>,
}

/// A parsed tsconfig retaining unrecognized compiler options as typed JSON.
#[derive(Clone, Debug, PartialEq)]
pub struct ProjectConfig {
    pub path: String,
    pub extends: Option<Extends>,
    pub references: Vec<ProjectReference>,
    pub include: Option<Vec<String>>,
    pub exclude: Option<Vec<String>>,
    pub files: Option<Vec<String>>,
    pub compiler_options: BTreeMap<String, JsonValue>,
    pub raw: BTreeMap<String, JsonValue>,
}

impl ProjectConfig {
    fn from_json(path: String, raw: BTreeMap<String, JsonValue>) -> Self {
        let extends = raw.get("extends").and_then(parse_extends);
        let references = raw
            .get("references")
            .and_then(JsonValue::as_array)
            .map(parse_references)
            .unwrap_or_default();
        let include = raw
            .get("include")
            .and_then(string_array)
            .map(|specs| valid_file_specs(specs, true));
        let exclude = raw
            .get("exclude")
            .and_then(string_array)
            .map(|specs| valid_file_specs(specs, false));
        let files = raw.get("files").and_then(string_array);
        let compiler_options = raw
            .get("compilerOptions")
            .and_then(JsonValue::as_object)
            .cloned()
            .unwrap_or_default();
        Self {
            path,
            extends,
            references,
            include,
            exclude,
            files,
            compiler_options,
            raw,
        }
    }

    /// Resolves relative extends paths against the config directory. Package
    /// specifiers are retained for the future module-resolution layer.
    #[must_use]
    pub fn resolved_extends(&self, file_system: &dyn FileSystem) -> Vec<String> {
        self.extends
            .iter()
            .flat_map(Extends::paths)
            .map(|path| resolve_extends_path(file_system, &self.path, path))
            .collect()
    }

    /// Resolves project reference paths relative to this configuration file.
    #[must_use]
    pub fn resolved_references(&self, file_system: &dyn FileSystem) -> Vec<ProjectReference> {
        let directory = config_directory(&self.path);
        self.references
            .iter()
            .map(|reference| {
                let mut path = if is_rooted_path(&reference.path) {
                    normalize_path(&reference.path)
                } else {
                    resolve_relative(directory, &reference.path)
                };
                if file_system.directory_exists(&path) {
                    path = resolve_relative(&path, "tsconfig.json");
                }
                ProjectReference {
                    path,
                    prepend: reference.prepend,
                    circular: reference.circular,
                }
            })
            .collect()
    }
}

/// Parses project configuration source text.
#[must_use]
pub fn parse_config_text(file_name: &str, source: &str) -> ParseResult<ProjectConfig> {
    let parsed = parse_jsonc(file_name, source);
    let Some(value) = parsed.value else {
        return ParseResult {
            value: None,
            diagnostics: parsed.diagnostics,
        };
    };
    let JsonValue::Object(raw) = value else {
        return ParseResult {
            value: None,
            diagnostics: vec![diagnostic(file_name, 0, 1136, std::iter::empty::<String>())],
        };
    };
    let mut diagnostics = parsed.diagnostics;
    validate_project_fields(file_name, &raw, &mut diagnostics);
    ParseResult {
        value: Some(ProjectConfig::from_json(normalize_path(file_name), raw)),
        diagnostics,
    }
}

fn validate_project_fields(
    file_name: &str,
    fields: &BTreeMap<String, JsonValue>,
    diagnostics: &mut Vec<ConfigDiagnostic>,
) {
    if fields.contains_key("excludes") {
        diagnostics.push(diagnostic(file_name, 0, 6114, std::iter::empty::<String>()));
    }

    if let Some(value) = fields.get("compilerOptions")
        && !matches!(value, JsonValue::Null | JsonValue::Object(_))
    {
        diagnostics.push(diagnostic(
            file_name,
            0,
            5024,
            ["compilerOptions".to_owned(), "object".to_owned()],
        ));
    }

    if let Some(value) = fields.get("extends") {
        validate_extends_field(file_name, value, diagnostics);
    }

    for name in ["files", "include", "exclude"] {
        validate_string_list_field(file_name, fields, name, diagnostics);
    }

    if let Some(value) = fields.get("references")
        && !matches!(value, JsonValue::Null)
    {
        let Some(references) = value.as_array() else {
            diagnostics.push(diagnostic(
                file_name,
                0,
                5024,
                ["references".to_owned(), "Array".to_owned()],
            ));
            return;
        };
        for reference in references {
            let Some(reference) = reference.as_object() else {
                diagnostics.push(diagnostic(
                    file_name,
                    0,
                    5024,
                    ["references".to_owned(), "object".to_owned()],
                ));
                continue;
            };
            if reference
                .get("path")
                .and_then(JsonValue::as_str)
                .is_none_or(str::is_empty)
            {
                diagnostics.push(diagnostic(
                    file_name,
                    0,
                    5024,
                    ["reference.path".to_owned(), "string".to_owned()],
                ));
            }
        }
    }
}

fn validate_extends_field(
    file_name: &str,
    value: &JsonValue,
    diagnostics: &mut Vec<ConfigDiagnostic>,
) {
    match value {
        JsonValue::Null => {}
        JsonValue::String(path) => validate_extends_path(file_name, path, diagnostics),
        JsonValue::Array(paths) => {
            for path in paths {
                if let Some(path) = path.as_str() {
                    validate_extends_path(file_name, path, diagnostics);
                } else {
                    diagnostics.push(diagnostic(
                        file_name,
                        0,
                        5024,
                        ["extends".to_owned(), "string".to_owned()],
                    ));
                }
            }
        }
        _ => diagnostics.push(diagnostic(
            file_name,
            0,
            5024,
            ["extends".to_owned(), "string or Array".to_owned()],
        )),
    }
}

fn validate_extends_path(file_name: &str, path: &str, diagnostics: &mut Vec<ConfigDiagnostic>) {
    if path.is_empty() {
        diagnostics.push(diagnostic(file_name, 0, 18_051, ["extends".to_owned()]));
    }
}

fn validate_string_list_field(
    file_name: &str,
    fields: &BTreeMap<String, JsonValue>,
    name: &str,
    diagnostics: &mut Vec<ConfigDiagnostic>,
) {
    let Some(value) = fields.get(name) else {
        return;
    };
    if matches!(value, JsonValue::Null) {
        return;
    }
    let Some(values) = value.as_array() else {
        diagnostics.push(diagnostic(
            file_name,
            0,
            5024,
            [name.to_owned(), "Array".to_owned()],
        ));
        return;
    };
    if values.iter().any(|value| value.as_str().is_none()) {
        diagnostics.push(diagnostic(
            file_name,
            0,
            5024,
            [name.to_owned(), "string".to_owned()],
        ));
    }
    if matches!(name, "include" | "exclude") {
        for value in values.iter().filter_map(JsonValue::as_str) {
            if let Some(code) = invalid_file_spec_code(value, name == "include") {
                diagnostics.push(diagnostic(file_name, 0, code, [value.to_owned()]));
            }
        }
    }
}

/// Reads and parses a project configuration through the compiler VFS.
#[must_use]
pub fn parse_config_file(
    file_system: &dyn FileSystem,
    file_name: &str,
) -> ParseResult<ProjectConfig> {
    let normalized = normalize_path(file_name);
    match file_system.read_file(&normalized) {
        Ok(source) => parse_config_text(&normalized, &source),
        Err(error) => ParseResult {
            value: None,
            diagnostics: vec![diagnostic(
                &normalized,
                0,
                5012,
                [normalized.clone(), error.to_string()],
            )],
        },
    }
}

/// Loads a project configuration and recursively applies all `extends` bases.
/// Later bases override earlier bases, and the leaf configuration overrides
/// every base. Project references are intentionally not inherited. File,
/// include, and exclude entries are normalized relative to the config file
/// which declared them before merging.
#[must_use]
pub fn resolve_config_file(
    file_system: &dyn FileSystem,
    file_name: &str,
) -> ParseResult<ProjectConfig> {
    let mut state = ConfigResolutionState {
        file_system,
        stack: Vec::new(),
        diagnostics: Vec::new(),
    };
    let value = state
        .resolve(&normalize_path(file_name))
        .map(substitute_config_dir_templates)
        .map(apply_default_excludes);
    ParseResult {
        value,
        diagnostics: state.diagnostics,
    }
}

struct ConfigResolutionState<'a> {
    file_system: &'a dyn FileSystem,
    stack: Vec<String>,
    diagnostics: Vec<ConfigDiagnostic>,
}

impl ConfigResolutionState<'_> {
    fn resolve(&mut self, file_name: &str) -> Option<ProjectConfig> {
        let file_name = normalize_path(file_name);
        if let Some(index) = self.stack.iter().position(|path| {
            if self.file_system.use_case_sensitive_file_names() {
                path == &file_name
            } else {
                path.eq_ignore_ascii_case(&file_name)
            }
        }) {
            let mut cycle = self.stack[index..].to_vec();
            cycle.push(file_name.clone());
            self.diagnostics
                .push(diagnostic(&file_name, 0, 18_000, [cycle.join(" -> ")]));
            return None;
        }
        if !self.file_system.file_exists(&file_name) {
            self.diagnostics
                .push(diagnostic(&file_name, 0, 5_083, [file_name.clone()]));
            return None;
        }

        self.stack.push(file_name.clone());
        let parsed = parse_config_file(self.file_system, &file_name);
        self.diagnostics.extend(parsed.diagnostics);
        let Some(config) = parsed.value else {
            self.stack.pop();
            return None;
        };
        let config = resolve_config_patterns(config);

        let mut merged = None;
        if let Some(extends) = &config.extends {
            for extends_path in extends.paths() {
                let Some(base_path) =
                    resolve_base_config_path(self.file_system, &config.path, extends_path)
                else {
                    self.diagnostics.push(diagnostic(
                        &config.path,
                        0,
                        6_053,
                        [extends_path.to_owned()],
                    ));
                    continue;
                };
                if let Some(base) = self.resolve(&base_path) {
                    merged = Some(match merged {
                        Some(previous) => merge_configs(previous, base),
                        None => base,
                    });
                }
            }
        }
        self.stack.pop();
        Some(match merged {
            Some(base) => merge_configs(base, config),
            None => without_extends(config),
        })
    }
}

fn merge_configs(mut base: ProjectConfig, child: ProjectConfig) -> ProjectConfig {
    let ProjectConfig {
        path,
        references,
        include,
        exclude,
        files,
        compiler_options,
        raw,
        ..
    } = child;
    if raw.contains_key("files") {
        base.files = files;
    }
    if raw.contains_key("include") {
        base.include = include;
    }
    if raw.contains_key("exclude") {
        base.exclude = exclude;
    }
    for (name, value) in compiler_options {
        base.compiler_options
            .retain(|existing, _| !existing.eq_ignore_ascii_case(&name));
        base.compiler_options.insert(name, value);
    }
    base.raw.extend(raw);
    base.path = path;
    base.extends = None;
    base.references = references;
    base.raw.remove("extends");
    base.raw.insert(
        "compilerOptions".to_owned(),
        JsonValue::Object(base.compiler_options.clone()),
    );
    base
}

fn without_extends(mut config: ProjectConfig) -> ProjectConfig {
    config.extends = None;
    config.raw.remove("extends");
    config
}

fn resolve_config_patterns(mut config: ProjectConfig) -> ProjectConfig {
    let directory = config_directory(&config.path);
    for values in [&mut config.files, &mut config.include, &mut config.exclude]
        .into_iter()
        .flatten()
    {
        for value in values {
            if !is_rooted_path(value) && config_dir_suffix(value).is_none() {
                *value = resolve_relative(directory, value);
            }
        }
    }
    for (name, value) in &mut config.compiler_options {
        match name.to_ascii_lowercase().as_str() {
            "baseurl" | "outfile" | "outdir" | "rootdir" | "declarationdir" | "tsbuildinfofile"
            | "maproot" => {
                if let JsonValue::String(path) = value
                    && !is_rooted_path(path)
                    && config_dir_suffix(path).is_none()
                {
                    *path = resolve_relative(directory, path);
                }
            }
            "rootdirs" | "typeroots" => {
                if let JsonValue::Array(paths) = value {
                    for path in paths {
                        if let JsonValue::String(path) = path
                            && !is_rooted_path(path)
                            && config_dir_suffix(path).is_none()
                        {
                            *path = resolve_relative(directory, path);
                        }
                    }
                }
            }
            "paths" => {
                if let JsonValue::Object(patterns) = value {
                    for substitutions in patterns.values_mut() {
                        if let JsonValue::Array(substitutions) = substitutions {
                            for substitution in substitutions {
                                if let JsonValue::String(substitution) = substitution
                                    && !is_rooted_path(substitution)
                                    && config_dir_suffix(substitution).is_none()
                                {
                                    *substitution = resolve_relative(directory, substitution);
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
    config
}

fn substitute_config_dir_templates(mut config: ProjectConfig) -> ProjectConfig {
    let directory = config_directory(&config.path).to_owned();
    for values in [&mut config.files, &mut config.include, &mut config.exclude]
        .into_iter()
        .flatten()
    {
        for value in values {
            substitute_config_dir_template(value, &directory);
        }
    }
    for (name, value) in &mut config.compiler_options {
        match name.to_ascii_lowercase().as_str() {
            "baseurl" | "outfile" | "outdir" | "rootdir" | "declarationdir" | "tsbuildinfofile"
            | "maproot" => {
                if let JsonValue::String(value) = value {
                    substitute_config_dir_template(value, &directory);
                }
            }
            "rootdirs" | "typeroots" => {
                if let JsonValue::Array(values) = value {
                    for value in values {
                        if let JsonValue::String(value) = value {
                            substitute_config_dir_template(value, &directory);
                        }
                    }
                }
            }
            "paths" => {
                if let JsonValue::Object(patterns) = value {
                    for substitutions in patterns.values_mut() {
                        if let JsonValue::Array(substitutions) = substitutions {
                            for substitution in substitutions {
                                if let JsonValue::String(substitution) = substitution {
                                    substitute_config_dir_template(substitution, &directory);
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
    if config.raw.contains_key("compilerOptions") {
        config.raw.insert(
            "compilerOptions".to_owned(),
            JsonValue::Object(config.compiler_options.clone()),
        );
    }
    config
}

fn apply_default_excludes(mut config: ProjectConfig) -> ProjectConfig {
    if config.exclude.is_some() {
        return config;
    }

    let mut exclusions = Vec::new();
    for option in ["outDir", "declarationDir"] {
        if let Some(path) = config.compiler_options.iter().find_map(|(name, value)| {
            name.eq_ignore_ascii_case(option)
                .then(|| value.as_str())
                .flatten()
        }) {
            exclusions.push(path.to_owned());
        }
    }
    if !exclusions.is_empty() {
        config.exclude = Some(exclusions);
    }
    config
}

fn substitute_config_dir_template(value: &mut String, directory: &str) {
    if let Some(suffix) = config_dir_suffix(value) {
        let suffix = suffix.trim_start_matches(['/', '\\']);
        *value = resolve_relative(directory, suffix);
    }
}

fn config_dir_suffix(value: &str) -> Option<&str> {
    const TEMPLATE: &str = "${configDir}";
    value
        .get(..TEMPLATE.len())
        .filter(|prefix| prefix.eq_ignore_ascii_case(TEMPLATE))
        .map(|_| &value[TEMPLATE.len()..])
}

fn parse_extends(value: &JsonValue) -> Option<Extends> {
    match value {
        JsonValue::String(path) if !path.is_empty() => Some(Extends::Single(path.clone())),
        JsonValue::Array(values) => Some(Extends::Multiple(
            values
                .iter()
                .filter_map(JsonValue::as_str)
                .filter(|path| !path.is_empty())
                .map(ToOwned::to_owned)
                .collect(),
        )),
        _ => None,
    }
}

fn string_array(value: &JsonValue) -> Option<Vec<String>> {
    value.as_array().map(|values| {
        values
            .iter()
            .filter_map(JsonValue::as_str)
            .map(ToOwned::to_owned)
            .collect()
    })
}

fn valid_file_specs(specs: Vec<String>, disallow_trailing_recursion: bool) -> Vec<String> {
    specs
        .into_iter()
        .filter(|spec| invalid_file_spec_code(spec, disallow_trailing_recursion).is_none())
        .collect()
}

fn invalid_file_spec_code(spec: &str, disallow_trailing_recursion: bool) -> Option<u32> {
    let normalized = spec.replace('\\', "/");
    let without_trailing_slash = normalized.strip_suffix('/').unwrap_or(&normalized);
    if disallow_trailing_recursion
        && (without_trailing_slash == "**" || without_trailing_slash.ends_with("/**"))
    {
        return Some(5010);
    }

    let recursive_index = if normalized.starts_with("**/") {
        Some(0)
    } else {
        normalized.find("/**/")
    };
    let parent_index = if normalized.ends_with("/..") {
        Some(normalized.len())
    } else {
        normalized.rfind("/../")
    };
    if recursive_index
        .zip(parent_index)
        .is_some_and(|(recursive, parent)| parent > recursive)
    {
        return Some(5065);
    }
    None
}

fn parse_references(values: &[JsonValue]) -> Vec<ProjectReference> {
    values
        .iter()
        .filter_map(JsonValue::as_object)
        .filter_map(|reference| {
            Some(ProjectReference {
                path: reference.get("path")?.as_str()?.to_owned(),
                prepend: reference.get("prepend").and_then(JsonValue::as_bool),
                circular: reference.get("circular").and_then(JsonValue::as_bool),
            })
        })
        .collect()
}

fn resolve_extends_path(
    file_system: &dyn FileSystem,
    config_path: &str,
    extends_path: &str,
) -> String {
    if !is_relative_path(extends_path) {
        return normalize_path(extends_path);
    }
    let candidate = resolve_relative(config_directory(config_path), extends_path);
    if file_system.file_exists(&candidate)
        || Path::new(&candidate)
            .extension()
            .is_some_and(|extension| extension.eq_ignore_ascii_case("json"))
    {
        candidate
    } else {
        let with_json = format!("{candidate}.json");
        if file_system.file_exists(&with_json) {
            with_json
        } else {
            candidate
        }
    }
}

fn resolve_base_config_path(
    file_system: &dyn FileSystem,
    config_path: &str,
    extends_path: &str,
) -> Option<String> {
    if is_relative_path(extends_path) || is_rooted_path(extends_path) {
        let candidate = if is_relative_path(extends_path) {
            resolve_relative(config_directory(config_path), extends_path)
        } else {
            normalize_path(extends_path)
        };
        return existing_config_candidate(file_system, &candidate);
    }

    let mut directory = config_directory(config_path).to_owned();
    loop {
        let candidate = resolve_relative(&directory, &format!("node_modules/{extends_path}"));
        if let Some(path) = existing_config_candidate(file_system, &candidate) {
            return Some(path);
        }
        let parent = parent_directory(&directory);
        if parent == directory {
            break;
        }
        directory = parent;
    }
    None
}

fn existing_config_candidate(file_system: &dyn FileSystem, candidate: &str) -> Option<String> {
    let candidate = normalize_path(candidate);
    if file_system.file_exists(&candidate) {
        return Some(candidate);
    }
    if Path::new(&candidate).extension().is_none() {
        let json = format!("{candidate}.json");
        if file_system.file_exists(&json) {
            return Some(json);
        }
    }
    if file_system.directory_exists(&candidate) {
        let package_json = resolve_relative(&candidate, "package.json");
        if file_system.file_exists(&package_json)
            && let Ok(source) = file_system.read_file(&package_json)
            && let Some(value) = parse_jsonc(&package_json, &source).value
            && let Some(tsconfig) = value
                .as_object()
                .and_then(|object| object.get("tsconfig"))
                .and_then(JsonValue::as_str)
        {
            let configured = resolve_relative(&candidate, tsconfig);
            if configured != candidate
                && let Some(configured) = existing_config_candidate(file_system, &configured)
            {
                return Some(configured);
            }
        }
        let tsconfig = resolve_relative(&candidate, "tsconfig.json");
        if file_system.file_exists(&tsconfig) {
            return Some(tsconfig);
        }
    }
    None
}

fn config_directory(path: &str) -> &str {
    match path.rsplit_once('/') {
        Some(("", _)) if path.starts_with('/') => "/",
        Some((directory, _)) => directory,
        None => "",
    }
}

fn resolve_relative(directory: &str, path: &str) -> String {
    if directory.is_empty() {
        normalize_path(path)
    } else if directory == "/" {
        normalize_path(&format!("/{path}"))
    } else {
        normalize_path(&format!("{directory}/{path}"))
    }
}

fn parent_directory(directory: &str) -> String {
    match directory.rsplit_once('/') {
        Some(("", _)) if directory.starts_with('/') => "/".to_owned(),
        Some((parent, _)) => parent.to_owned(),
        None if directory.as_bytes().get(1) == Some(&b':') => directory.to_owned(),
        None => String::new(),
    }
}

fn is_relative_path(path: &str) -> bool {
    path == "." || path == ".." || path.starts_with("./") || path.starts_with("../")
}

fn is_rooted_path(path: &str) -> bool {
    Path::new(path).is_absolute()
        || path.starts_with('\\')
        || (path.as_bytes().get(1) == Some(&b':')
            && path.as_bytes().first().is_some_and(u8::is_ascii_alphabetic))
}

pub(crate) fn diagnostic(
    file_name: &str,
    byte_offset: usize,
    code: u32,
    arguments: impl IntoIterator<Item = String>,
) -> ConfigDiagnostic {
    let message = message_by_code(code).expect("configuration diagnostic must be in the catalog");
    ConfigDiagnostic {
        file_name: file_name.to_owned(),
        byte_offset,
        diagnostic: Diagnostic::with_arguments(message, arguments),
    }
}

#[cfg(test)]
mod tests {
    use ts_vfs::{FileSystem, MemoryFileSystem};

    use super::{
        Extends, JsonValue, parse_config_file, parse_config_text, parse_jsonc, resolve_config_file,
    };

    #[test]
    fn parses_jsonc_project_fields_and_retains_compiler_option_types() {
        let source = r#"{
            // TypeScript permits comments and trailing commas.
            "extends": ["../base", "./shared.json",],
            "references": [
                { "path": "../library", "prepend": true, },
                { "path": "../types", "circular": false }
            ],
            "files": ["src/index.ts",],
            "include": ["src/**/*.ts"],
            "exclude": ["dist", "node_modules"],
            "compilerOptions": {
                "strict": true,
                "target": "esnext",
                "maxNodeModuleJsDepth": 2,
                "plugins": [{ "name": "example" }],
            },
        }"#;

        let result = parse_config_text("/repo/app/tsconfig.json", source);
        assert!(result.is_ok(), "{:?}", result.diagnostics);
        let config = result.value.unwrap();
        assert_eq!(
            config.extends,
            Some(Extends::Multiple(vec![
                "../base".into(),
                "./shared.json".into()
            ]))
        );
        assert_eq!(config.references.len(), 2);
        assert_eq!(config.references[0].path, "../library");
        assert_eq!(config.references[0].prepend, Some(true));
        assert_eq!(config.references[1].circular, Some(false));
        assert_eq!(config.files.unwrap(), ["src/index.ts"]);
        assert_eq!(config.include.unwrap(), ["src/**/*.ts"]);
        assert_eq!(config.exclude.unwrap(), ["dist", "node_modules"]);
        assert_eq!(
            config.compiler_options.get("strict"),
            Some(&JsonValue::Bool(true))
        );
        assert_eq!(
            config
                .compiler_options
                .get("target")
                .and_then(JsonValue::as_str),
            Some("esnext")
        );
        let depth = match config.compiler_options.get("maxNodeModuleJsDepth") {
            Some(JsonValue::Number(number)) => number,
            other => panic!("expected numeric option, got {other:?}"),
        };
        assert_eq!(depth.as_str(), "2");
        assert_eq!(depth.as_i64(), Some(2));
        assert!(matches!(
            config.compiler_options.get("plugins"),
            Some(JsonValue::Array(_))
        ));
    }

    #[test]
    fn reads_through_vfs_and_resolves_relative_extends() {
        let file_system = MemoryFileSystem::default();
        file_system
            .write_file(
                "/repo/app/tsconfig.json",
                r#"{
                    "extends": ["../base", "./shared.json", "@scope/config"],
                    "compilerOptions": { "strict": true }
                }"#,
            )
            .unwrap();
        file_system.write_file("/repo/base.json", "{}").unwrap();
        file_system
            .write_file("/repo/app/shared.json", "{}")
            .unwrap();

        let result = parse_config_file(&file_system, "/repo/app/./tsconfig.json");
        assert!(result.is_ok());
        let config = result.value.unwrap();
        assert_eq!(config.path, "/repo/app/tsconfig.json");
        assert_eq!(
            config.resolved_extends(&file_system),
            ["/repo/base.json", "/repo/app/shared.json", "@scope/config"]
        );
    }

    #[test]
    fn reports_invalid_project_field_types_without_discarding_valid_fields() {
        let result = parse_config_text(
            "/repo/tsconfig.json",
            r#"{
                "compilerOptions": [],
                "extends": ["./base", 1, ""],
                "files": ["index.ts", false],
                "include": "src",
                "exclude": ["dist", null],
                "references": [{ "path": "./lib" }, {}, 1]
            }"#,
        );

        let config = result.value.unwrap();
        assert_eq!(config.files, Some(vec!["index.ts".into()]));
        assert_eq!(config.references.len(), 1);
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(super::ConfigDiagnostic::code)
                .collect::<Vec<_>>(),
            [5024, 5024, 18_051, 5024, 5024, 5024, 5024, 5024]
        );
        assert_eq!(
            result.diagnostics[0].render(),
            "Compiler option 'compilerOptions' requires a value of type object."
        );
        assert_eq!(
            result.diagnostics[2].render(),
            "Compiler option 'extends' cannot be given an empty string."
        );
    }

    #[test]
    fn rejects_invalid_top_level_reference_and_extends_values() {
        let result = parse_config_text(
            "/repo/tsconfig.json",
            r#"{ "extends": true, "references": "./lib" }"#,
        );
        assert_eq!(result.diagnostics.len(), 2);
        assert_eq!(
            result.diagnostics[0].render(),
            "Compiler option 'extends' requires a value of type string or Array."
        );
        assert_eq!(
            result.diagnostics[1].render(),
            "Compiler option 'references' requires a value of type Array."
        );

        let empty = parse_config_text("/repo/tsconfig.json", r#"{ "extends": "" }"#);
        assert_eq!(empty.diagnostics.len(), 1);
        assert_eq!(empty.diagnostics[0].code(), 18_051);
        assert!(empty.value.unwrap().extends.is_none());
    }

    #[test]
    fn rejects_invalid_recursive_file_patterns_without_using_them() {
        let result = parse_config_text(
            "/repo/tsconfig.json",
            r#"{
                "include": ["src/**/*.ts", "generated/**", "**/../outside"],
                "exclude": ["dist/**", "temp/**/../outside"]
            }"#,
        );

        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(super::ConfigDiagnostic::code)
                .collect::<Vec<_>>(),
            [5010, 5065, 5065]
        );
        assert_eq!(
            result.diagnostics[0].render(),
            "File specification cannot end in a recursive directory wildcard ('**'): 'generated/**'."
        );
        assert_eq!(
            result.diagnostics[1].render(),
            "File specification cannot contain a parent directory ('..') that appears after a recursive directory wildcard ('**'): '**/../outside'."
        );

        let config = result.value.unwrap();
        assert_eq!(config.include, Some(vec!["src/**/*.ts".into()]));
        assert_eq!(config.exclude, Some(vec!["dist/**".into()]));
    }

    #[test]
    fn reports_the_common_excludes_typo_with_the_upstream_diagnostic() {
        let result = parse_config_text("/repo/tsconfig.json", r#"{ "excludes": ["dist"] }"#);
        assert!(result.value.is_some());
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(result.diagnostics[0].code(), 6114);
        assert_eq!(
            result.diagnostics[0].render(),
            "Unknown option 'excludes'. Did you mean 'exclude'?"
        );
    }

    #[test]
    fn preserves_number_spelling_and_decodes_unicode() {
        let result = parse_jsonc(
            "tsconfig.json",
            r#"{ "value": -1.25e+3, "name": "\u03b1 \ud83d\ude00" }"#,
        );
        assert!(result.is_ok());
        let object = result.value.unwrap();
        let object = object.as_object().unwrap();
        let JsonValue::Number(number) = &object["value"] else {
            panic!("expected number");
        };
        assert_eq!(number.as_str(), "-1.25e+3");
        assert_eq!(number.as_f64(), Some(-1_250.0));
        assert_eq!(object["name"].as_str(), Some("α 😀"));
    }

    #[test]
    fn reports_json_syntax_with_catalog_diagnostics() {
        let missing_colon = parse_config_text(
            "/repo/tsconfig.json",
            r#"{ "compilerOptions" { "strict": true } }"#,
        );
        assert_eq!(missing_colon.diagnostics.len(), 1);
        assert_eq!(missing_colon.diagnostics[0].code(), 1005);
        assert_eq!(missing_colon.diagnostics[0].render(), "':' expected.");

        let comment = parse_config_text("/repo/tsconfig.json", "{ /* unfinished");
        assert_eq!(comment.diagnostics[0].code(), 1010);
        assert_eq!(comment.diagnostics[0].render(), "'*/' expected.");

        let top_level_array = parse_config_text("/repo/tsconfig.json", "[]");
        assert_eq!(top_level_array.diagnostics[0].code(), 1136);
        assert_eq!(
            top_level_array.diagnostics[0].render(),
            "Property assignment expected."
        );
    }

    #[test]
    fn reports_vfs_read_failures_with_ts5012() {
        let file_system = MemoryFileSystem::default();
        let result = parse_config_file(&file_system, "/missing/tsconfig.json");
        assert!(result.value.is_none());
        assert_eq!(result.diagnostics[0].code(), 5012);
        assert!(
            result.diagnostics[0]
                .render()
                .starts_with("Cannot read file '/missing/tsconfig.json':")
        );
    }

    #[test]
    fn distinguishes_absent_and_explicitly_empty_file_lists() {
        let absent = parse_config_text("tsconfig.json", "{}").value.unwrap();
        assert_eq!(absent.files, None);

        let empty = parse_config_text("tsconfig.json", r#"{ "files": [] }"#)
            .value
            .unwrap();
        assert_eq!(empty.files, Some(Vec::new()));
    }

    #[test]
    fn accepts_an_empty_config_as_an_empty_object() {
        let result = parse_config_text("/repo/base.json", " // only trivia\n");
        assert!(result.is_ok());
        assert!(result.value.unwrap().raw.is_empty());
    }

    #[test]
    fn accepts_a_utf8_bom_and_keeps_relative_config_paths_relative() {
        let file_system = MemoryFileSystem::default();
        file_system
            .write_file("base.json", "\u{feff}{ \"compilerOptions\": {} }")
            .unwrap();
        let result = parse_config_text("tsconfig.json", "\u{feff}{ \"extends\": \"./base\" }");
        assert!(result.is_ok());
        assert_eq!(
            result.value.unwrap().resolved_extends(&file_system),
            ["base.json"]
        );
    }

    #[test]
    fn resolves_extends_and_merges_leaf_over_base() {
        let file_system = MemoryFileSystem::default();
        file_system
            .write_file(
                "/repo/base.json",
                r#"{
                    "files": ["base.ts"],
                    "include": ["base/**/*.ts"],
                    "exclude": ["base/out"],
                    "compilerOptions": { "strict": true, "target": "es2019" }
                }"#,
            )
            .unwrap();
        file_system
            .write_file(
                "/repo/app/tsconfig.json",
                r#"{
                    "extends": "../base",
                    "include": ["src/**/*.ts"],
                    "compilerOptions": { "target": "es2022", "noEmit": true }
                }"#,
            )
            .unwrap();

        let result = resolve_config_file(&file_system, "/repo/app/tsconfig.json");
        assert!(result.is_ok(), "{:?}", result.diagnostics);
        let config = result.value.unwrap();
        assert_eq!(config.files.unwrap(), ["/repo/base.ts"]);
        assert_eq!(config.include.unwrap(), ["/repo/app/src/**/*.ts"]);
        assert_eq!(config.exclude.unwrap(), ["/repo/base/out"]);
        assert_eq!(
            config.compiler_options.get("strict"),
            Some(&JsonValue::Bool(true))
        );
        assert_eq!(
            config
                .compiler_options
                .get("target")
                .and_then(JsonValue::as_str),
            Some("es2022")
        );
        assert_eq!(
            config.compiler_options.get("noEmit"),
            Some(&JsonValue::Bool(true))
        );
        assert!(config.extends.is_none());
    }

    #[test]
    fn applies_multiple_bases_left_to_right_and_supports_package_configs() {
        let file_system = MemoryFileSystem::default();
        file_system
            .write_file(
                "/repo/first.json",
                r#"{"compilerOptions":{"target":"es2018","strict":true}}"#,
            )
            .unwrap();
        file_system
            .write_file(
                "/repo/node_modules/preset/package.json",
                r#"{"tsconfig":"config/base.json"}"#,
            )
            .unwrap();
        file_system
            .write_file(
                "/repo/node_modules/preset/config/base.json",
                r#"{"compilerOptions":{"target":"es2021","declaration":true}}"#,
            )
            .unwrap();
        file_system
            .write_file(
                "/repo/app/tsconfig.json",
                r#"{"extends":["../first","preset"],"files":[]}"#,
            )
            .unwrap();

        let config = resolve_config_file(&file_system, "/repo/app/tsconfig.json")
            .value
            .unwrap();
        assert_eq!(config.files, Some(Vec::new()));
        assert_eq!(
            config
                .compiler_options
                .get("target")
                .and_then(JsonValue::as_str),
            Some("es2021")
        );
        assert_eq!(
            config.compiler_options.get("strict"),
            Some(&JsonValue::Bool(true))
        );
        assert_eq!(
            config.compiler_options.get("declaration"),
            Some(&JsonValue::Bool(true))
        );
    }

    #[test]
    fn resolves_extensionless_and_directory_package_config_entries() {
        let file_system = MemoryFileSystem::default();
        file_system
            .write_file(
                "/repo/node_modules/@scope/base/package.json",
                r#"{ "tsconfig": "configs/base" }"#,
            )
            .unwrap();
        file_system
            .write_file(
                "/repo/node_modules/@scope/base/configs/base.json",
                r#"{ "compilerOptions": { "strict": false } }"#,
            )
            .unwrap();
        file_system
            .write_file(
                "/repo/node_modules/preset/package.json",
                r#"{ "tsconfig": "configs" }"#,
            )
            .unwrap();
        file_system
            .write_file(
                "/repo/node_modules/preset/configs/tsconfig.json",
                r#"{ "compilerOptions": { "declaration": true } }"#,
            )
            .unwrap();
        file_system
            .write_file(
                "/repo/app/tsconfig.json",
                r#"{ "extends": ["@scope/base", "preset"] }"#,
            )
            .unwrap();

        let result = resolve_config_file(&file_system, "/repo/app/tsconfig.json");
        assert!(result.is_ok(), "{:?}", result.diagnostics);
        let config = result.value.unwrap();
        assert_eq!(
            config.compiler_options.get("strict"),
            Some(&JsonValue::Bool(false))
        );
        assert_eq!(
            config.compiler_options.get("declaration"),
            Some(&JsonValue::Bool(true))
        );
    }

    #[test]
    fn finds_package_configs_at_the_filesystem_root() {
        let file_system = MemoryFileSystem::default();
        file_system
            .write_file(
                "/node_modules/preset/tsconfig.json",
                r#"{ "compilerOptions": { "strict": false } }"#,
            )
            .unwrap();
        file_system
            .write_file("/project/tsconfig.json", r#"{ "extends": "preset" }"#)
            .unwrap();

        let result = resolve_config_file(&file_system, "/project/tsconfig.json");
        assert!(result.is_ok(), "{:?}", result.diagnostics);
        assert_eq!(
            result.value.unwrap().compiler_options.get("strict"),
            Some(&JsonValue::Bool(false))
        );
    }

    #[test]
    fn resolves_relative_extends_from_a_root_level_config() {
        let file_system = MemoryFileSystem::default();
        file_system
            .write_file(
                "/base.json",
                r#"{ "compilerOptions": { "declaration": true } }"#,
            )
            .unwrap();
        file_system
            .write_file("/tsconfig.json", r#"{ "extends": "./base" }"#)
            .unwrap();

        let parsed = parse_config_file(&file_system, "/tsconfig.json")
            .value
            .unwrap();
        assert_eq!(parsed.resolved_extends(&file_system), ["/base.json"]);

        let result = resolve_config_file(&file_system, "/tsconfig.json");
        assert!(result.is_ok(), "{:?}", result.diagnostics);
        assert_eq!(
            result.value.unwrap().compiler_options.get("declaration"),
            Some(&JsonValue::Bool(true))
        );
    }

    #[test]
    fn resolves_emit_paths_relative_to_their_config() {
        let file_system = MemoryFileSystem::default();
        file_system
            .write_file(
                "/repo/config/tsconfig.json",
                r#"{
                    "compilerOptions": {
                        "outDir": "../dist",
                        "rootDir": "src",
                        "declarationDir": "../types",
                        "tsBuildInfoFile": "../cache/project.tsbuildinfo"
                    }
                }"#,
            )
            .unwrap();
        let config = resolve_config_file(&file_system, "/repo/config/tsconfig.json")
            .value
            .unwrap();
        for (name, expected) in [
            ("outDir", "/repo/dist"),
            ("rootDir", "/repo/config/src"),
            ("declarationDir", "/repo/types"),
            ("tsBuildInfoFile", "/repo/cache/project.tsbuildinfo"),
        ] {
            assert_eq!(
                config
                    .compiler_options
                    .get(name)
                    .and_then(JsonValue::as_str),
                Some(expected)
            );
        }
    }

    #[test]
    fn keeps_inherited_paths_relative_to_the_config_that_declared_them() {
        let file_system = MemoryFileSystem::default();
        file_system
            .write_file(
                "/repo/config/base.json",
                r#"{
                    "compilerOptions": {
                        "BASEURL": ".",
                        "outFile": "dist/bundle.js",
                        "mapRoot": "maps",
                        "rootDirs": ["src", "generated"],
                        "typeRoots": ["types"],
                        "paths": { "@app/*": ["src/*"] }
                    }
                }"#,
            )
            .unwrap();
        file_system
            .write_file(
                "/repo/app/tsconfig.json",
                r#"{ "extends": "../config/base.json" }"#,
            )
            .unwrap();

        let result = resolve_config_file(&file_system, "/repo/app/tsconfig.json");
        assert!(result.is_ok(), "{:?}", result.diagnostics);
        let config = result.value.unwrap();
        for (name, expected) in [
            ("BASEURL", "/repo/config"),
            ("outFile", "/repo/config/dist/bundle.js"),
            ("mapRoot", "/repo/config/maps"),
        ] {
            assert_eq!(
                config
                    .compiler_options
                    .get(name)
                    .and_then(JsonValue::as_str),
                Some(expected)
            );
        }
        assert_eq!(
            config.compiler_options.get("rootDirs"),
            Some(&JsonValue::Array(vec![
                JsonValue::String("/repo/config/src".into()),
                JsonValue::String("/repo/config/generated".into()),
            ]))
        );
        assert_eq!(
            config.compiler_options.get("typeRoots"),
            Some(&JsonValue::Array(vec![JsonValue::String(
                "/repo/config/types".into()
            )]))
        );
        assert_eq!(
            config
                .compiler_options
                .get("paths")
                .and_then(JsonValue::as_object)
                .and_then(|paths| paths.get("@app/*")),
            Some(&JsonValue::Array(vec![JsonValue::String(
                "/repo/config/src/*".into()
            )]))
        );
    }

    #[test]
    fn excludes_output_directories_unless_exclude_was_explicitly_set() {
        let file_system = MemoryFileSystem::default();
        file_system
            .write_file(
                "/repo/config/base.json",
                r#"{
                    "compilerOptions": {
                        "outDir": "../dist",
                        "declarationDir": "../types"
                    }
                }"#,
            )
            .unwrap();
        file_system
            .write_file(
                "/repo/app/tsconfig.json",
                r#"{ "extends": "../config/base.json" }"#,
            )
            .unwrap();

        let inherited = resolve_config_file(&file_system, "/repo/app/tsconfig.json")
            .value
            .unwrap();
        assert_eq!(
            inherited.exclude,
            Some(vec!["/repo/dist".into(), "/repo/types".into()])
        );
        assert!(!inherited.raw.contains_key("exclude"));

        file_system
            .write_file(
                "/repo/app/tsconfig.json",
                r#"{ "extends": "../config/base.json", "exclude": [] }"#,
            )
            .unwrap();
        let explicit = resolve_config_file(&file_system, "/repo/app/tsconfig.json")
            .value
            .unwrap();
        assert_eq!(explicit.exclude, Some(Vec::new()));

        file_system
            .write_file(
                "/repo/app/tsconfig.json",
                r#"{ "extends": "../config/base.json", "exclude": null }"#,
            )
            .unwrap();
        let cleared = resolve_config_file(&file_system, "/repo/app/tsconfig.json")
            .value
            .unwrap();
        assert_eq!(
            cleared.exclude,
            Some(vec!["/repo/dist".into(), "/repo/types".into()])
        );
    }

    #[test]
    fn expands_inherited_config_dir_templates_from_the_leaf_config() {
        let file_system = MemoryFileSystem::default();
        file_system
            .write_file(
                "/repo/config/base.json",
                r#"{
                    "files": ["${configDir}/src/index.ts"],
                    "include": ["${configDir}/src/**/*.ts"],
                    "compilerOptions": {
                        "outDir": "${configDir}/dist",
                        "rootDirs": ["${CONFIGDIR}/src"],
                        "typeRoots": ["${configDir}/types"],
                        "paths": { "@app/*": ["${configDir}/src/*"] }
                    }
                }"#,
            )
            .unwrap();
        file_system
            .write_file(
                "/repo/app/tsconfig.json",
                r#"{ "extends": "../config/base.json" }"#,
            )
            .unwrap();

        let config = resolve_config_file(&file_system, "/repo/app/tsconfig.json")
            .value
            .unwrap();
        assert_eq!(config.files, Some(vec!["/repo/app/src/index.ts".into()]));
        assert_eq!(config.include, Some(vec!["/repo/app/src/**/*.ts".into()]));
        assert_eq!(
            config
                .compiler_options
                .get("outDir")
                .and_then(JsonValue::as_str),
            Some("/repo/app/dist")
        );
        assert_eq!(
            config.compiler_options.get("rootDirs"),
            Some(&JsonValue::Array(vec![JsonValue::String(
                "/repo/app/src".into()
            )]))
        );
        assert_eq!(
            config.compiler_options.get("typeRoots"),
            Some(&JsonValue::Array(vec![JsonValue::String(
                "/repo/app/types".into()
            )]))
        );
        assert_eq!(
            config
                .compiler_options
                .get("paths")
                .and_then(JsonValue::as_object)
                .and_then(|paths| paths.get("@app/*")),
            Some(&JsonValue::Array(vec![JsonValue::String(
                "/repo/app/src/*".into()
            )]))
        );
    }

    #[test]
    fn null_project_fields_and_case_variants_override_inherited_values() {
        let file_system = MemoryFileSystem::default();
        file_system
            .write_file(
                "/repo/base.json",
                r#"{
                    "files": ["base.ts"],
                    "include": ["src/**/*.ts"],
                    "exclude": ["dist"],
                    "compilerOptions": {
                        "Strict": true,
                        "outDir": "dist",
                        "types": ["node"]
                    }
                }"#,
            )
            .unwrap();
        file_system
            .write_file(
                "/repo/app/tsconfig.json",
                r#"{
                    "extends": "../base.json",
                    "files": null,
                    "include": null,
                    "exclude": null,
                    "compilerOptions": {
                        "strict": false,
                        "outDir": null,
                        "types": null
                    }
                }"#,
            )
            .unwrap();

        let config = resolve_config_file(&file_system, "/repo/app/tsconfig.json")
            .value
            .unwrap();
        assert_eq!(config.files, None);
        assert_eq!(config.include, None);
        assert_eq!(config.exclude, None);
        assert_eq!(
            config.compiler_options.get("strict"),
            Some(&JsonValue::Bool(false))
        );
        assert!(!config.compiler_options.contains_key("Strict"));
        assert_eq!(
            config.compiler_options.get("outDir"),
            Some(&JsonValue::Null)
        );
        assert_eq!(config.compiler_options.get("types"), Some(&JsonValue::Null));
    }

    #[test]
    fn reports_missing_and_circular_base_configs() {
        let file_system = MemoryFileSystem::default();
        file_system
            .write_file("/repo/a.json", r#"{"extends":["./b","./missing"]}"#)
            .unwrap();
        file_system
            .write_file("/repo/b.json", r#"{"extends":"./a"}"#)
            .unwrap();

        let result = resolve_config_file(&file_system, "/repo/a.json");
        assert!(result.value.is_some());
        assert_eq!(
            result
                .diagnostics
                .iter()
                .map(super::ConfigDiagnostic::code)
                .collect::<Vec<_>>(),
            [18_000, 6_053]
        );
        assert!(result.diagnostics[0].render().contains("/repo/a.json"));
    }

    #[test]
    fn detects_case_only_config_cycles_on_case_insensitive_file_systems() {
        let file_system = MemoryFileSystem::new(false);
        file_system
            .write_file("/repo/base.json", r#"{ "extends": "./BASE.json" }"#)
            .unwrap();

        let result = resolve_config_file(&file_system, "/repo/base.json");
        assert!(result.value.is_some());
        assert_eq!(result.diagnostics.len(), 1);
        assert_eq!(result.diagnostics[0].code(), 18_000);
    }

    #[test]
    fn resolves_bare_and_windows_rooted_reference_paths() {
        let file_system = MemoryFileSystem::new(false);
        file_system
            .write_file("C:/repo/app/lib/tsconfig.json", "{}")
            .unwrap();
        file_system
            .write_file("D:/shared/types/tsconfig.json", "{}")
            .unwrap();
        let config = parse_config_text(
            "C:/repo/app/tsconfig.json",
            r#"{
                "references": [
                    { "path": "lib" },
                    { "path": "D:/shared/types" }
                ],
                "compilerOptions": { "outDir": "D:/build" }
            }"#,
        )
        .value
        .unwrap();

        let references = config.resolved_references(&file_system);
        assert_eq!(references[0].path, "C:/repo/app/lib/tsconfig.json");
        assert_eq!(references[1].path, "D:/shared/types/tsconfig.json");

        file_system
            .write_file(
                "C:/repo/app/tsconfig.json",
                r#"{ "compilerOptions": { "outDir": "D:/build" } }"#,
            )
            .unwrap();
        let resolved = resolve_config_file(&file_system, "C:/repo/app/tsconfig.json")
            .value
            .unwrap();
        assert_eq!(
            resolved
                .compiler_options
                .get("outDir")
                .and_then(JsonValue::as_str),
            Some("D:/build")
        );
    }

    #[test]
    fn resolves_leaf_project_references_without_inheriting_base_references() {
        let file_system = MemoryFileSystem::default();
        file_system
            .write_file(
                "/repo/base.json",
                r#"{"references":[{"path":"./base-project"}]}"#,
            )
            .unwrap();
        file_system
            .write_file(
                "/repo/app/tsconfig.json",
                r#"{"extends":"../base","references":[{"path":"../lib","prepend":true},{"path":"../types.json","circular":false}]}"#,
            )
            .unwrap();
        file_system
            .write_file("/repo/lib/tsconfig.json", "{}")
            .unwrap();
        file_system.write_file("/repo/types.json", "{}").unwrap();

        let config = resolve_config_file(&file_system, "/repo/app/tsconfig.json")
            .value
            .unwrap();
        let references = config.resolved_references(&file_system);
        assert_eq!(references.len(), 2);
        assert_eq!(references[0].path, "/repo/lib/tsconfig.json");
        assert_eq!(references[0].prepend, Some(true));
        assert_eq!(references[1].path, "/repo/types.json");
        assert_eq!(references[1].circular, Some(false));
    }
}
