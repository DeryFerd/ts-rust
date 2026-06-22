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
        let include = raw.get("include").and_then(string_array);
        let exclude = raw.get("exclude").and_then(string_array);
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
                let mut path = if is_relative_path(&reference.path) {
                    resolve_relative(directory, &reference.path)
                } else {
                    normalize_path(&reference.path)
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
    ParseResult {
        value: Some(ProjectConfig::from_json(normalize_path(file_name), raw)),
        diagnostics: parsed.diagnostics,
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
    let value = state.resolve(&normalize_path(file_name));
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
        if let Some(index) = self.stack.iter().position(|path| path == &file_name) {
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
                        5_083,
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
    if files.is_some() {
        base.files = files;
    }
    if include.is_some() {
        base.include = include;
    }
    if exclude.is_some() {
        base.exclude = exclude;
    }
    base.compiler_options.extend(compiler_options);
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
            if !Path::new(value).is_absolute() {
                *value = resolve_relative(directory, value);
            }
        }
    }
    if let Some(JsonValue::String(base_url)) = config.compiler_options.get_mut("baseUrl")
        && !Path::new(base_url).is_absolute()
    {
        *base_url = resolve_relative(directory, base_url);
    }
    for (name, value) in &mut config.compiler_options {
        if matches!(
            name.to_ascii_lowercase().as_str(),
            "outdir" | "rootdir" | "declarationdir" | "tsbuildinfofile"
        ) && let JsonValue::String(path) = value
            && !Path::new(path.as_str()).is_absolute()
        {
            *path = resolve_relative(directory, path);
        }
    }
    if let Some(JsonValue::Array(root_dirs)) = config.compiler_options.get_mut("rootDirs") {
        for root_dir in root_dirs {
            if let JsonValue::String(root_dir) = root_dir
                && !Path::new(root_dir.as_str()).is_absolute()
            {
                *root_dir = resolve_relative(directory, root_dir);
            }
        }
    }
    config
}

fn parse_extends(value: &JsonValue) -> Option<Extends> {
    match value {
        JsonValue::String(path) => Some(Extends::Single(path.clone())),
        JsonValue::Array(values) => Some(Extends::Multiple(
            values
                .iter()
                .filter_map(JsonValue::as_str)
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
    let directory = config_path
        .rsplit_once('/')
        .map_or("", |(directory, _)| directory);
    let candidate = if directory.is_empty() {
        normalize_path(extends_path)
    } else {
        normalize_path(&format!("{directory}/{extends_path}"))
    };
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
    if is_relative_path(extends_path) || Path::new(extends_path).is_absolute() {
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
        let parent = directory
            .rsplit_once('/')
            .map_or("", |(parent, _)| parent)
            .to_owned();
        if parent == directory || (parent.is_empty() && directory.is_empty()) {
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
            if file_system.file_exists(&configured) {
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
    path.rsplit_once('/').map_or("", |(directory, _)| directory)
}

fn resolve_relative(directory: &str, path: &str) -> String {
    if directory.is_empty() {
        normalize_path(path)
    } else {
        normalize_path(&format!("{directory}/{path}"))
    }
}

fn is_relative_path(path: &str) -> bool {
    path == "." || path == ".." || path.starts_with("./") || path.starts_with("../")
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
            [18_000, 5_083]
        );
        assert!(result.diagnostics[0].render().contains("/repo/a.json"));
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
