//! Foundational TypeScript module resolution.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::{PoisonError, RwLock},
};

use serde_json::Value;
use ts_path::{FileExtension, is_absolute, is_relative, normalize_path, resolve_path, root_length};
use ts_semver::{Version, VersionRange};
use ts_vfs::FileSystem;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ResolutionMode {
    Classic,
    #[default]
    Node10,
    Node16,
    NodeNext,
    Bundler,
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(clippy::struct_excessive_bools)]
pub struct ResolutionOptions {
    pub mode: ResolutionMode,
    pub allow_arbitrary_extensions: bool,
    pub allow_javascript: bool,
    pub resolve_json: bool,
    pub prefer_types: bool,
    pub base_url: Option<String>,
    pub paths: BTreeMap<String, Vec<String>>,
    pub root_dirs: Vec<String>,
    pub type_roots: Option<Vec<String>>,
    pub types: Option<Vec<String>>,
}

impl Default for ResolutionOptions {
    fn default() -> Self {
        Self {
            mode: ResolutionMode::Node10,
            allow_arbitrary_extensions: false,
            allow_javascript: true,
            resolve_json: false,
            prefer_types: true,
            base_url: None,
            paths: BTreeMap::new(),
            root_dirs: Vec::new(),
            type_roots: None,
            types: None,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FailedLookupKind {
    File,
    Directory,
    PackageJson,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FailedLookup {
    pub kind: FailedLookupKind,
    pub path: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolvedModule {
    pub resolved_file_name: String,
    pub extension: Option<FileExtension>,
    pub is_external_library_import: bool,
    pub package_json: Option<String>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ResolutionResult {
    pub resolved: Option<ResolvedModule>,
    pub failed_lookups: Vec<FailedLookup>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct PackageJson {
    pub types: Option<String>,
    pub typings: Option<String>,
    pub main: Option<String>,
    pub package_type: Option<String>,
    pub exports: Option<Value>,
    pub types_versions: Option<Value>,
    pub name: Option<String>,
    pub imports: Option<Value>,
}

pub struct Resolver<'a, F: FileSystem + ?Sized> {
    file_system: &'a F,
    options: ResolutionOptions,
    cache: RwLock<BTreeMap<(String, String), ResolutionResult>>,
}

impl<'a, F: FileSystem + ?Sized> Resolver<'a, F> {
    #[must_use]
    pub fn new(file_system: &'a F, options: ResolutionOptions) -> Self {
        Self {
            file_system,
            options,
            cache: RwLock::new(BTreeMap::new()),
        }
    }

    #[must_use]
    pub fn options(&self) -> ResolutionOptions {
        self.options.clone()
    }

    #[must_use]
    pub fn resolve(&self, specifier: &str, containing_file: &str) -> ResolutionResult {
        let key = (specifier.to_owned(), normalize_path(containing_file));
        if let Some(cached) = self
            .cache
            .read()
            .unwrap_or_else(PoisonError::into_inner)
            .get(&key)
        {
            return cached.clone();
        }
        let mut state = ResolutionState {
            resolver: self,
            failed_lookups: Vec::new(),
        };
        let containing_directory = directory_path(containing_file);
        let resolved = if is_relative(specifier) {
            let candidate = resolve_path(&containing_directory, &[specifier]);
            state.resolve_candidate(&candidate, false).or_else(|| {
                state.resolve_root_dirs(specifier, &containing_directory)
            })
        } else if is_absolute(specifier) {
            state.resolve_paths_or_base_url(specifier).or_else(|| {
                let candidate = resolve_path(&containing_directory, &[specifier]);
                state.resolve_candidate(&candidate, false)
            })
        } else if self.options.mode == ResolutionMode::Classic {
            state.resolve_paths_or_base_url(specifier).or_else(|| {
                ancestors(&containing_directory)
                    .into_iter()
                    .find_map(|directory| {
                        let candidate = resolve_path(&directory, &[specifier]);
                        state.resolve_candidate(&candidate, false)
                    })
            })
        } else {
            state
                .resolve_paths_or_base_url(specifier)
                .or_else(|| state.resolve_package_imports_or_self(specifier, &containing_directory))
                .or_else(|| state.resolve_node_modules(specifier, &containing_directory))
                .or_else(|| state.resolve_from_type_roots(specifier, &containing_directory))
        };
        let result = ResolutionResult {
            resolved,
            failed_lookups: state.failed_lookups,
        };
        self.cache
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .insert(key, result.clone());
        result
    }

    /// Resolves a `types` compiler-option entry or automatically discovered
    /// package through type roots and ancestor `node_modules/@types` folders.
    #[must_use]
    pub fn resolve_type_reference(&self, name: &str, containing_file: &str) -> ResolutionResult {
        let mut state = ResolutionState {
            resolver: self,
            failed_lookups: Vec::new(),
        };
        let containing_directory = directory_path(containing_file);
        let type_root_name = name
            .strip_prefix('@')
            .and_then(|name| name.split_once('/'))
            .map_or_else(
                || name.to_owned(),
                |(scope, package)| format!("{scope}__{package}"),
            );
        let resolved = state
            .resolve_from_type_roots(&type_root_name, &containing_directory)
            .or_else(|| {
                types_package_name(name).and_then(|types_name| {
                    state.resolve_node_modules_types(&types_name, &containing_directory)
                })
            });
        ResolutionResult {
            resolved,
            failed_lookups: state.failed_lookups,
        }
    }

    pub fn clear_cache(&self) {
        self.cache
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .clear();
    }
}

struct ResolutionState<'a, 'fs, F: FileSystem + ?Sized> {
    resolver: &'a Resolver<'fs, F>,
    failed_lookups: Vec<FailedLookup>,
}

enum PackageMetadataResolution {
    NotApplicable,
    Resolved(ResolvedModule),
    Blocked,
}

impl<F: FileSystem + ?Sized> ResolutionState<'_, '_, F> {
    fn resolve_paths_or_base_url(&mut self, specifier: &str) -> Option<ResolvedModule> {
        if let Some((capture, substitutions)) =
            best_path_match(&self.resolver.options.paths, specifier)
        {
            let base = self
                .resolver
                .options
                .base_url
                .clone()
                .unwrap_or_else(|| ".".to_owned());
            for substitution in substitutions {
                let mapped = substitution.replace('*', &capture);
                let candidate = resolve_path(&base, &[&mapped]);
                if let Some(resolved) = self.resolve_candidate(&candidate, false) {
                    return Some(resolved);
                }
            }
        }
        let base = self.resolver.options.base_url.as_deref()?;
        let candidate = resolve_path(base, &[specifier]);
        self.resolve_candidate(&candidate, false)
    }

    fn resolve_root_dirs(
        &mut self,
        specifier: &str,
        containing_directory: &str,
    ) -> Option<ResolvedModule> {
        let roots = self.resolver.options.root_dirs.clone();
        let normalized_containing = normalize_path(containing_directory);
        let (_, suffix) = roots
            .iter()
            .filter_map(|root| {
                let normalized_root = normalize_path(root);
                path_suffix(&normalized_containing, &normalized_root)
                    .map(|suffix| (normalized_root.len(), suffix.to_owned()))
            })
            .max_by_key(|(length, _)| *length)?;
        for root in roots {
            let candidate_directory = if suffix.is_empty() {
                normalize_path(&root)
            } else {
                resolve_path(&root, &[&suffix])
            };
            let candidate = resolve_path(&candidate_directory, &[specifier]);
            if let Some(resolved) = self.resolve_candidate(&candidate, false) {
                return Some(resolved);
            }
        }
        None
    }

    fn resolve_package_imports_or_self(
        &mut self,
        specifier: &str,
        containing_directory: &str,
    ) -> Option<ResolvedModule> {
        if !matches!(
            self.resolver.options.mode,
            ResolutionMode::Node16 | ResolutionMode::NodeNext | ResolutionMode::Bundler
        ) {
            return None;
        }
        if specifier == "#"
            || (self.resolver.options.mode == ResolutionMode::Node16 && specifier.starts_with("#/"))
        {
            return None;
        }
        for ancestor in ancestors(containing_directory) {
            let package_json_path = join(&ancestor, "package.json");
            if !self.resolver.file_system.file_exists(&package_json_path) {
                continue;
            }
            let package = self.read_package_json(&package_json_path)?;
            let target = if specifier.starts_with('#') {
                package.imports.as_ref().and_then(|imports| {
                    package_map_target(imports, specifier, self.resolver.options.prefer_types)
                })
            } else {
                let name = package.name.as_deref()?;
                let rest = specifier
                    .strip_prefix(name)
                    .filter(|rest| rest.is_empty() || rest.starts_with('/'))?;
                let key = if rest.is_empty() {
                    ".".to_owned()
                } else {
                    format!(".{rest}")
                };
                package.exports.as_ref().and_then(|exports| {
                    package_export_target(exports, &key, self.resolver.options.prefer_types)
                })
            }?;
            if target.starts_with("./") {
                let candidate = resolve_path(&ancestor, &[target.trim_start_matches("./")]);
                return self.resolve_candidate_with_package(&candidate, &package_json_path);
            }
            return self.resolve_node_modules(&target, &ancestor);
        }
        None
    }

    fn resolve_from_type_roots(
        &mut self,
        specifier: &str,
        containing_directory: &str,
    ) -> Option<ResolvedModule> {
        for root in effective_type_roots(&self.resolver.options, containing_directory) {
            let candidate = resolve_path(&root, &[specifier]);
            if let Some(mut resolved) = self.resolve_candidate(&candidate, true) {
                resolved.is_external_library_import = true;
                return Some(resolved);
            }
        }
        None
    }

    fn resolve_node_modules(
        &mut self,
        specifier: &str,
        containing_directory: &str,
    ) -> Option<ResolvedModule> {
        let (package_name, rest) = parse_package_name(specifier)?;
        for ancestor in ancestors(containing_directory) {
            if ancestor.ends_with("/node_modules") {
                continue;
            }
            let node_modules = join(&ancestor, "node_modules");
            let package_directory = join(&node_modules, package_name);
            match self.resolve_package_metadata(&package_directory, rest) {
                PackageMetadataResolution::Resolved(resolved) => return Some(resolved),
                PackageMetadataResolution::Blocked => return None,
                PackageMetadataResolution::NotApplicable => {}
            }
            let candidate = if rest.is_empty() {
                package_directory
            } else {
                join(&package_directory, rest)
            };
            if let Some(mut resolved) = self.resolve_candidate(&candidate, true) {
                resolved.is_external_library_import = true;
                return Some(resolved);
            }
        }
        if let Some(types_name) = types_package_name(specifier) {
            return self.resolve_node_modules_types(&types_name, containing_directory);
        }
        None
    }

    fn resolve_node_modules_types(
        &mut self,
        specifier: &str,
        containing_directory: &str,
    ) -> Option<ResolvedModule> {
        let (package_name, rest) = parse_package_name(specifier)?;
        for ancestor in ancestors(containing_directory) {
            if ancestor.ends_with("/node_modules") {
                continue;
            }
            let package_directory = join(&join(&ancestor, "node_modules"), package_name);
            let candidate = if rest.is_empty() {
                package_directory
            } else {
                join(&package_directory, rest)
            };
            if let Some(mut resolved) = self.resolve_candidate(&candidate, true) {
                resolved.is_external_library_import = true;
                return Some(resolved);
            }
        }
        None
    }

    fn resolve_package_metadata(
        &mut self,
        package_directory: &str,
        rest: &str,
    ) -> PackageMetadataResolution {
        let package_json_path = join(package_directory, "package.json");
        if !self.resolver.file_system.file_exists(&package_json_path) {
            return PackageMetadataResolution::NotApplicable;
        }
        let Some(package) = self.read_package_json(&package_json_path) else {
            return PackageMetadataResolution::NotApplicable;
        };
        if let Some(exports) = &package.exports
            && matches!(
                self.resolver.options.mode,
                ResolutionMode::Node16 | ResolutionMode::NodeNext | ResolutionMode::Bundler
            )
        {
            let key = if rest.is_empty() {
                ".".to_owned()
            } else {
                format!("./{rest}")
            };
            let Some(target) =
                package_export_target(exports, &key, self.resolver.options.prefer_types)
            else {
                return PackageMetadataResolution::Blocked;
            };
            let candidate = resolve_path(package_directory, &[target.trim_start_matches("./")]);
            if let Some(mut resolved) =
                self.resolve_candidate_with_package(&candidate, &package_json_path)
            {
                resolved.is_external_library_import = true;
                return PackageMetadataResolution::Resolved(resolved);
            }
            return PackageMetadataResolution::Blocked;
        }
        if !rest.is_empty()
            && let Some(types_versions) = &package.types_versions
            && let Some(targets) = types_version_targets(types_versions, rest)
        {
            for target in targets {
                let candidate = resolve_path(package_directory, &[&target]);
                if let Some(mut resolved) =
                    self.resolve_candidate_with_package(&candidate, &package_json_path)
                {
                    resolved.is_external_library_import = true;
                    return PackageMetadataResolution::Resolved(resolved);
                }
            }
            return PackageMetadataResolution::Blocked;
        }
        PackageMetadataResolution::NotApplicable
    }

    fn resolve_candidate_with_package(
        &mut self,
        candidate: &str,
        package_json: &str,
    ) -> Option<ResolvedModule> {
        if let Some(resolved) = self.resolve_file(candidate, true, Some(package_json)) {
            return Some(resolved);
        }
        if self.resolver.file_system.directory_exists(candidate) {
            return self.resolve_index(candidate, true, Some(package_json));
        }
        None
    }

    fn resolve_candidate(&mut self, candidate: &str, external: bool) -> Option<ResolvedModule> {
        if !candidate.ends_with('/')
            && let Some(resolved) = self.resolve_file(candidate, external, None)
        {
            return Some(resolved);
        }
        if !self.resolver.file_system.directory_exists(candidate) {
            self.failed(FailedLookupKind::Directory, candidate);
            return None;
        }
        self.resolve_directory(candidate, external)
    }

    fn resolve_directory(&mut self, directory: &str, external: bool) -> Option<ResolvedModule> {
        let package_json_path = join(directory, "package.json");
        let package = self.read_package_json(&package_json_path);
        if let Some(package) = package {
            if self.resolver.options.prefer_types
                && let Some(types_versions) = &package.types_versions
            {
                let types_entry = package
                    .typings
                    .as_deref()
                    .or(package.types.as_deref())
                    .unwrap_or("index");
                if let Some(targets) = types_version_targets(types_versions, types_entry) {
                    for target in targets {
                        let candidate = resolve_path(directory, &[&target]);
                        if let Some(mut resolved) =
                            self.resolve_candidate_with_package(&candidate, &package_json_path)
                        {
                            resolved.package_json = Some(package_json_path.clone());
                            return Some(resolved);
                        }
                    }
                }
            }
            let fields = if self.resolver.options.prefer_types {
                [
                    package.typings.as_deref(),
                    package.types.as_deref(),
                    package.main.as_deref(),
                ]
            } else {
                [
                    package.main.as_deref(),
                    package.typings.as_deref(),
                    package.types.as_deref(),
                ]
            };
            for field in fields.into_iter().flatten() {
                let target = resolve_path(directory, &[field]);
                if let Some(mut resolved) =
                    self.resolve_file(&target, external, Some(&package_json_path))
                {
                    resolved.package_json = Some(package_json_path.clone());
                    return Some(resolved);
                }
                if self.resolver.file_system.directory_exists(&target)
                    && let Some(mut resolved) =
                        self.resolve_index(&target, external, Some(&package_json_path))
                {
                    resolved.package_json = Some(package_json_path.clone());
                    return Some(resolved);
                }
            }
        }
        self.resolve_index(directory, external, None)
    }

    fn resolve_index(
        &mut self,
        directory: &str,
        external: bool,
        package_json: Option<&str>,
    ) -> Option<ResolvedModule> {
        self.resolve_file(&join(directory, "index"), external, package_json)
    }

    fn resolve_file(
        &mut self,
        candidate: &str,
        external: bool,
        package_json: Option<&str>,
    ) -> Option<ResolvedModule> {
        for path in self.file_candidates(candidate) {
            if self.resolver.file_system.file_exists(&path) {
                let resolved_file_name = self.resolver.file_system.realpath(&path);
                return Some(ResolvedModule {
                    extension: ts_path::extension_from_path(&resolved_file_name),
                    resolved_file_name,
                    is_external_library_import: external,
                    package_json: package_json.map(str::to_owned),
                });
            }
            self.failed(FailedLookupKind::File, &path);
        }
        None
    }

    fn file_candidates(&self, candidate: &str) -> Vec<String> {
        let normalized = normalize_path(candidate);
        let extension = source_extension(&normalized);
        if extension.is_none()
            && self.resolver.options.allow_arbitrary_extensions
            && let Some(segment) = normalized.rsplit('/').next()
            && let Some(dot) = segment.rfind('.')
        {
            let extension = &segment[dot..];
            let stem = &normalized[..normalized.len() - extension.len()];
            return vec![format!("{stem}.d{extension}.ts")];
        }
        let stem = extension.map_or_else(
            || normalized.as_str(),
            |extension| &normalized[..normalized.len() - extension.len()],
        );
        let endings: &[&str] = match extension {
            Some(".mjs" | ".mts" | ".d.mts") => &[".mts", ".d.mts", ".mjs"],
            Some(".cjs" | ".cts" | ".d.cts") => &[".cts", ".d.cts", ".cjs"],
            Some(".tsx" | ".jsx") => &[".tsx", ".ts", ".d.ts", ".jsx", ".js"],
            Some(".ts" | ".d.ts" | ".js") | None => {
                if self.resolver.options.allow_javascript {
                    &[".ts", ".tsx", ".d.ts", ".js", ".jsx"]
                } else {
                    &[".ts", ".tsx", ".d.ts"]
                }
            }
            Some(".json") if self.resolver.options.resolve_json => &[".d.json.ts", ".json"],
            Some(extension) if self.resolver.options.allow_arbitrary_extensions => {
                return vec![format!("{stem}.d{extension}.ts")];
            }
            Some(_) => &[".d.ts"],
        };
        endings
            .iter()
            .map(|ending| format!("{stem}{ending}"))
            .collect()
    }

    fn read_package_json(&mut self, path: &str) -> Option<PackageJson> {
        if !self.resolver.file_system.file_exists(path) {
            self.failed(FailedLookupKind::PackageJson, path);
            return None;
        }
        let contents = self.resolver.file_system.read_file(path).ok()?;
        parse_package_json(&contents).ok()
    }

    fn failed(&mut self, kind: FailedLookupKind, path: &str) {
        self.failed_lookups.push(FailedLookup {
            kind,
            path: normalize_path(path),
        });
    }
}

/// Parses the package fields used by foundational Node resolution.
///
/// # Errors
///
/// Returns `serde_json::Error` when `contents` is not valid JSON.
pub fn parse_package_json(contents: &str) -> serde_json::Result<PackageJson> {
    let value: Value = serde_json::from_str(contents)?;
    Ok(PackageJson {
        types: string_field(&value, "types"),
        typings: string_field(&value, "typings"),
        main: string_field(&value, "main"),
        package_type: string_field(&value, "type"),
        exports: value.get("exports").cloned(),
        types_versions: value.get("typesVersions").cloned(),
        name: string_field(&value, "name"),
        imports: value.get("imports").cloned(),
    })
}

fn best_path_match(
    paths: &BTreeMap<String, Vec<String>>,
    specifier: &str,
) -> Option<(String, Vec<String>)> {
    paths
        .iter()
        .filter_map(|(pattern, substitutions)| {
            match_pattern(pattern, specifier).map(|capture| {
                (
                    pattern.len().saturating_sub(1),
                    capture,
                    substitutions.as_slice(),
                )
            })
        })
        .max_by_key(|(specificity, _, _)| *specificity)
        .map(|(_, capture, substitutions)| (capture.to_owned(), substitutions.to_vec()))
}

fn match_pattern<'a>(pattern: &str, value: &'a str) -> Option<&'a str> {
    let Some(star) = pattern.find('*') else {
        return (pattern == value).then_some("");
    };
    let (prefix, suffix_with_star) = pattern.split_at(star);
    let suffix = &suffix_with_star[1..];
    value
        .strip_prefix(prefix)?
        .strip_suffix(suffix)
        .filter(|_| value.len() >= prefix.len() + suffix.len())
}

fn path_suffix<'a>(path: &'a str, root: &str) -> Option<&'a str> {
    let suffix = path.strip_prefix(root)?;
    if suffix.is_empty() {
        Some("")
    } else {
        suffix.strip_prefix('/')
    }
}

fn package_export_target(exports: &Value, key: &str, prefer_types: bool) -> Option<String> {
    if let Some(object) = exports.as_object() {
        if object.keys().any(|name| name.starts_with('.')) {
            if let Some(value) = object.get(key) {
                return select_export_condition(value, prefer_types).map(str::to_owned);
            }
            let (value, capture) = wildcard_export(object, key)?;
            return select_export_condition(value, prefer_types)
                .map(|target| target.replace('*', &capture));
        }
        return select_export_condition(exports, prefer_types).map(str::to_owned);
    }
    (key == ".")
        .then(|| select_export_condition(exports, prefer_types))
        .flatten()
        .map(str::to_owned)
}

fn package_map_target(map: &Value, key: &str, prefer_types: bool) -> Option<String> {
    let object = map.as_object()?;
    if let Some(value) = object.get(key) {
        return select_export_condition(value, prefer_types).map(str::to_owned);
    }
    let (value, capture) = wildcard_export(object, key)?;
    select_export_condition(value, prefer_types).map(|target| target.replace('*', &capture))
}

fn types_package_name(specifier: &str) -> Option<String> {
    if specifier.starts_with("@types/") || specifier.starts_with('#') {
        return None;
    }
    let (package, rest) = parse_package_name(specifier)?;
    let package = package
        .strip_prefix('@')
        .map_or_else(|| package.to_owned(), |name| name.replace('/', "__"));
    Some(if rest.is_empty() {
        format!("@types/{package}")
    } else {
        format!("@types/{package}/{rest}")
    })
}

/// Returns explicit type roots or ancestor `node_modules/@types` directories.
#[must_use]
pub fn effective_type_roots(options: &ResolutionOptions, current_directory: &str) -> Vec<String> {
    options.type_roots.clone().unwrap_or_else(|| {
        ancestors(current_directory)
            .into_iter()
            .map(|directory| join(&join(&directory, "node_modules"), "@types"))
            .collect()
    })
}

/// Lists automatic type directive package names in stable order.
#[must_use]
pub fn automatic_type_directive_names(
    file_system: &dyn FileSystem,
    options: &ResolutionOptions,
    current_directory: &str,
) -> Vec<String> {
    if let Some(types) = &options.types
        && !types.iter().any(|name| name == "*")
    {
        return types.clone();
    }
    let mut installed = Vec::new();
    let mut seen = BTreeSet::new();
    for root in effective_type_roots(options, current_directory) {
        if let Ok(entries) = file_system.read_directory(&root) {
            for name in entries.directories {
                let package_json = join(&join(&root, &name), "package.json");
                let is_not_needed = file_system
                    .read_file(&package_json)
                    .ok()
                    .and_then(|contents| serde_json::from_str::<Value>(&contents).ok())
                    .is_some_and(|package| package.get("typings").is_some_and(Value::is_null));
                if !name.starts_with('.') && !is_not_needed && seen.insert(name.clone()) {
                    installed.push(name);
                }
            }
        }
    }
    let names = options.types.as_ref().map_or_else(
        || installed.clone(),
        |types| {
            types
                .iter()
                .flat_map(|name| {
                    if name == "*" {
                        installed.clone()
                    } else {
                        vec![name.clone()]
                    }
                })
                .collect()
        },
    );
    let mut seen = BTreeSet::new();
    names
        .into_iter()
        .filter(|name| seen.insert(name.clone()))
        .collect()
}

fn wildcard_export<'a>(
    exports: &'a serde_json::Map<String, Value>,
    key: &str,
) -> Option<(&'a Value, String)> {
    exports
        .iter()
        .filter_map(|(pattern, value)| {
            match_pattern(pattern, key).map(|capture| (pattern.len(), value, capture))
        })
        .max_by_key(|(specificity, _, _)| *specificity)
        .map(|(_, value, capture)| (value, capture.to_owned()))
}

fn select_export_condition(value: &Value, prefer_types: bool) -> Option<&str> {
    if let Some(target) = value.as_str() {
        return Some(target);
    }
    if let Some(targets) = value.as_array() {
        return targets
            .iter()
            .find_map(|target| select_export_condition(target, prefer_types));
    }
    let object = value.as_object()?;
    let conditions: &[&str] = if prefer_types {
        &["types", "import", "require", "default"]
    } else {
        &["import", "require", "default", "types"]
    };
    conditions
        .iter()
        .find_map(|condition| object.get(*condition))
        .and_then(|value| select_export_condition(value, prefer_types))
}

fn types_version_targets(types_versions: &Value, rest: &str) -> Option<Vec<String>> {
    let versions = types_versions.as_object()?;
    let compiler_version = Version::parse(env!("CARGO_PKG_VERSION")).ok()?;
    let mapping = versions.iter().find_map(|(range, mapping)| {
        VersionRange::parse(range)
            .ok()
            .filter(|range| range.test(&compiler_version))
            .and_then(|_| mapping.as_object())
    })?;
    let (_, capture, targets) = mapping
        .iter()
        .filter_map(|(pattern, targets)| {
            match_pattern(pattern, rest)
                .map(|capture| (pattern.len().saturating_sub(1), capture, targets.as_array()))
        })
        .max_by_key(|(specificity, _, _)| *specificity)?;
    Some(
        targets?
            .iter()
            .filter_map(Value::as_str)
            .map(|target| target.replace('*', capture))
            .collect(),
    )
}

fn string_field(value: &Value, field: &str) -> Option<String> {
    value.get(field)?.as_str().map(str::to_owned)
}

fn source_extension(path: &str) -> Option<&'static str> {
    [
        ".d.mts", ".d.cts", ".d.ts", ".mjs", ".mts", ".cjs", ".cts", ".tsx", ".jsx", ".json",
        ".ts", ".js",
    ]
    .into_iter()
    .find(|extension| path.ends_with(extension))
}

fn parse_package_name(specifier: &str) -> Option<(&str, &str)> {
    if specifier.starts_with('#') {
        return None;
    }
    if let Some(scoped) = specifier.strip_prefix('@') {
        let first_slash = scoped.find('/')? + 1;
        let after_scope = &specifier[first_slash + 1..];
        let package_end = after_scope
            .find('/')
            .map_or(specifier.len(), |index| first_slash + 1 + index);
        let package_name = &specifier[..package_end];
        let rest = specifier.get(package_end + 1..).unwrap_or("");
        Some((package_name, rest))
    } else {
        let package_end = specifier.find('/').unwrap_or(specifier.len());
        let package_name = &specifier[..package_end];
        if package_name.is_empty() {
            return None;
        }
        let rest = specifier.get(package_end + 1..).unwrap_or("");
        Some((package_name, rest))
    }
}

fn directory_path(path: &str) -> String {
    let normalized = normalize_path(path);
    let root = root_length(&normalized);
    let trimmed = normalized.trim_end_matches('/');
    let last_slash = trimmed.rfind('/').unwrap_or(root.saturating_sub(1));
    if last_slash < root {
        normalized[..root].to_owned()
    } else {
        normalized[..last_slash].to_owned()
    }
}

fn join(left: &str, right: &str) -> String {
    resolve_path(left, &[right])
}

fn ancestors(path: &str) -> Vec<String> {
    let mut result = Vec::new();
    let normalized = normalize_path(path);
    let root = root_length(&normalized);
    let mut current = if normalized.len() == root {
        normalized
    } else {
        normalized.trim_end_matches('/').to_owned()
    };
    loop {
        result.push(current.clone());
        let parent = directory_path(&current);
        if parent == current || parent.len() < root_length(&current) {
            break;
        }
        current = parent;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use ts_vfs::MemoryFileSystem;

    fn fs(files: &[(&str, &str)]) -> MemoryFileSystem {
        let fs = MemoryFileSystem::new(true);
        for (path, contents) in files {
            fs.write_file(path, contents).unwrap();
        }
        fs
    }

    #[test]
    fn resolves_relative_files_with_typescript_substitution() {
        let fs = fs(&[("/src/lib.ts", "")]);
        let result =
            Resolver::new(&fs, ResolutionOptions::default()).resolve("./lib.js", "/src/main.ts");
        let resolved = result.resolved.unwrap();
        assert_eq!(resolved.resolved_file_name, "/src/lib.ts");
        assert_eq!(resolved.extension, Some(FileExtension::Ts));
        assert!(!resolved.is_external_library_import);
    }

    #[test]
    fn resolves_scoped_packages_from_the_filesystem_root() {
        let fs = fs(&[(
            "/node_modules/@fullcalendar/react/index.d.ts",
            "export default class FullCalendar {}",
        )]);
        let result = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                ..ResolutionOptions::default()
            },
        )
        .resolve("@fullcalendar/react", "/index.tsx");
        assert_eq!(
            result.resolved.unwrap().resolved_file_name,
            "/node_modules/@fullcalendar/react/index.d.ts"
        );
    }

    #[test]
    fn uses_package_typings_then_main_and_index() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"typings":"types/entry.d.ts","main":"dist/main.js"}"#,
            ),
            ("/app/node_modules/pkg/types/entry.d.ts", ""),
            (
                "/app/node_modules/typepkg/package.json",
                r#"{"types":"types.d.ts","main":"runtime.js"}"#,
            ),
            ("/app/node_modules/typepkg/types.d.ts", ""),
            (
                "/app/node_modules/mainpkg/package.json",
                r#"{"main":"dist/main.js"}"#,
            ),
            ("/app/node_modules/mainpkg/dist/main.ts", ""),
            ("/app/node_modules/fallback/index.ts", ""),
        ]);
        let resolver = Resolver::new(&fs, ResolutionOptions::default());
        let package = resolver
            .resolve("pkg", "/app/src/main.ts")
            .resolved
            .unwrap();
        assert_eq!(
            package.resolved_file_name,
            "/app/node_modules/pkg/types/entry.d.ts"
        );
        assert!(package.is_external_library_import);
        let types = resolver
            .resolve("typepkg", "/app/src/main.ts")
            .resolved
            .unwrap();
        assert_eq!(
            types.resolved_file_name,
            "/app/node_modules/typepkg/types.d.ts"
        );
        let main = resolver
            .resolve("mainpkg", "/app/src/main.ts")
            .resolved
            .unwrap();
        assert_eq!(
            main.resolved_file_name,
            "/app/node_modules/mainpkg/dist/main.ts"
        );
        let fallback = resolver
            .resolve("fallback", "/app/src/main.ts")
            .resolved
            .unwrap();
        assert_eq!(
            fallback.resolved_file_name,
            "/app/node_modules/fallback/index.ts"
        );
    }

    #[test]
    fn walks_node_modules_ancestors_and_resolves_subpaths() {
        let fs = fs(&[("/repo/node_modules/@scope/pkg/subpath.ts", "")]);
        let result = Resolver::new(&fs, ResolutionOptions::default())
            .resolve("@scope/pkg/subpath", "/repo/packages/app/src/main.ts");
        assert_eq!(
            result.resolved.unwrap().resolved_file_name,
            "/repo/node_modules/@scope/pkg/subpath.ts"
        );
    }

    #[test]
    fn records_failed_file_directory_and_package_lookups() {
        let fs = MemoryFileSystem::new(true);
        let result =
            Resolver::new(&fs, ResolutionOptions::default()).resolve("./missing", "/src/main.ts");
        assert!(result.resolved.is_none());
        assert!(result.failed_lookups.iter().any(|lookup| {
            lookup.kind == FailedLookupKind::File && lookup.path == "/src/missing.ts"
        }));
        assert!(result.failed_lookups.iter().any(|lookup| {
            lookup.kind == FailedLookupKind::Directory && lookup.path == "/src/missing"
        }));
    }

    #[test]
    fn honors_javascript_and_json_options() {
        let fs = fs(&[("/src/value.js", ""), ("/src/data.json", "{}")]);
        let no_js = ResolutionOptions {
            allow_javascript: false,
            ..ResolutionOptions::default()
        };
        assert!(
            Resolver::new(&fs, no_js)
                .resolve("./value", "/src/main.ts")
                .resolved
                .is_none()
        );
        let json = ResolutionOptions {
            resolve_json: true,
            ..ResolutionOptions::default()
        };
        assert_eq!(
            Resolver::new(&fs, json)
                .resolve("./data.json", "/src/main.ts")
                .resolved
                .unwrap()
                .extension,
            Some(FileExtension::Json)
        );
    }

    #[test]
    fn resolves_arbitrary_extensions_to_declaration_companions() {
        let fs = fs(&[("/src/data.d.html.ts", "")]);
        let options = ResolutionOptions {
            allow_arbitrary_extensions: true,
            ..ResolutionOptions::default()
        };
        assert_eq!(
            Resolver::new(&fs, options)
                .resolve("./data.html", "/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/src/data.d.html.ts"
        );
    }

    #[test]
    fn resolves_base_url_paths_with_wildcards_and_fallbacks() {
        let fs = fs(&[
            ("/repo/src/lib/exact.ts", ""),
            ("/repo/generated/models/user.ts", ""),
            ("/repo/src/plain.ts", ""),
        ]);
        let options = ResolutionOptions {
            base_url: Some("/repo".into()),
            paths: BTreeMap::from([
                (
                    "@lib/exact".into(),
                    vec!["missing.ts".into(), "src/lib/exact".into()],
                ),
                ("@models/*".into(), vec!["generated/models/*".into()]),
            ]),
            ..ResolutionOptions::default()
        };
        let resolver = Resolver::new(&fs, options);
        assert_eq!(
            resolver
                .resolve("@lib/exact", "/repo/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/src/lib/exact.ts"
        );
        assert_eq!(
            resolver
                .resolve("@models/user", "/repo/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/generated/models/user.ts"
        );
        assert_eq!(
            resolver
                .resolve("src/plain", "/repo/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/src/plain.ts"
        );
    }

    #[test]
    fn resolves_rooted_specifiers_through_paths_with_real_root_fallback() {
        let fs = fs(&[("/repo/src/foo.ts", ""), ("/bar.ts", "")]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                base_url: Some("/repo".into()),
                paths: BTreeMap::from([("/*".into(), vec!["./src/*".into()])]),
                ..ResolutionOptions::default()
            },
        );
        assert_eq!(
            resolver
                .resolve("/foo", "/repo/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/src/foo.ts"
        );
        assert_eq!(
            resolver
                .resolve("/bar", "/repo/app/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/bar.ts"
        );
    }

    #[test]
    fn resolves_relative_modules_across_root_dirs() {
        let fs = fs(&[("/generated/views/template.ts", "")]);
        let options = ResolutionOptions {
            root_dirs: vec!["/src".into(), "/generated".into()],
            ..ResolutionOptions::default()
        };
        let result = Resolver::new(&fs, options).resolve("./template", "/src/views/page.ts");
        assert_eq!(
            result.resolved.unwrap().resolved_file_name,
            "/generated/views/template.ts"
        );
    }

    #[test]
    fn resolves_package_exports_and_types_conditions() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"exports":{".":{"types":"./types/index.d.ts","default":"./dist/index.js"},"./features/*":{"types":"./types/features/*.d.ts","default":"./dist/features/*.js"}}}"#,
            ),
            ("/app/node_modules/pkg/types/index.d.ts", ""),
            ("/app/node_modules/pkg/types/features/tool.d.ts", ""),
            ("/app/node_modules/pkg/private.ts", ""),
        ]);
        let options = ResolutionOptions {
            mode: ResolutionMode::NodeNext,
            ..ResolutionOptions::default()
        };
        let resolver = Resolver::new(&fs, options);
        assert_eq!(
            resolver
                .resolve("pkg", "/app/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/types/index.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("pkg/features/tool", "/app/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/types/features/tool.d.ts"
        );
        assert!(
            resolver
                .resolve("pkg/private", "/app/src/main.ts")
                .resolved
                .is_none()
        );
    }

    #[test]
    fn resolves_package_types_versions_subpaths() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"typesVersions":{"<7":{"feature/*":["old/feature/*"]},">=7":{"feature/*":["types/feature/*"],"*":["types/*"]}}}"#,
            ),
            ("/app/node_modules/pkg/old/feature/tool.d.ts", ""),
            ("/app/node_modules/pkg/types/feature/tool.d.ts", ""),
        ]);
        let resolved = Resolver::new(&fs, ResolutionOptions::default())
            .resolve("pkg/feature/tool", "/app/src/main.ts")
            .resolved
            .unwrap();
        assert_eq!(
            resolved.resolved_file_name,
            "/app/node_modules/pkg/types/feature/tool.d.ts"
        );
        assert_eq!(
            resolved.package_json.as_deref(),
            Some("/app/node_modules/pkg/package.json")
        );
    }

    #[test]
    fn resolves_package_types_versions_root_entry() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"types":"index","typesVersions":{">=7":{"*":["types/*"]}}}"#,
            ),
            ("/app/node_modules/pkg/index.d.ts", ""),
            ("/app/node_modules/pkg/types/index.d.ts", ""),
        ]);
        let resolver = Resolver::new(&fs, ResolutionOptions::default());
        let resolution = resolver
            .resolve("pkg", "/app/src/main.ts")
            .resolved
            .unwrap();
        assert_eq!(
            resolution.resolved_file_name,
            "/app/node_modules/pkg/types/index.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("../", "/app/node_modules/pkg/types/index.d.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/pkg/types/index.d.ts"
        );
    }

    #[test]
    fn node16_resolves_package_imports_and_patterns() {
        let fs = fs(&[
            (
                "/repo/package.json",
                r##"{"imports":{"#core":{"types":"./types/core.d.ts"},"#features/*":"./types/features/*.d.ts"}}"##,
            ),
            ("/repo/types/core.d.ts", ""),
            ("/repo/types/features/tool.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Node16,
                ..ResolutionOptions::default()
            },
        );
        assert_eq!(
            resolver
                .resolve("#core", "/repo/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/types/core.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("#features/tool", "/repo/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/types/features/tool.d.ts"
        );
    }

    #[test]
    fn nodenext_resolves_package_self_name_exports() {
        let fs = fs(&[
            (
                "/repo/package.json",
                r#"{"name":"workspace-pkg","exports":{".":{"types":"./types/index.d.ts"},"./feature":"./types/feature.d.ts"}}"#,
            ),
            ("/repo/types/index.d.ts", ""),
            ("/repo/types/feature.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::NodeNext,
                ..ResolutionOptions::default()
            },
        );
        assert_eq!(
            resolver
                .resolve("workspace-pkg/feature", "/repo/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/types/feature.d.ts"
        );
    }

    #[test]
    fn bundler_falls_back_to_at_types_and_custom_type_roots() {
        let fs = fs(&[
            (
                "/app/node_modules/pkg/package.json",
                r#"{"main":"index.js"}"#,
            ),
            ("/app/node_modules/pkg/index.js", ""),
            ("/app/node_modules/@types/pkg/index.d.ts", ""),
            ("/custom/types/ambient/index.d.ts", ""),
        ]);
        let resolver = Resolver::new(
            &fs,
            ResolutionOptions {
                mode: ResolutionMode::Bundler,
                allow_javascript: false,
                type_roots: Some(vec!["/custom/types".into()]),
                ..ResolutionOptions::default()
            },
        );
        assert_eq!(
            resolver
                .resolve("pkg", "/app/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/app/node_modules/@types/pkg/index.d.ts"
        );
        assert_eq!(
            resolver
                .resolve("ambient", "/app/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/custom/types/ambient/index.d.ts"
        );
    }

    #[test]
    fn discovers_automatic_types_and_caches_resolution_results() {
        let fs = fs(&[
            ("/repo/node_modules/@types/node/index.d.ts", ""),
            ("/repo/node_modules/@types/jest/index.d.ts", ""),
            (
                "/repo/node_modules/@types/obsolete/package.json",
                r#"{"typings":null}"#,
            ),
        ]);
        let options = ResolutionOptions::default();
        assert_eq!(
            automatic_type_directive_names(&fs, &options, "/repo/src"),
            ["jest", "node"]
        );
        let selected = ResolutionOptions {
            types: Some(vec!["custom".into(), "*".into(), "node".into()]),
            ..ResolutionOptions::default()
        };
        assert_eq!(
            automatic_type_directive_names(&fs, &selected, "/repo/src"),
            ["custom", "jest", "node"]
        );
        let resolver = Resolver::new(&fs, options);
        assert!(
            resolver
                .resolve("./later", "/repo/src/main.ts")
                .resolved
                .is_none()
        );
        fs.write_file("/repo/src/later.ts", "").unwrap();
        assert!(
            resolver
                .resolve("./later", "/repo/src/main.ts")
                .resolved
                .is_none()
        );
        resolver.clear_cache();
        assert_eq!(
            resolver
                .resolve("./later", "/repo/src/main.ts")
                .resolved
                .unwrap()
                .resolved_file_name,
            "/repo/src/later.ts"
        );
    }
}
