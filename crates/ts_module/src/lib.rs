//! Foundational TypeScript module resolution.

use serde_json::Value;
use ts_path::{FileExtension, is_absolute, is_relative, normalize_path, resolve_path, root_length};
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ResolutionOptions {
    pub mode: ResolutionMode,
    pub allow_javascript: bool,
    pub resolve_json: bool,
    pub prefer_types: bool,
}

impl Default for ResolutionOptions {
    fn default() -> Self {
        Self {
            mode: ResolutionMode::Node10,
            allow_javascript: true,
            resolve_json: false,
            prefer_types: true,
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
}

pub struct Resolver<'a, F: FileSystem + ?Sized> {
    file_system: &'a F,
    options: ResolutionOptions,
}

impl<'a, F: FileSystem + ?Sized> Resolver<'a, F> {
    #[must_use]
    pub const fn new(file_system: &'a F, options: ResolutionOptions) -> Self {
        Self {
            file_system,
            options,
        }
    }

    #[must_use]
    pub const fn options(&self) -> ResolutionOptions {
        self.options
    }

    #[must_use]
    pub fn resolve(&self, specifier: &str, containing_file: &str) -> ResolutionResult {
        let mut state = ResolutionState {
            resolver: self,
            failed_lookups: Vec::new(),
        };
        let containing_directory = directory_path(containing_file);
        let resolved = if is_relative(specifier) || is_absolute(specifier) {
            let candidate = resolve_path(&containing_directory, &[specifier]);
            state.resolve_candidate(&candidate, false)
        } else if self.options.mode == ResolutionMode::Classic {
            None
        } else {
            state.resolve_node_modules(specifier, &containing_directory)
        };
        ResolutionResult {
            resolved,
            failed_lookups: state.failed_lookups,
        }
    }
}

struct ResolutionState<'a, 'fs, F: FileSystem + ?Sized> {
    resolver: &'a Resolver<'fs, F>,
    failed_lookups: Vec<FailedLookup>,
}

impl<F: FileSystem + ?Sized> ResolutionState<'_, '_, F> {
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
                return Some(ResolvedModule {
                    extension: ts_path::extension_from_path(&path),
                    resolved_file_name: path,
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
    })
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
    let mut current = normalize_path(path).trim_end_matches('/').to_owned();
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
}
