//! TypeScript-compatible wildcard matching and config file discovery.

use std::collections::{HashMap, HashSet};
use std::io;

use ts_path::{
    CaseSensitivity, FileExtension, SUPPORTED_TS_EXTENSIONS, canonical_file_name, normalize_path,
    resolve_path,
};
use ts_vfs::FileSystem;

#[derive(Clone, Debug, Eq, PartialEq)]
enum Component {
    Literal(String),
    Wildcard(String),
    Recursive,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GlobPattern {
    components: Vec<Component>,
    case_sensitive: bool,
    exclude: bool,
}

impl GlobPattern {
    #[must_use]
    pub fn compile(
        spec: &str,
        base_path: &str,
        case_sensitive: bool,
        exclude: bool,
    ) -> Option<Self> {
        let spec = resolve_path(base_path, &[spec]);
        let mut parts: Vec<String> = spec
            .split('/')
            .filter(|part| !part.is_empty() && *part != ".")
            .map(str::to_owned)
            .collect();
        if !exclude && parts.last().is_some_and(|part| part == "**") {
            return None;
        }
        if parts
            .last()
            .is_some_and(|part| !part.contains(['.', '*', '?']))
        {
            parts.extend(["**".to_owned(), "*".to_owned()]);
        }
        let components = parts
            .into_iter()
            .map(|part| {
                if part == "**" {
                    Component::Recursive
                } else if part.contains(['*', '?']) {
                    Component::Wildcard(part)
                } else {
                    Component::Literal(part)
                }
            })
            .collect();
        Some(Self {
            components,
            case_sensitive,
            exclude,
        })
    }

    #[must_use]
    pub fn matches(&self, path: &str) -> bool {
        let normalized = normalize_path(path);
        let parts: Vec<&str> = normalized
            .split('/')
            .filter(|part| !part.is_empty())
            .collect();
        let mut memo = HashMap::new();
        self.matches_from(&parts, 0, 0, &mut memo)
    }

    fn matches_from(
        &self,
        path: &[&str],
        path_index: usize,
        pattern_index: usize,
        memo: &mut HashMap<(usize, usize), bool>,
    ) -> bool {
        if let Some(result) = memo.get(&(path_index, pattern_index)) {
            return *result;
        }
        let result = if pattern_index == self.components.len() {
            path_index == path.len() || self.exclude
        } else {
            match &self.components[pattern_index] {
                Component::Recursive => {
                    self.matches_from(path, path_index, pattern_index + 1, memo)
                        || path.get(path_index).is_some_and(|part| {
                            (self.exclude || !is_implicit_excluded_component(part))
                                && self.matches_from(path, path_index + 1, pattern_index, memo)
                        })
                }
                Component::Literal(literal) => path.get(path_index).is_some_and(|part| {
                    self.equal(literal, part)
                        && self.matches_from(path, path_index + 1, pattern_index + 1, memo)
                }),
                Component::Wildcard(wildcard) => path.get(path_index).is_some_and(|part| {
                    (self.exclude || !is_package_folder(part))
                        && (self.exclude || !part.starts_with('.') || wildcard.starts_with('.'))
                        && wildcard_component_matches(wildcard, part, self.case_sensitive)
                        && (self.exclude
                            || path_index + 1 != path.len()
                            || should_include_file(wildcard, part, self.case_sensitive))
                        && self.matches_from(path, path_index + 1, pattern_index + 1, memo)
                }),
            }
        };
        memo.insert((path_index, pattern_index), result);
        result
    }

    fn equal(&self, left: &str, right: &str) -> bool {
        if self.case_sensitive {
            left == right
        } else {
            canonical_file_name(left, CaseSensitivity::Insensitive)
                == canonical_file_name(right, CaseSensitivity::Insensitive)
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DiscoveryOptions {
    pub base_path: String,
    pub files: Vec<String>,
    pub include: Vec<String>,
    pub exclude: Vec<String>,
    pub extensions: Vec<FileExtension>,
}

impl DiscoveryOptions {
    #[must_use]
    pub fn new(base_path: impl Into<String>) -> Self {
        Self {
            base_path: base_path.into(),
            files: Vec::new(),
            include: vec!["**/*".to_owned()],
            exclude: Vec::new(),
            extensions: SUPPORTED_TS_EXTENSIONS.to_vec(),
        }
    }
}

/// Discovers configuration input files using the supplied virtual filesystem.
///
/// # Errors
///
/// Returns an I/O error when a directory required by traversal cannot be read.
pub fn discover_files<F: FileSystem + ?Sized>(
    file_system: &F,
    options: &DiscoveryOptions,
) -> io::Result<Vec<String>> {
    let base = normalize_path(&options.base_path);
    let case_sensitive = file_system.use_case_sensitive_file_names();
    let mut includes = Vec::new();
    let mut traversal_roots = Vec::new();
    let mut seen_roots = HashSet::new();
    for spec in &options.include {
        if let Some(pattern) = GlobPattern::compile(spec, &base, case_sensitive, false) {
            let root = include_traversal_root(file_system, spec, &base, case_sensitive);
            if seen_roots.insert(canonical(&root, case_sensitive)) {
                traversal_roots.push(root);
            }
            includes.push(pattern);
        }
    }
    let excludes: Vec<_> = options
        .exclude
        .iter()
        .filter_map(|spec| GlobPattern::compile(spec, &base, case_sensitive, true))
        .collect();

    let mut seen = HashSet::new();
    let mut result = Vec::new();
    for file in &options.files {
        let absolute = resolve_path(&base, &[file]);
        if seen.insert(canonical(&absolute, case_sensitive)) {
            result.push(absolute);
        }
    }

    let mut buckets = vec![Vec::new(); includes.len().max(1)];
    let mut visited = HashSet::new();
    for root in traversal_roots {
        if file_system.directory_exists(&root) {
            visit(
                file_system,
                &root,
                &includes,
                &excludes,
                &options.extensions,
                &mut buckets,
                &mut visited,
            )?;
        }
    }
    for bucket in buckets {
        for file in bucket {
            if seen.insert(canonical(&file, case_sensitive)) {
                result.push(file);
            }
        }
    }
    Ok(result)
}

fn visit<F: FileSystem + ?Sized>(
    file_system: &F,
    directory: &str,
    includes: &[GlobPattern],
    excludes: &[GlobPattern],
    extensions: &[FileExtension],
    buckets: &mut [Vec<String>],
    visited: &mut HashSet<String>,
) -> io::Result<()> {
    let canonical_directory = canonical(
        &file_system.realpath(directory),
        file_system.use_case_sensitive_file_names(),
    );
    if !visited.insert(canonical_directory) {
        return Ok(());
    }
    let mut entries = file_system.read_directory(directory)?;
    entries.files.sort();
    entries.directories.sort();
    for file in entries.files {
        if !has_allowed_extension(&file, extensions) {
            continue;
        }
        let absolute = join(directory, &file);
        if excludes.iter().any(|pattern| pattern.matches(&absolute)) {
            continue;
        }
        let include_index = includes
            .iter()
            .position(|pattern| pattern.matches(&absolute));
        if let Some(index) = include_index {
            buckets[index].push(absolute);
        }
    }
    for child in entries.directories {
        let absolute = join(directory, &child);
        if excludes.iter().any(|pattern| pattern.matches(&absolute)) {
            continue;
        }
        visit(
            file_system,
            &absolute,
            includes,
            excludes,
            extensions,
            buckets,
            visited,
        )?;
    }
    Ok(())
}

fn include_traversal_root<F: FileSystem + ?Sized>(
    file_system: &F,
    spec: &str,
    base: &str,
    case_sensitive: bool,
) -> String {
    let normalized = resolve_path(base, &[spec]);
    if contains_path(base, &normalized, case_sensitive) {
        return base.to_owned();
    }
    if let Some(wildcard) = normalized.find(['*', '?']) {
        let prefix = &normalized[..wildcard];
        if prefix.ends_with('/') {
            let root = prefix.trim_end_matches('/');
            return if root.is_empty() { "/" } else { root }.to_owned();
        }
        return prefix.rsplit_once('/').map_or_else(
            || "/".to_owned(),
            |(directory, _)| {
                if directory.is_empty() {
                    "/".to_owned()
                } else {
                    directory.to_owned()
                }
            },
        );
    }
    if file_system.directory_exists(&normalized) {
        normalized
    } else {
        normalized.rsplit_once('/').map_or_else(
            || base.to_owned(),
            |(directory, _)| {
                if directory.is_empty() {
                    "/".to_owned()
                } else {
                    directory.to_owned()
                }
            },
        )
    }
}

fn contains_path(directory: &str, path: &str, case_sensitive: bool) -> bool {
    let directory = canonical(directory, case_sensitive);
    let path = canonical(path, case_sensitive);
    path == directory
        || path
            .strip_prefix(&directory)
            .is_some_and(|remainder| directory.ends_with('/') || remainder.starts_with('/'))
}

fn wildcard_component_matches(pattern: &str, value: &str, case_sensitive: bool) -> bool {
    let pattern: Vec<char> = pattern.chars().collect();
    let value: Vec<char> = value.chars().collect();
    let mut previous = vec![false; value.len() + 1];
    previous[0] = true;
    for pattern_char in pattern {
        let mut current = vec![false; value.len() + 1];
        if pattern_char == '*' {
            current[0] = previous[0];
            for index in 1..=value.len() {
                current[index] = previous[index] || current[index - 1];
            }
        } else {
            for index in 1..=value.len() {
                current[index] = previous[index - 1]
                    && (pattern_char == '?'
                        || chars_equal(pattern_char, value[index - 1], case_sensitive));
            }
        }
        previous = current;
    }
    previous[value.len()]
}

fn chars_equal(left: char, right: char, case_sensitive: bool) -> bool {
    left == right
        || !case_sensitive
            && canonical_file_name(&left.to_string(), CaseSensitivity::Insensitive)
                == canonical_file_name(&right.to_string(), CaseSensitivity::Insensitive)
}

fn should_include_file(pattern: &str, file_name: &str, case_sensitive: bool) -> bool {
    let has_min_suffix = if case_sensitive {
        file_name.ends_with(".min.js")
    } else {
        file_name
            .get(file_name.len().saturating_sub(".min.js".len())..)
            .is_some_and(|suffix| suffix.eq_ignore_ascii_case(".min.js"))
    };
    if !has_min_suffix {
        return true;
    }
    let pattern = if case_sensitive {
        pattern.to_owned()
    } else {
        pattern.to_ascii_lowercase()
    };
    pattern.contains(".min.js") || pattern.contains(".min.")
}

fn has_allowed_extension(file: &str, extensions: &[FileExtension]) -> bool {
    extensions.iter().any(|extension| {
        let extension = extension.as_str();
        file.len() > extension.len() && file.get(file.len() - extension.len()..) == Some(extension)
    })
}

fn is_implicit_excluded_component(component: &str) -> bool {
    component.starts_with('.') || is_package_folder(component)
}

fn is_package_folder(component: &str) -> bool {
    ["node_modules", "bower_components", "jspm_packages"]
        .into_iter()
        .any(|folder| component.eq_ignore_ascii_case(folder))
}

fn canonical(path: &str, case_sensitive: bool) -> String {
    canonical_file_name(
        path,
        if case_sensitive {
            CaseSensitivity::Sensitive
        } else {
            CaseSensitivity::Insensitive
        },
    )
}

fn join(directory: &str, name: &str) -> String {
    resolve_path(directory, &[name])
}

#[cfg(test)]
mod tests {
    use super::*;
    use ts_vfs::MemoryFileSystem;

    fn file_system(case_sensitive: bool, files: &[&str]) -> MemoryFileSystem {
        let fs = MemoryFileSystem::new(case_sensitive);
        for file in files {
            fs.write_file(file, "").unwrap();
        }
        fs
    }

    #[test]
    fn supports_star_question_and_recursive_wildcards() {
        let fs = file_system(true, &["/dev/x/a.ts", "/dev/x/ab.ts", "/dev/x/y/a.ts"]);
        let mut options = DiscoveryOptions::new("/dev");
        options.include = vec!["x/?.ts".into(), "x/**/a.ts".into()];
        assert_eq!(
            discover_files(&fs, &options).unwrap(),
            vec!["/dev/x/a.ts", "/dev/x/y/a.ts"]
        );
    }

    #[test]
    fn directory_include_is_implicitly_recursive() {
        let fs = file_system(true, &["/dev/src/a.ts", "/dev/src/nested/b.ts"]);
        let mut options = DiscoveryOptions::new("/dev");
        options.include = vec!["src".into()];
        assert_eq!(
            discover_files(&fs, &options).unwrap(),
            vec!["/dev/src/a.ts", "/dev/src/nested/b.ts"]
        );
    }

    #[test]
    fn wildcard_includes_skip_package_and_hidden_folders() {
        let fs = file_system(
            true,
            &["/dev/a.ts", "/dev/node_modules/a.ts", "/dev/.cache/a.ts"],
        );
        let options = DiscoveryOptions::new("/dev");
        assert_eq!(discover_files(&fs, &options).unwrap(), vec!["/dev/a.ts"]);

        let mut explicit = DiscoveryOptions::new("/dev");
        explicit.include = vec!["node_modules/a.ts".into(), ".cache/a.ts".into()];
        assert_eq!(
            discover_files(&fs, &explicit).unwrap(),
            vec!["/dev/node_modules/a.ts", "/dev/.cache/a.ts"]
        );
    }

    #[test]
    fn files_are_literal_and_take_precedence_over_excludes() {
        let fs = file_system(true, &["/dev/src/a.ts", "/dev/src/b.ts"]);
        let mut options = DiscoveryOptions::new("/dev");
        options.files = vec!["src/a.ts".into(), "missing.custom".into()];
        options.include = vec!["src/*.ts".into()];
        options.exclude = vec!["src/a.ts".into()];
        assert_eq!(
            discover_files(&fs, &options).unwrap(),
            vec!["/dev/src/a.ts", "/dev/missing.custom", "/dev/src/b.ts"]
        );
    }

    #[test]
    fn filters_extensions_and_preserves_include_order() {
        let fs = file_system(true, &["/dev/x/a.ts", "/dev/x/a.js", "/dev/z/a.ts"]);
        let mut options = DiscoveryOptions::new("/dev");
        options.include = vec!["z/*.ts".into(), "x/*.ts".into()];
        assert_eq!(
            discover_files(&fs, &options).unwrap(),
            vec!["/dev/z/a.ts", "/dev/x/a.ts"]
        );
    }

    #[test]
    fn matching_obeys_file_system_case_sensitivity() {
        let insensitive = file_system(false, &["/Dev/Src/Main.ts"]);
        let mut options = DiscoveryOptions::new("/dev");
        options.include = vec!["src/main.ts".into()];
        assert_eq!(
            discover_files(&insensitive, &options).unwrap(),
            vec!["/dev/Src/Main.ts"]
        );

        let sensitive = file_system(true, &["/dev/Src/Main.ts"]);
        assert!(discover_files(&sensitive, &options).unwrap().is_empty());
    }

    #[test]
    fn matches_unicode_case_and_keeps_dotted_i_distinct() {
        let insensitive = file_system(
            false,
            &["/Dev/CAF\u{00c9}/Main.ts", "/Dev/\u{0130}/other.ts"],
        );
        let mut options = DiscoveryOptions::new("/dev");
        options.include = vec!["caf\u{00e9}/*.ts".into(), "i/*.ts".into()];

        assert_eq!(
            discover_files(&insensitive, &options).unwrap(),
            vec!["/dev/CAF\u{00c9}/Main.ts"]
        );
    }

    #[test]
    fn relative_patterns_can_include_sibling_directories() {
        let file_system = file_system(
            true,
            &[
                "/repo/app/local.ts",
                "/repo/shared/entry.ts",
                "/repo/shared/nested/deep.ts",
            ],
        );
        let mut options = DiscoveryOptions::new("/repo/app");
        options.include = vec!["../shared/**/*.ts".into(), "*.ts".into()];

        assert_eq!(
            discover_files(&file_system, &options).unwrap(),
            vec![
                "/repo/shared/entry.ts",
                "/repo/shared/nested/deep.ts",
                "/repo/app/local.ts"
            ]
        );
    }

    #[test]
    fn wildcard_javascript_patterns_skip_minified_files_unless_requested() {
        let file_system = file_system(
            false,
            &["/dev/app.js", "/dev/vendor.min.js", "/dev/other.MIN.js"],
        );
        let mut options = DiscoveryOptions::new("/dev");
        options.extensions = vec![FileExtension::Js];
        options.include = vec!["*.js".into()];
        assert_eq!(
            discover_files(&file_system, &options).unwrap(),
            vec!["/dev/app.js"]
        );

        options.include = vec!["*.min.js".into()];
        assert_eq!(
            discover_files(&file_system, &options).unwrap(),
            vec!["/dev/other.MIN.js", "/dev/vendor.min.js"]
        );
    }

    #[test]
    fn wildcard_question_marks_match_unicode_characters() {
        let file_system = file_system(
            true,
            &[
                "/dev/a.ts",
                "/dev/\u{00e9}.ts",
                "/dev/\u{1f389}.ts",
                "/dev/ab.ts",
            ],
        );
        let mut options = DiscoveryOptions::new("/dev");
        options.include = vec!["?.ts".into()];

        assert_eq!(
            discover_files(&file_system, &options).unwrap(),
            vec!["/dev/a.ts", "/dev/\u{00e9}.ts", "/dev/\u{1f389}.ts"]
        );
    }

    #[test]
    fn trailing_recursive_include_matches_nothing() {
        let fs = file_system(true, &["/dev/a.ts", "/dev/nested/b.ts"]);
        let mut options = DiscoveryOptions::new("/dev");
        options.include = vec!["**".into()];
        assert!(discover_files(&fs, &options).unwrap().is_empty());
    }

    #[test]
    fn discovers_absolute_patterns_across_config_directories() {
        let fs = file_system(
            true,
            &[
                "/repo/base/src/a.ts",
                "/repo/base/src/nested/b.ts",
                "/repo/base/src/generated/skip.ts",
                "/repo/app/local/c.ts",
                "/repo/app/local/skip/d.ts",
            ],
        );
        let mut options = DiscoveryOptions::new("/repo/app");
        options.include = vec![
            "/repo/base/src/**/*.ts".into(),
            "/repo/app/local/**/*.ts".into(),
        ];
        options.exclude = vec!["/repo/base/src/generated".into(), "local/skip".into()];
        assert_eq!(
            discover_files(&fs, &options).unwrap(),
            vec![
                "/repo/base/src/a.ts",
                "/repo/base/src/nested/b.ts",
                "/repo/app/local/c.ts"
            ]
        );
    }
}
