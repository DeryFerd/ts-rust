//! TypeScript-compatible wildcard matching and config file discovery.

use std::collections::{HashMap, HashSet};
use std::io;

use ts_path::{FileExtension, SUPPORTED_TS_EXTENSIONS, is_absolute, normalize_path, resolve_path};
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
        let mut spec = normalize_path(spec);
        let base = normalize_path(base_path);
        if is_absolute(&spec) {
            spec = relative_to(&spec, &base)?.to_owned();
        }
        spec = spec.trim_start_matches("./").to_owned();
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
            path_index == path.len()
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
            left.eq_ignore_ascii_case(right)
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
    let includes: Vec<_> = options
        .include
        .iter()
        .filter_map(|spec| GlobPattern::compile(spec, &base, case_sensitive, false))
        .collect();
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
    visit(
        file_system,
        &base,
        &base,
        &includes,
        &excludes,
        &options.extensions,
        &mut buckets,
    )?;
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
    base: &str,
    directory: &str,
    includes: &[GlobPattern],
    excludes: &[GlobPattern],
    extensions: &[FileExtension],
    buckets: &mut [Vec<String>],
) -> io::Result<()> {
    let mut entries = file_system.read_directory(directory)?;
    entries.files.sort();
    entries.directories.sort();
    for file in entries.files {
        if !has_allowed_extension(&file, extensions) {
            continue;
        }
        let absolute = join(directory, &file);
        let relative = relative_to(&absolute, base).unwrap_or(&absolute);
        if excludes.iter().any(|pattern| pattern.matches(relative)) {
            continue;
        }
        let include_index = includes
            .iter()
            .position(|pattern| pattern.matches(relative));
        if let Some(index) = include_index {
            buckets[index].push(absolute);
        }
    }
    for child in entries.directories {
        let absolute = join(directory, &child);
        let relative = relative_to(&absolute, base).unwrap_or(&absolute);
        if excludes.iter().any(|pattern| pattern.matches(relative)) {
            continue;
        }
        visit(
            file_system,
            base,
            &absolute,
            includes,
            excludes,
            extensions,
            buckets,
        )?;
    }
    Ok(())
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
            && left.to_lowercase().collect::<String>() == right.to_lowercase().collect::<String>()
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
    if case_sensitive {
        path.to_owned()
    } else {
        path.to_ascii_lowercase()
    }
}

fn join(directory: &str, name: &str) -> String {
    resolve_path(directory, &[name])
}

fn relative_to<'a>(path: &'a str, base: &str) -> Option<&'a str> {
    if path == base {
        return Some("");
    }
    if base.ends_with('/') {
        path.strip_prefix(base)
    } else {
        path.strip_prefix(base)?.strip_prefix('/')
    }
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
    fn trailing_recursive_include_matches_nothing() {
        let fs = file_system(true, &["/dev/a.ts", "/dev/nested/b.ts"]);
        let mut options = DiscoveryOptions::new("/dev");
        options.include = vec!["**".into()];
        assert!(discover_files(&fs, &options).unwrap().is_empty());
    }
}
