//! TypeScript-compatible, platform-independent path operations.
//!
//! Compiler paths always use `/`, even on Windows hosts. These functions work
//! on path strings and deliberately do not consult the host filesystem.

use std::fmt;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum FileExtension {
    Ts,
    Tsx,
    Dts,
    Js,
    Jsx,
    Json,
    TsBuildInfo,
    Mjs,
    Mts,
    Dmts,
    Cjs,
    Cts,
    Dcts,
}

impl FileExtension {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Ts => ".ts",
            Self::Tsx => ".tsx",
            Self::Dts => ".d.ts",
            Self::Js => ".js",
            Self::Jsx => ".jsx",
            Self::Json => ".json",
            Self::TsBuildInfo => ".tsbuildinfo",
            Self::Mjs => ".mjs",
            Self::Mts => ".mts",
            Self::Dmts => ".d.mts",
            Self::Cjs => ".cjs",
            Self::Cts => ".cts",
            Self::Dcts => ".d.cts",
        }
    }

    #[must_use]
    pub const fn is_typescript(self) -> bool {
        matches!(
            self,
            Self::Ts | Self::Tsx | Self::Dts | Self::Mts | Self::Dmts | Self::Cts | Self::Dcts
        )
    }

    #[must_use]
    pub const fn is_declaration(self) -> bool {
        matches!(self, Self::Dts | Self::Dmts | Self::Dcts)
    }
}

impl fmt::Display for FileExtension {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.as_str())
    }
}

pub const SUPPORTED_DECLARATION_EXTENSIONS: [FileExtension; 3] =
    [FileExtension::Dts, FileExtension::Dcts, FileExtension::Dmts];
pub const SUPPORTED_TS_IMPLEMENTATION_EXTENSIONS: [FileExtension; 4] = [
    FileExtension::Ts,
    FileExtension::Tsx,
    FileExtension::Mts,
    FileExtension::Cts,
];
pub const SUPPORTED_TS_EXTENSIONS: [FileExtension; 7] = [
    FileExtension::Ts,
    FileExtension::Tsx,
    FileExtension::Dts,
    FileExtension::Cts,
    FileExtension::Dcts,
    FileExtension::Mts,
    FileExtension::Dmts,
];

const EXTENSIONS_LONGEST_FIRST: [FileExtension; 13] = [
    FileExtension::TsBuildInfo,
    FileExtension::Dmts,
    FileExtension::Dcts,
    FileExtension::Dts,
    FileExtension::Json,
    FileExtension::Mjs,
    FileExtension::Mts,
    FileExtension::Cjs,
    FileExtension::Cts,
    FileExtension::Tsx,
    FileExtension::Jsx,
    FileExtension::Ts,
    FileExtension::Js,
];

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum ScriptKind {
    #[default]
    Unknown,
    Js,
    Jsx,
    Ts,
    Tsx,
    External,
    Json,
    Deferred,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum CaseSensitivity {
    Insensitive,
    #[default]
    Sensitive,
}

#[derive(Clone, Copy, Debug)]
struct Root {
    len: usize,
    is_url: bool,
}

#[must_use]
pub fn normalize_slashes(path: &str) -> String {
    path.replace('\\', "/")
}

fn root(path: &str) -> Root {
    let bytes = path.as_bytes();
    if bytes.is_empty() {
        return Root {
            len: 0,
            is_url: false,
        };
    }
    if matches!(bytes[0], b'/' | b'\\') {
        if bytes.len() == 1 || bytes.get(1) != Some(&bytes[0]) {
            return Root {
                len: 1,
                is_url: false,
            };
        }
        let len = path[2..]
            .find(char::from(bytes[0]))
            .map_or(bytes.len(), |index| index + 3);
        return Root { len, is_url: false };
    }
    if bytes[0].is_ascii_alphabetic() && bytes.get(1) == Some(&b':') {
        if bytes.len() == 2 {
            return Root {
                len: 2,
                is_url: false,
            };
        }
        if matches!(bytes.get(2), Some(b'/' | b'\\')) {
            return Root {
                len: 3,
                is_url: false,
            };
        }
    }
    if bytes.starts_with(b"^/") {
        return Root {
            len: 2,
            is_url: false,
        };
    }
    let Some(scheme_end) = path.find("://") else {
        return Root {
            len: 0,
            is_url: false,
        };
    };
    let authority_start = scheme_end + 3;
    let Some(authority_slash) = path[authority_start..].find('/') else {
        return Root {
            len: bytes.len(),
            is_url: true,
        };
    };
    let authority_end = authority_start + authority_slash;
    let mut len = authority_end + 1;
    let scheme = &path[..scheme_end];
    let authority = &path[authority_start..authority_end];
    if scheme == "file" && matches!(authority, "" | "localhost") {
        let volume = authority_end + 1;
        if bytes.get(volume).is_some_and(u8::is_ascii_alphabetic) {
            let separator_end = if bytes.get(volume + 1) == Some(&b':') {
                Some(volume + 2)
            } else if bytes.get(volume + 1) == Some(&b'%')
                && bytes.get(volume + 2) == Some(&b'3')
                && bytes
                    .get(volume + 3)
                    .is_some_and(|byte| matches!(byte, b'a' | b'A'))
            {
                Some(volume + 4)
            } else {
                None
            };
            if let Some(end) = separator_end {
                if end == bytes.len() {
                    len = end;
                } else if bytes.get(end) == Some(&b'/') {
                    len = end + 1;
                }
            }
        }
    }
    Root { len, is_url: true }
}

#[must_use]
pub fn root_length(path: &str) -> usize {
    root(path).len
}

#[must_use]
pub fn is_url(path: &str) -> bool {
    root(path).is_url
}

#[must_use]
pub fn is_rooted_disk_path(path: &str) -> bool {
    let value = root(path);
    value.len != 0 && !value.is_url
}

#[must_use]
pub fn is_absolute(path: &str) -> bool {
    root_length(path) != 0
}

#[must_use]
pub fn is_relative(path: &str) -> bool {
    matches!(path, "." | "..")
        || path
            .as_bytes()
            .strip_prefix(b".")
            .is_some_and(|rest| matches!(rest.first(), Some(b'/' | b'\\')))
        || path
            .as_bytes()
            .strip_prefix(b"..")
            .is_some_and(|rest| matches!(rest.first(), Some(b'/' | b'\\')))
}

#[must_use]
pub fn combine_paths(first: &str, paths: &[&str]) -> String {
    let mut result = normalize_slashes(first);
    for path in paths.iter().copied().filter(|path| !path.is_empty()) {
        let path = normalize_slashes(path);
        if result.is_empty() || root_length(&path) != 0 {
            result = path;
        } else {
            if !result.ends_with('/') {
                result.push('/');
            }
            result.push_str(&path);
        }
    }
    result
}

#[must_use]
pub fn normalize_path(path: &str) -> String {
    let path = normalize_slashes(path);
    let root_len = root_length(&path);
    let root = &path[..root_len];
    let trailing = path.ends_with('/');
    let mut components: Vec<&str> = Vec::new();
    for component in path[root_len..].split('/') {
        match component {
            "" | "." => {}
            ".." if components.last().is_some_and(|last| *last != "..") => {
                components.pop();
            }
            ".." if root_len != 0 => {}
            _ => components.push(component),
        }
    }
    let mut result = String::from(root);
    if !components.is_empty() {
        if !result.is_empty() && !result.ends_with('/') {
            result.push('/');
        }
        result.push_str(&components.join("/"));
    }
    if trailing && !result.is_empty() && !result.ends_with('/') {
        result.push('/');
    }
    result
}

#[must_use]
pub fn resolve_path(first: &str, paths: &[&str]) -> String {
    normalize_path(&combine_paths(first, paths))
}

/// Returns the path from `directory` to `target` using filesystem case rules.
/// Paths on different roots remain absolute.
#[must_use]
pub fn relative_path_from_directory(
    directory: &str,
    target: &str,
    case_sensitivity: CaseSensitivity,
) -> String {
    let directory = normalize_path(directory);
    let target = normalize_path(target);
    let directory_root = root_length(&directory);
    let target_root = root_length(&target);
    if !directory[..directory_root].eq_ignore_ascii_case(&target[..target_root]) {
        return path_from_components(
            &target[..target_root],
            &path_components(&target, target_root),
        );
    }

    let directory_components = path_components(&directory, directory_root);
    let target_components = path_components(&target, target_root);
    let common = directory_components
        .iter()
        .zip(&target_components)
        .take_while(|(left, right)| {
            canonical_file_name(left, case_sensitivity)
                == canonical_file_name(right, case_sensitivity)
        })
        .count();
    let mut parts = vec![".."; directory_components.len().saturating_sub(common)];
    parts.extend(target_components[common..].iter().copied());
    parts.join("/")
}

/// Returns a source-map path, converting an unrelated disk root into a file URL.
#[must_use]
pub fn relative_path_to_directory_or_url(
    directory: &str,
    target: &str,
    case_sensitivity: CaseSensitivity,
) -> String {
    let relative = relative_path_from_directory(directory, target, case_sensitivity);
    if !is_rooted_disk_path(&relative) {
        return relative;
    }
    if relative.starts_with('/') {
        format!("file://{relative}")
    } else {
        format!("file:///{relative}")
    }
}

fn path_components(path: &str, root_len: usize) -> Vec<&str> {
    path[root_len..]
        .split('/')
        .filter(|component| !component.is_empty())
        .collect()
}

fn path_from_components(root: &str, components: &[&str]) -> String {
    if root.is_empty() {
        return components.join("/");
    }
    let mut result = ensure_trailing_directory_separator(root);
    result.push_str(&components.join("/"));
    result
}

#[must_use]
pub fn canonicalize(
    path: &str,
    current_directory: &str,
    case_sensitivity: CaseSensitivity,
) -> String {
    let normalized = if is_rooted_disk_path(path) {
        normalize_path(path)
    } else {
        resolve_path(current_directory, &[path])
    };
    canonical_file_name(&normalized, case_sensitivity)
}

/// Applies TypeScript's case-insensitive file-name rules without changing the path.
#[must_use]
pub fn canonical_file_name(path: &str, case_sensitivity: CaseSensitivity) -> String {
    match case_sensitivity {
        CaseSensitivity::Sensitive => path.to_owned(),
        CaseSensitivity::Insensitive => path
            .chars()
            .flat_map(|ch| {
                if ch == '\u{0130}' {
                    ch.to_string().chars().collect::<Vec<_>>()
                } else {
                    ch.to_lowercase().collect()
                }
            })
            .collect(),
    }
}

#[must_use]
pub fn common_path_prefix(paths: &[&str], case_sensitivity: CaseSensitivity) -> Option<String> {
    let first = normalize_path(paths.first()?);
    let first_root = root_length(&first);
    let mut common: Vec<&str> = first[first_root..]
        .split('/')
        .filter(|part| !part.is_empty())
        .collect();
    let root_text = &first[..first_root];
    for path in &paths[1..] {
        let path = normalize_path(path);
        let path_root = root_length(&path);
        if !root_text.eq_ignore_ascii_case(&path[..path_root]) {
            return None;
        }
        let parts: Vec<&str> = path[path_root..]
            .split('/')
            .filter(|part| !part.is_empty())
            .collect();
        let shared = common
            .iter()
            .zip(parts)
            .take_while(|(left, right)| match case_sensitivity {
                CaseSensitivity::Sensitive => left == &right,
                CaseSensitivity::Insensitive => {
                    canonical_file_name(left, case_sensitivity)
                        == canonical_file_name(right, case_sensitivity)
                }
            })
            .count();
        common.truncate(shared);
    }
    let mut result = root_text.to_owned();
    if !common.is_empty() {
        if !result.is_empty() && !result.ends_with('/') {
            result.push('/');
        }
        result.push_str(&common.join("/"));
    }
    Some(result)
}

#[must_use]
pub fn directory_path(path: &str) -> String {
    let path = normalize_slashes(path);
    let root_len = root_length(&path);
    let end = path[root_len..]
        .trim_end_matches('/')
        .rfind('/')
        .map_or(root_len, |index| root_len + index);
    if end == 0 {
        String::new()
    } else {
        path[..end.max(root_len)].to_owned()
    }
}

#[must_use]
pub fn base_file_name(path: &str) -> &str {
    let root_len = root_length(path);
    if root_len == path.len() {
        return "";
    }
    let path = path
        .strip_suffix('/')
        .or_else(|| path.strip_suffix('\\'))
        .unwrap_or(path);
    let start = path
        .rfind(['/', '\\'])
        .map_or(root_len, |separator| (separator + 1).max(root_len));
    &path[start..]
}

#[must_use]
pub fn ensure_trailing_directory_separator(path: &str) -> String {
    let mut path = normalize_slashes(path);
    if !path.is_empty() && !path.ends_with('/') {
        path.push('/');
    }
    path
}

#[must_use]
pub fn remove_file_extension(path: &str) -> &str {
    if let Some(extension) = extension_from_path(path)
        && extension != FileExtension::TsBuildInfo
    {
        return &path[..path.len() - extension.as_str().len()];
    }
    path
}

#[must_use]
pub fn change_extension(path: &str, extension: &str) -> String {
    let without_extension = remove_file_extension(path);
    if without_extension.len() == path.len() {
        return path.to_owned();
    }
    format!("{without_extension}{extension}")
}

#[must_use]
pub fn declaration_emit_extension(path: &str) -> &'static str {
    match extension_from_path(path) {
        Some(FileExtension::Mts | FileExtension::Mjs | FileExtension::Dmts) => ".d.mts",
        Some(FileExtension::Cts | FileExtension::Cjs | FileExtension::Dcts) => ".d.cts",
        _ => ".d.ts",
    }
}

#[must_use]
pub fn extension_from_path(path: &str) -> Option<FileExtension> {
    EXTENSIONS_LONGEST_FIRST.into_iter().find(|extension| {
        path.len() > extension.as_str().len() && path.ends_with(extension.as_str())
    })
}

#[must_use]
pub fn has_typescript_extension(path: &str) -> bool {
    extension_from_path(path).is_some_and(FileExtension::is_typescript)
}

#[must_use]
pub fn is_declaration_file(path: &str) -> bool {
    extension_from_path(path).is_some_and(FileExtension::is_declaration)
        || path.rsplit(['/', '\\']).next().is_some_and(|base| {
            base.contains(".d.") && base.get(base.len().saturating_sub(3)..) == Some(".ts")
        })
}

#[must_use]
pub fn script_kind_from_path(path: &str) -> ScriptKind {
    if has_extension_ignore_case(path, ".jsx") {
        ScriptKind::Jsx
    } else if has_extension_ignore_case(path, ".tsx") {
        ScriptKind::Tsx
    } else if [".js", ".cjs", ".mjs"]
        .into_iter()
        .any(|extension| has_extension_ignore_case(path, extension))
    {
        ScriptKind::Js
    } else if [".ts", ".cts", ".mts"]
        .into_iter()
        .any(|extension| has_extension_ignore_case(path, extension))
    {
        ScriptKind::Ts
    } else if has_extension_ignore_case(path, ".json") {
        ScriptKind::Json
    } else {
        ScriptKind::Unknown
    }
}

fn has_extension_ignore_case(path: &str, extension: &str) -> bool {
    path.get(path.len().saturating_sub(extension.len())..)
        .is_some_and(|suffix| suffix.eq_ignore_ascii_case(extension))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalizes_slashes_and_relative_segments() {
        assert_eq!(normalize_slashes(r"\\server\path"), "//server/path");
        assert_eq!(normalize_path("/a/./b/../c/"), "/a/c/");
        assert_eq!(normalize_path("../../a"), "../../a");
        assert_eq!(normalize_path("/../../a"), "/a");
    }

    #[test]
    fn classifies_roots_like_upstream() {
        let cases = [
            ("a", 0, false, false),
            ("/path", 1, false, true),
            ("c:", 2, false, true),
            ("c:d", 0, false, false),
            ("c:/", 3, false, true),
            ("//server/share", 9, false, true),
            ("file:///path", 8, true, false),
            ("file:///c:/path", 11, true, false),
            ("http://server/path", 14, true, false),
        ];
        for (path, expected_root, expected_url, expected_disk) in cases {
            assert_eq!(root_length(path), expected_root, "{path}");
            assert_eq!(is_url(path), expected_url, "{path}");
            assert_eq!(is_rooted_disk_path(path), expected_disk, "{path}");
        }
    }

    #[test]
    fn combines_and_resolves_with_absolute_replacement() {
        assert_eq!(
            combine_paths("path", &["dir", "..", "file.ts"]),
            "path/dir/../file.ts"
        );
        assert_eq!(combine_paths("/path", &["/to", "file.ts"]), "/to/file.ts");
        assert_eq!(
            resolve_path("/path", &["dir", "..", "file.ts"]),
            "/path/file.ts"
        );
        assert_eq!(resolve_path("a", &["b", "/c"]), "/c");
    }

    #[test]
    fn canonicalizes_and_finds_common_prefix() {
        assert_eq!(
            canonicalize("../SRC/File.ts", "/work/pkg", CaseSensitivity::Insensitive),
            "/work/src/file.ts"
        );
        assert_eq!(
            common_path_prefix(&["/a/b/c", "/a/b/d"], CaseSensitivity::Sensitive),
            Some("/a/b".into())
        );
        assert_eq!(
            common_path_prefix(&["c:/a", "d:/a"], CaseSensitivity::Insensitive),
            None
        );
        assert_eq!(
            common_path_prefix(
                &["/src/CAF\u{00c9}/first.ts", "/src/caf\u{00e9}/second.ts",],
                CaseSensitivity::Insensitive,
            ),
            Some("/src/CAF\u{00c9}".into())
        );
        assert_eq!(
            canonical_file_name("/SRC/CAF\u{00c9}/\u{0130}.ts", CaseSensitivity::Insensitive),
            "/src/caf\u{00e9}/\u{0130}.ts"
        );
    }

    #[test]
    fn computes_relative_paths_with_root_and_case_identity() {
        assert_eq!(
            relative_path_from_directory(
                "/project/testfiles",
                "/project/testFiles/app.ts",
                CaseSensitivity::Insensitive,
            ),
            "app.ts"
        );
        assert_eq!(
            relative_path_from_directory(
                "/project/testfiles",
                "/project/testFiles/app.ts",
                CaseSensitivity::Sensitive,
            ),
            "../testFiles/app.ts"
        );
        assert_eq!(
            relative_path_from_directory("/a/b/c", "/a/b", CaseSensitivity::Sensitive),
            ".."
        );
        assert_eq!(
            relative_path_from_directory("/a/b", "/a/b", CaseSensitivity::Sensitive),
            ""
        );
        assert_eq!(
            relative_path_from_directory("C:/work", "D:/src/a.ts", CaseSensitivity::Sensitive),
            "D:/src/a.ts"
        );
        assert_eq!(
            relative_path_from_directory(
                "//server/share",
                "//other/share/a.ts",
                CaseSensitivity::Sensitive,
            ),
            "//other/share/a.ts"
        );
        assert_eq!(
            relative_path_from_directory(
                "file:///src/lib",
                "file:///src/main.ts",
                CaseSensitivity::Sensitive,
            ),
            "../main.ts"
        );
    }

    #[test]
    fn converts_unrelated_source_map_disk_roots_to_file_urls() {
        assert_eq!(
            relative_path_to_directory_or_url(
                "C:/build",
                "D:/src/main.ts",
                CaseSensitivity::Insensitive,
            ),
            "file:///D:/src/main.ts"
        );
        assert_eq!(
            relative_path_to_directory_or_url(
                "/build",
                "//server/share/main.ts",
                CaseSensitivity::Sensitive,
            ),
            "file:////server/share/main.ts"
        );
        assert_eq!(
            relative_path_to_directory_or_url(
                "/project/dist",
                "/project/src/main.ts",
                CaseSensitivity::Sensitive,
            ),
            "../src/main.ts"
        );
    }

    #[test]
    fn classifies_extensions_and_script_kinds() {
        assert_eq!(
            extension_from_path("index.d.mts"),
            Some(FileExtension::Dmts)
        );
        assert_eq!(extension_from_path("index.TS"), None);
        assert!(has_typescript_extension("index.cts"));
        assert!(is_declaration_file("types.d.css.ts"));
        assert_eq!(script_kind_from_path("component.TSX"), ScriptKind::Tsx);
        assert_eq!(script_kind_from_path("package.json"), ScriptKind::Json);
        assert_eq!(SUPPORTED_TS_EXTENSIONS.len(), 7);
    }

    #[test]
    fn derives_directory_base_and_emit_extensions() {
        assert_eq!(directory_path("/src/nested/file.ts"), "/src/nested");
        assert_eq!(directory_path("C:/file.ts"), "C:/");
        assert_eq!(directory_path("file.ts"), "");
        assert_eq!(base_file_name(r"C:\src\file.ts"), "file.ts");
        assert_eq!(base_file_name("/src/nested/"), "nested");
        assert_eq!(base_file_name("//server"), "");
        assert_eq!(base_file_name("file://server"), "");
        assert_eq!(base_file_name("file:///src/nested/"), "nested");
        assert_eq!(ensure_trailing_directory_separator("/src"), "/src/");
        assert_eq!(remove_file_extension("/src/file.d.mts"), "/src/file");
        assert_eq!(
            remove_file_extension("/src/file.custom"),
            "/src/file.custom"
        );
        assert_eq!(
            remove_file_extension("/src/build.tsbuildinfo"),
            "/src/build.tsbuildinfo"
        );
        assert_eq!(remove_file_extension("/src/.config"), "/src/.config");
        assert_eq!(change_extension("/src/file.ts", ".js"), "/src/file.js");
        assert_eq!(
            change_extension("/src/styles.css", ".js"),
            "/src/styles.css"
        );
        assert_eq!(change_extension("/src/file", ".js"), "/src/file");
        assert_eq!(declaration_emit_extension("entry.mts"), ".d.mts");
        assert_eq!(declaration_emit_extension("entry.cjs"), ".d.cts");
        assert_eq!(declaration_emit_extension("entry.tsx"), ".d.ts");
    }

    #[test]
    fn detects_only_explicit_relative_paths() {
        for path in [".", "..", "./a", "../a", r".\a", r"..\a"] {
            assert!(is_relative(path), "{path}");
        }
        for path in ["", "a", "a/b", "/a", "c:/a"] {
            assert!(!is_relative(path), "{path}");
        }
    }
}
