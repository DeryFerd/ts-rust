//! File-system abstractions used by the compiler.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io;
use std::sync::{
    RwLock,
    atomic::{AtomicU64, Ordering},
};
use std::time::UNIX_EPOCH;

/// The immediate children of a directory, sorted by name.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct DirectoryEntries {
    pub files: Vec<String>,
    pub directories: Vec<String>,
}

/// The compiler-facing subset of file-system operations.
pub trait FileSystem: Send + Sync {
    /// Whether differently-cased paths can identify different files.
    fn use_case_sensitive_file_names(&self) -> bool;

    fn file_exists(&self, path: &str) -> bool;

    fn directory_exists(&self, path: &str) -> bool;

    /// Resolves symbolic-link aliases when the file system can identify them.
    fn realpath(&self, path: &str) -> String {
        normalize_path(path)
    }

    /// Returns a monotonically comparable last-modified value for a file.
    fn modified_time(&self, path: &str) -> Option<u128>;

    /// Reads a UTF-8 text file.
    ///
    /// # Errors
    ///
    /// Returns an I/O error when the file cannot be read or is not UTF-8.
    fn read_file(&self, path: &str) -> io::Result<String>;

    /// Replaces or creates a UTF-8 text file.
    ///
    /// # Errors
    ///
    /// Returns an I/O error when the file cannot be created or replaced.
    fn write_file(&self, path: &str, contents: &str) -> io::Result<()>;

    /// Returns immediate file and directory names in deterministic order.
    ///
    /// # Errors
    ///
    /// Returns an I/O error when the directory cannot be read.
    fn read_directory(&self, path: &str) -> io::Result<DirectoryEntries>;
}

/// Normalizes a compiler path without consulting the host file system.
///
/// Both slash forms are accepted, repeated separators and `.` are removed,
/// and `..` is resolved without traversing above an absolute root. Trailing
/// separators are removed except for roots.
#[must_use]
pub fn normalize_path(path: &str) -> String {
    let slashed = path.replace('\\', "/");
    let (root, rest, absolute) = split_root(&slashed);
    let mut components: Vec<&str> = Vec::new();

    for component in rest.split('/') {
        match component {
            "" | "." => {}
            ".." if components.last().is_some_and(|last| *last != "..") => {
                components.pop();
            }
            ".." if absolute => {}
            _ => components.push(component),
        }
    }

    join_normalized(root, &components)
}

fn split_root(path: &str) -> (&str, &str, bool) {
    if let Some(rest) = path.strip_prefix("//") {
        let root_length = rest.find('/').map_or(path.len(), |separator| separator + 3);
        return (
            &path[..root_length],
            path[root_length..].trim_start_matches('/'),
            true,
        );
    }
    if let Some(rest) = path.strip_prefix('/') {
        return ("/", rest.trim_start_matches('/'), true);
    }
    if path.as_bytes().get(1) == Some(&b':')
        && path.as_bytes().first().is_some_and(u8::is_ascii_alphabetic)
    {
        return (&path[..2], path[2..].trim_start_matches('/'), true);
    }
    if let Some(rest) = path.strip_prefix("^/") {
        return ("^/", rest.trim_start_matches('/'), true);
    }
    if let Some(scheme_end) = path.find("://") {
        let authority_start = scheme_end + 3;
        let Some(authority_length) = path[authority_start..].find('/') else {
            return (path, "", true);
        };
        let authority_end = authority_start + authority_length;
        let mut root_length = authority_end + 1;
        let scheme = &path[..scheme_end];
        let authority = &path[authority_start..authority_end];
        if scheme == "file" && matches!(authority, "" | "localhost") {
            let bytes = path.as_bytes();
            let volume_start = authority_end + 1;
            if bytes.get(volume_start).is_some_and(u8::is_ascii_alphabetic) {
                let separator_end = if bytes.get(volume_start + 1) == Some(&b':') {
                    Some(volume_start + 2)
                } else if bytes.get(volume_start + 1) == Some(&b'%')
                    && bytes.get(volume_start + 2) == Some(&b'3')
                    && bytes
                        .get(volume_start + 3)
                        .is_some_and(|byte| matches!(byte, b'a' | b'A'))
                {
                    Some(volume_start + 4)
                } else {
                    None
                };
                if let Some(end) = separator_end {
                    if end == bytes.len() {
                        root_length = end;
                    } else if bytes.get(end) == Some(&b'/') {
                        root_length = end + 1;
                    }
                }
            }
        }
        return (
            &path[..root_length],
            path[root_length..].trim_start_matches('/'),
            true,
        );
    }
    ("", path, false)
}

fn join_normalized(root: &str, components: &[&str]) -> String {
    let joined = components.join("/");
    match (root, joined.is_empty()) {
        ("", _) => joined,
        (_, true) if root.len() == 2 && root.ends_with(':') => format!("{root}/"),
        (_, true) => root.to_owned(),
        (_, false) if root.ends_with('/') => format!("{root}{joined}"),
        (_, false) => format!("{root}/{joined}"),
    }
}

/// A file system backed by the process OS.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct OsFileSystem {
    case_sensitive: bool,
}

impl OsFileSystem {
    #[must_use]
    pub const fn new(case_sensitive: bool) -> Self {
        Self { case_sensitive }
    }
}

impl Default for OsFileSystem {
    fn default() -> Self {
        Self::new(!cfg!(windows))
    }
}

impl FileSystem for OsFileSystem {
    fn use_case_sensitive_file_names(&self) -> bool {
        self.case_sensitive
    }

    fn file_exists(&self, path: &str) -> bool {
        fs::metadata(normalize_path(path)).is_ok_and(|metadata| metadata.is_file())
    }

    fn directory_exists(&self, path: &str) -> bool {
        fs::metadata(normalize_path(path)).is_ok_and(|metadata| metadata.is_dir())
    }

    fn realpath(&self, path: &str) -> String {
        fs::canonicalize(normalize_path(path))
            .ok()
            .and_then(|path| path.to_str().map(normalize_path))
            .unwrap_or_else(|| normalize_path(path))
    }

    fn modified_time(&self, path: &str) -> Option<u128> {
        fs::metadata(normalize_path(path))
            .ok()?
            .modified()
            .ok()?
            .duration_since(UNIX_EPOCH)
            .ok()
            .map(|duration| duration.as_nanos())
    }

    fn read_file(&self, path: &str) -> io::Result<String> {
        let bytes = fs::read(normalize_path(path))?;
        if let Some(decoded) = decode_utf16_bom(&bytes) {
            return Ok(decoded);
        }
        let mut contents = String::from_utf8(bytes)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
        if contents.starts_with('\u{feff}') {
            contents.drain(..'\u{feff}'.len_utf8());
        }
        Ok(contents)
    }

    fn write_file(&self, path: &str, contents: &str) -> io::Result<()> {
        fs::write(normalize_path(path), contents)
    }

    fn read_directory(&self, path: &str) -> io::Result<DirectoryEntries> {
        let mut files = Vec::new();
        let mut directories = Vec::new();

        for entry in fs::read_dir(normalize_path(path))? {
            let entry = entry?;
            let name = entry.file_name().into_string().map_err(|_| {
                io::Error::new(io::ErrorKind::InvalidData, "directory entry is not UTF-8")
            })?;
            let metadata = entry.metadata()?;
            if metadata.is_dir() {
                directories.push(name);
            } else if metadata.is_file() {
                files.push(name);
            }
        }

        files.sort();
        directories.sort();
        Ok(DirectoryEntries { files, directories })
    }
}

/// Decodes UTF-16 text carrying a little- or big-endian byte-order mark.
#[must_use]
pub fn decode_utf16_bom(bytes: &[u8]) -> Option<String> {
    let (payload, little_endian) = match bytes {
        [0xff, 0xfe, payload @ ..] => (payload, true),
        [0xfe, 0xff, payload @ ..] => (payload, false),
        _ => return None,
    };
    let units = payload.chunks_exact(2).map(|chunk| {
        let pair = [chunk[0], chunk[1]];
        if little_endian {
            u16::from_le_bytes(pair)
        } else {
            u16::from_be_bytes(pair)
        }
    });
    Some(
        char::decode_utf16(units)
            .map(|unit| unit.unwrap_or('\u{fffd}'))
            .collect(),
    )
}

#[derive(Clone, Debug)]
struct MemoryFile {
    path: String,
    contents: String,
    modified_time: u128,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LinkKind {
    Directory,
    File,
}

#[derive(Clone, Debug)]
struct MemoryLink {
    alias: String,
    source: String,
    kind: LinkKind,
}

/// A deterministic, thread-safe file system for compiler tests.
#[derive(Debug)]
pub struct MemoryFileSystem {
    case_sensitive: bool,
    files: RwLock<BTreeMap<String, MemoryFile>>,
    links: RwLock<Vec<MemoryLink>>,
    clock: AtomicU64,
}

impl MemoryFileSystem {
    #[must_use]
    pub fn new(case_sensitive: bool) -> Self {
        Self {
            case_sensitive,
            files: RwLock::new(BTreeMap::new()),
            links: RwLock::new(Vec::new()),
            clock: AtomicU64::new(0),
        }
    }

    /// Registers a directory alias whose contents physically live at `source`.
    pub fn add_directory_link(&self, source: &str, alias: &str) {
        self.add_link(source, alias, LinkKind::Directory);
    }

    /// Registers a file alias that shares its contents and identity with `source`.
    pub fn add_file_link(&self, source: &str, alias: &str) {
        self.add_link(source, alias, LinkKind::File);
    }

    fn add_link(&self, source: &str, alias: &str, kind: LinkKind) {
        let source = normalize_path(source);
        let alias = normalize_path(alias);
        if let Ok(mut links) = self.links.write() {
            links.push(MemoryLink {
                alias,
                source,
                kind,
            });
            links.sort_by(|left, right| right.alias.len().cmp(&left.alias.len()));
        }
    }

    /// Returns all normalized file paths in deterministic order.
    ///
    /// # Errors
    ///
    /// Returns an error if another thread poisoned the internal lock.
    pub fn file_paths(&self) -> io::Result<Vec<String>> {
        let files = self
            .files
            .read()
            .map_err(|_| io::Error::other("memory file system lock is poisoned"))?;
        let mut paths: Vec<_> = files.values().map(|file| file.path.clone()).collect();
        paths.sort();
        Ok(paths)
    }

    fn canonical_path(&self, path: &str) -> String {
        let normalized = normalize_path(path);
        if self.case_sensitive {
            normalized
        } else {
            normalized
                .chars()
                .flat_map(|character| {
                    if character == '\u{0130}' {
                        character.to_string().chars().collect::<Vec<_>>()
                    } else {
                        character.to_lowercase().collect()
                    }
                })
                .collect()
        }
    }

    fn resolve_linked_path(&self, path: &str) -> String {
        let mut path = normalize_path(path);
        let Ok(links) = self.links.read() else {
            return path;
        };
        for _ in 0..links.len() {
            let canonical = self.canonical_path(&path);
            let Some(link) = links.iter().find(|link| {
                let canonical_alias = self.canonical_path(&link.alias);
                canonical == canonical_alias
                    || link.kind == LinkKind::Directory
                        && canonical
                            .strip_prefix(&canonical_alias)
                            .is_some_and(|rest| rest.starts_with('/'))
            }) else {
                break;
            };
            let canonical_alias = self.canonical_path(&link.alias);
            if canonical == canonical_alias {
                path.clone_from(&link.source);
            } else {
                let remainder = path_relative_to(&canonical, &canonical_alias)
                    .expect("matched directory alias has a relative suffix");
                let suffix = display_remainder(&path, remainder);
                path = format!("{}/{suffix}", link.source);
            }
        }
        path
    }

    fn canonical_lookup_path(&self, path: &str) -> String {
        self.canonical_path(&self.resolve_linked_path(path))
    }

    fn lock_error() -> io::Error {
        io::Error::other("memory file system lock is poisoned")
    }

    fn normalized_directory_exists(&self, directory: &str) -> bool {
        if directory.is_empty() || is_root(directory) {
            return true;
        }

        let canonical = self.canonical_lookup_path(directory);
        let prefix = format!("{canonical}/");
        if self
            .files
            .read()
            .is_ok_and(|files| files.keys().any(|path| path.starts_with(&prefix)))
        {
            return true;
        }

        let canonical_directory = self.canonical_path(directory);
        let alias_prefix = format!("{canonical_directory}/");
        self.links.read().is_ok_and(|links| {
            links.iter().any(|link| {
                self.canonical_path(&link.alias)
                    .strip_prefix(&alias_prefix)
                    .is_some_and(|remainder| !remainder.is_empty())
            })
        })
    }
}

impl Default for MemoryFileSystem {
    fn default() -> Self {
        Self::new(true)
    }
}

impl FileSystem for MemoryFileSystem {
    fn use_case_sensitive_file_names(&self) -> bool {
        self.case_sensitive
    }

    fn file_exists(&self, path: &str) -> bool {
        let canonical = self.canonical_lookup_path(path);
        self.files
            .read()
            .is_ok_and(|files| files.contains_key(&canonical))
    }

    fn directory_exists(&self, path: &str) -> bool {
        self.normalized_directory_exists(&normalize_path(path))
    }

    fn realpath(&self, path: &str) -> String {
        let resolved = self.resolve_linked_path(path);
        if self.case_sensitive {
            return resolved;
        }

        let canonical = self.canonical_path(&resolved);
        let Ok(files) = self.files.read() else {
            return resolved;
        };
        if let Some(file) = files.get(&canonical) {
            return file.path.clone();
        }

        for file in files.values() {
            let canonical_file = self.canonical_path(&file.path);
            let Some(remainder) = path_relative_to(&canonical_file, &canonical) else {
                continue;
            };
            if remainder.is_empty() {
                continue;
            }
            let display = display_remainder(&file.path, remainder);
            let directory = &file.path[..file.path.len() - display.len()];
            return normalize_path(directory);
        }

        resolved
    }

    fn modified_time(&self, path: &str) -> Option<u128> {
        let canonical = self.canonical_lookup_path(path);
        self.files
            .read()
            .ok()?
            .get(&canonical)
            .map(|file| file.modified_time)
    }

    fn read_file(&self, path: &str) -> io::Result<String> {
        let canonical = self.canonical_lookup_path(path);
        self.files
            .read()
            .map_err(|_| Self::lock_error())?
            .get(&canonical)
            .map(|file| {
                file.contents
                    .strip_prefix('\u{feff}')
                    .unwrap_or(&file.contents)
                    .to_owned()
            })
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, canonical))
    }

    fn write_file(&self, path: &str, contents: &str) -> io::Result<()> {
        let normalized = self.resolve_linked_path(path);
        if normalized.is_empty() || is_root(&normalized) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "file path must include a file name",
            ));
        }
        let canonical = self.canonical_path(&normalized);
        let modified_time = u128::from(self.clock.fetch_add(1, Ordering::Relaxed) + 1);
        let mut files = self.files.write().map_err(|_| Self::lock_error())?;
        match files.get_mut(&canonical) {
            Some(file) => {
                contents.clone_into(&mut file.contents);
                file.modified_time = modified_time;
            }
            None => {
                files.insert(
                    canonical,
                    MemoryFile {
                        path: normalized,
                        contents: contents.to_owned(),
                        modified_time,
                    },
                );
            }
        }
        Ok(())
    }

    fn read_directory(&self, path: &str) -> io::Result<DirectoryEntries> {
        let normalized = normalize_path(path);
        if !self.normalized_directory_exists(&normalized) {
            return Err(io::Error::new(io::ErrorKind::NotFound, normalized));
        }

        let canonical_directory = self.canonical_lookup_path(&normalized);
        let files = self.files.read().map_err(|_| Self::lock_error())?;
        let mut child_files = BTreeSet::new();
        let mut child_directories = BTreeSet::new();

        for file in files.values() {
            let canonical_file = self.canonical_path(&file.path);
            let Some(remainder) = path_relative_to(&canonical_file, &canonical_directory) else {
                continue;
            };
            if remainder.is_empty() {
                continue;
            }

            let display_remainder = display_remainder(&file.path, remainder);
            if let Some((directory, _)) = display_remainder.split_once('/') {
                child_directories.insert(directory.to_owned());
            } else {
                child_files.insert(display_remainder.to_owned());
            }
        }

        let canonical_requested_directory = self.canonical_path(&normalized);
        let links = self.links.read().map_err(|_| Self::lock_error())?;
        for link in links.iter() {
            let canonical_alias = self.canonical_path(&link.alias);
            let Some(remainder) =
                path_relative_to(&canonical_alias, &canonical_requested_directory)
            else {
                continue;
            };
            if remainder.is_empty() {
                continue;
            }
            let display = display_remainder(&link.alias, remainder);
            if let Some((child, _)) = display.split_once('/') {
                child_directories.insert(child.to_owned());
            } else if link.kind == LinkKind::File {
                child_files.insert(display.to_owned());
            } else {
                child_directories.insert(display.to_owned());
            }
        }

        Ok(DirectoryEntries {
            files: child_files.into_iter().collect(),
            directories: child_directories.into_iter().collect(),
        })
    }
}

fn is_root(path: &str) -> bool {
    let (root, remainder, absolute) = split_root(path);
    absolute && !root.is_empty() && remainder.is_empty()
}

fn path_relative_to<'a>(path: &'a str, directory: &str) -> Option<&'a str> {
    if directory.is_empty() {
        return (!path.starts_with('/') && path.as_bytes().get(1) != Some(&b':')).then_some(path);
    }
    if directory.ends_with('/') {
        return path.strip_prefix(directory);
    }
    path.strip_prefix(directory)?.strip_prefix('/')
}

fn display_remainder<'a>(path: &'a str, canonical_remainder: &str) -> &'a str {
    let component_count = canonical_remainder
        .bytes()
        .filter(|byte| *byte == b'/')
        .count()
        + 1;
    path.rmatch_indices('/')
        .nth(component_count - 1)
        .map_or(path, |(separator, _)| &path[separator + 1..])
}

#[cfg(test)]
mod tests {
    use super::{DirectoryEntries, FileSystem, MemoryFileSystem, OsFileSystem, normalize_path};
    use std::fs;
    use std::io;
    use std::sync::atomic::{AtomicU64, Ordering};

    #[test]
    fn normalizes_slashes_and_components() {
        assert_eq!(
            normalize_path(r"C:\src\.\compiler\..\index.ts"),
            "C:/src/index.ts"
        );
        assert_eq!(normalize_path("/src//compiler/../../index.ts"), "/index.ts");
        assert_eq!(normalize_path("../../src/../index.ts"), "../../index.ts");
        assert_eq!(normalize_path("/../../"), "/");
    }

    #[test]
    fn preserves_dynamic_network_and_url_roots() {
        assert_eq!(normalize_path("^/../../untitled.ts"), "^/untitled.ts");
        assert_eq!(
            normalize_path("//server/../../share/file.ts"),
            "//server/share/file.ts"
        );
        assert_eq!(normalize_path("file:///src/../main.ts"), "file:///main.ts");
        assert_eq!(
            normalize_path("file:///C:/src/../../main.ts"),
            "file:///C:/main.ts"
        );
        assert_eq!(
            normalize_path("https://example.test/src/../main.ts"),
            "https://example.test/main.ts"
        );
    }

    #[test]
    fn memory_file_system_uses_normalized_paths() -> io::Result<()> {
        let fs = MemoryFileSystem::new(true);
        fs.write_file(r"/src\compiler/./scanner.ts", "export {}")?;

        assert!(fs.file_exists("/src/compiler/scanner.ts"));
        assert!(fs.directory_exists("/src/compiler"));
        assert_eq!(
            fs.read_file("/src/tmp/../compiler/scanner.ts")?,
            "export {}"
        );
        assert_eq!(fs.file_paths()?, vec!["/src/compiler/scanner.ts"]);
        Ok(())
    }

    #[test]
    fn memory_file_system_strips_a_leading_utf8_byte_order_mark() -> io::Result<()> {
        let file_system = MemoryFileSystem::new(true);
        file_system.write_file("/project/source.ts", "\u{feff}const value = 1;")?;
        file_system.write_file("/project/embedded.ts", "const value = '\u{feff}';")?;

        assert_eq!(
            file_system.read_file("/project/source.ts")?,
            "const value = 1;"
        );
        assert_eq!(
            file_system.read_file("/project/embedded.ts")?,
            "const value = '\u{feff}';"
        );
        Ok(())
    }

    #[test]
    fn case_sensitivity_is_configurable() -> io::Result<()> {
        let sensitive = MemoryFileSystem::new(true);
        sensitive.write_file("/Src/Main.ts", "first")?;
        assert!(!sensitive.file_exists("/src/main.ts"));

        let insensitive = MemoryFileSystem::new(false);
        insensitive.write_file("/Src/Main.ts", "first")?;
        insensitive.write_file("/Src/Util/strings.ts", "")?;
        insensitive.write_file("/src/main.ts", "second")?;
        assert_eq!(insensitive.read_file("/SRC/MAIN.TS")?, "second");
        assert_eq!(
            insensitive.read_directory("/SRC")?,
            DirectoryEntries {
                files: vec!["Main.ts".into()],
                directories: vec!["Util".into()],
            }
        );
        assert_eq!(
            insensitive.file_paths()?,
            vec!["/Src/Main.ts", "/Src/Util/strings.ts"]
        );
        Ok(())
    }

    #[test]
    fn insensitive_paths_fold_unicode_without_collapsing_dotted_i() -> io::Result<()> {
        let file_system = MemoryFileSystem::new(false);
        file_system.write_file("/CAF\u{00c9}/\u{1e9e}OURCE.ts", "first")?;
        file_system.write_file("/caf\u{00e9}/\u{00df}ource.ts", "second")?;
        file_system.write_file("/caf\u{00e9}/\u{0130}.ts", "dotted")?;

        assert_eq!(
            file_system.read_file("/caf\u{00e9}/\u{00df}OURCE.TS")?,
            "second"
        );
        assert!(!file_system.file_exists("/caf\u{00e9}/i.ts"));
        assert_eq!(
            file_system.read_directory("/caf\u{00e9}")?.files,
            vec!["\u{0130}.ts", "\u{1e9e}OURCE.ts"]
        );
        Ok(())
    }

    #[test]
    fn resolves_directory_links_with_file_system_case_rules() -> io::Result<()> {
        let file_system = MemoryFileSystem::new(false);
        file_system.write_file("/packages/Caf\u{00e9}/entry.ts", "")?;
        file_system.add_directory_link("/packages/Caf\u{00e9}", "/Node_Modules/CAF\u{00c9}");

        assert_eq!(
            file_system.realpath("/node_modules/caf\u{00e9}/Entry.ts"),
            "/packages/Caf\u{00e9}/entry.ts"
        );
        Ok(())
    }

    #[test]
    fn case_insensitive_realpath_returns_stored_file_and_directory_casing() -> io::Result<()> {
        let file_system = MemoryFileSystem::new(false);
        file_system.write_file("/Source/Upper/Entry.ts", "")?;

        assert_eq!(
            file_system.realpath("/SOURCE/upper/ENTRY.TS"),
            "/Source/Upper/Entry.ts"
        );
        assert_eq!(file_system.realpath("/source/UPPER"), "/Source/Upper");
        assert_eq!(
            file_system.realpath("/source/Missing.ts"),
            "/source/Missing.ts"
        );
        Ok(())
    }

    #[test]
    fn directory_links_share_file_contents_and_directory_entries() -> io::Result<()> {
        let file_system = MemoryFileSystem::new(false);
        file_system.write_file("/packages/Shared/index.ts", "before")?;
        file_system.write_file("/packages/Shared/src/nested.ts", "nested")?;
        file_system.add_directory_link("/packages/Shared", "/app/node_modules/shared");

        assert!(file_system.directory_exists("/app/node_modules"));
        assert!(file_system.directory_exists("/APP/NODE_MODULES/SHARED"));
        assert!(file_system.file_exists("/app/node_modules/shared/INDEX.TS"));
        assert_eq!(
            file_system.read_file("/app/node_modules/shared/index.ts")?,
            "before"
        );
        assert_eq!(
            file_system.read_directory("/app/node_modules")?,
            DirectoryEntries {
                files: Vec::new(),
                directories: vec!["shared".into()],
            }
        );
        assert_eq!(
            file_system.read_directory("/app/node_modules/shared")?,
            DirectoryEntries {
                files: vec!["index.ts".into()],
                directories: vec!["src".into()],
            }
        );

        file_system.write_file("/app/node_modules/shared/index.ts", "after")?;
        assert_eq!(file_system.read_file("/packages/Shared/index.ts")?, "after");
        assert_eq!(
            file_system.modified_time("/packages/Shared/index.ts"),
            file_system.modified_time("/app/node_modules/shared/index.ts")
        );
        Ok(())
    }

    #[test]
    fn follows_chained_directory_links_for_all_file_operations() -> io::Result<()> {
        let file_system = MemoryFileSystem::new(true);
        file_system.write_file("/real/package/index.ts", "content")?;
        file_system.add_directory_link("/real/package", "/middle/package");
        file_system.add_directory_link("/middle/package", "/app/node_modules/package");

        assert!(file_system.directory_exists("/app/node_modules/package"));
        assert!(file_system.file_exists("/app/node_modules/package/index.ts"));
        assert_eq!(
            file_system.read_file("/app/node_modules/package/index.ts")?,
            "content"
        );
        file_system.write_file("/app/node_modules/package/new.ts", "new")?;
        assert_eq!(file_system.read_file("/real/package/new.ts")?, "new");
        Ok(())
    }

    #[test]
    fn file_links_share_identity_contents_and_directory_entries() -> io::Result<()> {
        let file_system = MemoryFileSystem::new(false);
        file_system.write_file("/packages/Shared/index.d.ts", "before")?;
        file_system.add_file_link(
            "/packages/Shared/index.d.ts",
            "/app/node_modules/shared/INDEX.d.ts",
        );

        assert!(file_system.directory_exists("/app/node_modules/shared"));
        assert!(file_system.file_exists("/APP/NODE_MODULES/SHARED/index.D.TS"));
        assert!(!file_system.directory_exists("/app/node_modules/shared/index.d.ts"));
        assert_eq!(
            file_system.realpath("/app/node_modules/shared/index.d.ts"),
            "/packages/Shared/index.d.ts"
        );
        assert_eq!(
            file_system.read_directory("/app/node_modules/shared")?,
            DirectoryEntries {
                files: vec!["INDEX.d.ts".into()],
                directories: Vec::new(),
            }
        );
        file_system.write_file("/app/node_modules/shared/index.d.ts", "after")?;
        assert_eq!(
            file_system.read_file("/packages/Shared/index.d.ts")?,
            "after"
        );
        assert_eq!(
            file_system.file_paths()?,
            vec!["/packages/Shared/index.d.ts"]
        );
        Ok(())
    }

    #[test]
    fn file_links_follow_linked_parent_directories() -> io::Result<()> {
        let file_system = MemoryFileSystem::new(true);
        file_system.write_file("/real/package/index.ts", "value")?;
        file_system.add_directory_link("/real/package", "/workspace/package");
        file_system.add_file_link(
            "/workspace/package/index.ts",
            "/app/node_modules/package/index.ts",
        );

        assert_eq!(
            file_system.realpath("/app/node_modules/package/index.ts"),
            "/real/package/index.ts"
        );
        assert_eq!(
            file_system.read_file("/app/node_modules/package/index.ts")?,
            "value"
        );
        Ok(())
    }

    #[test]
    fn drive_roots_can_be_enumerated() -> io::Result<()> {
        let fs = MemoryFileSystem::new(false);
        fs.write_file(r"C:\src\main.ts", "")?;

        assert!(fs.directory_exists("c:/"));
        assert_eq!(fs.read_directory("c:/")?.directories, vec!["src"]);
        assert_eq!(fs.read_directory("C:/src")?.files, vec!["main.ts"]);
        Ok(())
    }

    #[test]
    fn directory_entries_are_immediate_and_sorted() -> io::Result<()> {
        let fs = MemoryFileSystem::new(true);
        fs.write_file("/project/z.ts", "")?;
        fs.write_file("/project/a.ts", "")?;
        fs.write_file("/project/src/nested.ts", "")?;
        fs.write_file("/project/lib/types.d.ts", "")?;

        assert_eq!(
            fs.read_directory("/project")?,
            DirectoryEntries {
                files: vec!["a.ts".into(), "z.ts".into()],
                directories: vec!["lib".into(), "src".into()],
            }
        );
        assert_eq!(fs.read_directory("/project/src")?.files, vec!["nested.ts"]);
        assert_eq!(
            fs.read_directory("/missing").unwrap_err().kind(),
            io::ErrorKind::NotFound
        );
        Ok(())
    }

    #[test]
    fn os_file_system_round_trips_text() -> io::Result<()> {
        static NEXT_ID: AtomicU64 = AtomicU64::new(0);
        let directory = std::env::temp_dir().join(format!(
            "ts-vfs-{}-{}",
            std::process::id(),
            NEXT_ID.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&directory)?;
        let path = directory.join("source.ts");
        let path = path
            .to_str()
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "temp path is not UTF-8"))?;
        let vfs = OsFileSystem::default();

        vfs.write_file(path, "const value = 1;")?;
        assert!(vfs.file_exists(path));
        assert_eq!(vfs.read_file(path)?, "const value = 1;");
        assert_eq!(
            vfs.read_directory(directory.to_str().ok_or_else(|| io::Error::new(
                io::ErrorKind::InvalidData,
                "temp path is not UTF-8"
            ))?)?,
            DirectoryEntries {
                files: vec!["source.ts".into()],
                directories: Vec::new(),
            }
        );

        fs::write(path, b"\xef\xbb\xbfconst value = 2;")?;
        assert_eq!(vfs.read_file(path)?, "const value = 2;");

        fs::write(path, [0xff, 0xfe, b'o', 0, b'k', 0])?;
        assert_eq!(vfs.read_file(path)?, "ok");

        fs::remove_dir_all(directory)
    }
}
