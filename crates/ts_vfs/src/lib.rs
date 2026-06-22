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
        return ("//", rest.trim_start_matches('/'), true);
    }
    if let Some(rest) = path.strip_prefix('/') {
        return ("/", rest.trim_start_matches('/'), true);
    }
    if path.as_bytes().get(1) == Some(&b':')
        && path.as_bytes().first().is_some_and(u8::is_ascii_alphabetic)
    {
        return (&path[..2], path[2..].trim_start_matches('/'), true);
    }
    ("", path, false)
}

fn join_normalized(root: &str, components: &[&str]) -> String {
    let joined = components.join("/");
    match (root, joined.is_empty()) {
        ("", _) => joined,
        ("/" | "//", true) => root.to_owned(),
        ("/" | "//", false) => format!("{root}{joined}"),
        (_, true) => format!("{root}/"),
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
        fs::read_to_string(normalize_path(path))
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

#[derive(Clone, Debug)]
struct MemoryFile {
    path: String,
    contents: String,
    modified_time: u128,
}

/// A deterministic, thread-safe file system for compiler tests.
#[derive(Debug)]
pub struct MemoryFileSystem {
    case_sensitive: bool,
    files: RwLock<BTreeMap<String, MemoryFile>>,
    clock: AtomicU64,
}

impl MemoryFileSystem {
    #[must_use]
    pub fn new(case_sensitive: bool) -> Self {
        Self {
            case_sensitive,
            files: RwLock::new(BTreeMap::new()),
            clock: AtomicU64::new(0),
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
            // TypeScript deliberately preserves non-ASCII path characters when
            // canonicalizing case-insensitive file names.
            normalized.to_ascii_lowercase()
        }
    }

    fn lock_error() -> io::Error {
        io::Error::other("memory file system lock is poisoned")
    }

    fn normalized_directory_exists(&self, directory: &str) -> bool {
        if directory.is_empty() || is_root(directory) {
            return true;
        }

        let canonical = self.canonical_path(directory);
        let prefix = format!("{canonical}/");
        self.files
            .read()
            .is_ok_and(|files| files.keys().any(|path| path.starts_with(&prefix)))
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
        let canonical = self.canonical_path(path);
        self.files
            .read()
            .is_ok_and(|files| files.contains_key(&canonical))
    }

    fn directory_exists(&self, path: &str) -> bool {
        self.normalized_directory_exists(&normalize_path(path))
    }

    fn modified_time(&self, path: &str) -> Option<u128> {
        let canonical = self.canonical_path(path);
        self.files
            .read()
            .ok()?
            .get(&canonical)
            .map(|file| file.modified_time)
    }

    fn read_file(&self, path: &str) -> io::Result<String> {
        let canonical = self.canonical_path(path);
        self.files
            .read()
            .map_err(|_| Self::lock_error())?
            .get(&canonical)
            .map(|file| file.contents.clone())
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, canonical))
    }

    fn write_file(&self, path: &str, contents: &str) -> io::Result<()> {
        let normalized = normalize_path(path);
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

        let canonical_directory = self.canonical_path(&normalized);
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

            // ASCII case folding preserves byte lengths, so the canonical
            // remainder identifies the corresponding suffix in the display
            // path even when the lookup used different casing.
            let display_remainder = &file.path[file.path.len() - remainder.len()..];
            if let Some((directory, _)) = display_remainder.split_once('/') {
                child_directories.insert(directory.to_owned());
            } else {
                child_files.insert(display_remainder.to_owned());
            }
        }

        Ok(DirectoryEntries {
            files: child_files.into_iter().collect(),
            directories: child_directories.into_iter().collect(),
        })
    }
}

fn is_root(path: &str) -> bool {
    path == "/" || path == "//" || path.ends_with(":/") && !path[..path.len() - 2].contains('/')
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

        fs::remove_dir_all(directory)
    }
}
