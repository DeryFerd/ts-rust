//! Go: internal/bundled/bundled.go, embed.go (the `!noembed` build),
//! embed_generated.go and libs_generated.go.
//!
//! PORT: the pinned reference build embeds the libs and names them
//! `bundled:///libs/lib.*.d.ts` (see the oracle `*.files.txt` lists), so
//! embed.go is ported and noembed.go is not. The lib texts come from
//! `crates/ts_bundled/libs`, which is identical to the pinned
//! `internal/bundled/libs`.

use crate::prelude::*;
use std::sync::OnceLock;
use std::time::SystemTime;

// Go: bundled.go:19 Embedded
// Embedded is true if the bundled files are implemented through an embedded FS.
pub const EMBEDDED: bool = EMBEDDED_UNEXPORTED;

// Go: bundled.go:23 WrapFS
// WrapFS returns an FS which redirects embedded paths to the embedded file system.
// If the embedded file system is not available, it returns the original FS.
pub fn wrap_fs_exported(fs: Rc<dyn Fs>) -> Rc<dyn Fs> {
    wrap_fs(fs)
}

// Go: bundled.go:30 LibPath
// LibPath returns the path to the directory containing the bundled lib.d.ts files.
// If embedding is not enabled, this is a path on disk, and must be accessed through
// a real OS filesystem.
pub fn lib_path_exported() -> String {
    lib_path()
}

// PORT: bundled.go:34 bundledSourceDir, testingLibPath and TestingLibPath
// are for Go tests only and are not ported.

// Go: embed.go:13 embedded
// PORT: renamed; the Go names `Embedded` and `embedded` share a snake name.
const EMBEDDED_UNEXPORTED: bool = true;

// Go: embed.go:15 scheme
const SCHEME: &str = "bundled:///";

// Go: embed.go:17 splitPath
fn split_path(path: &str) -> Option<&str> {
    path.strip_prefix(SCHEME)
}

// Go: embed.go:21 libPath
pub fn lib_path() -> String {
    format!("{SCHEME}libs")
}

// Go: embed.go:25 IsBundled
pub fn is_bundled(path: &str) -> bool {
    split_path(path).is_some()
}

// wrappedFS is implemented directly rather than going through [io/fs.FS].
// Our vfs.FS works with file contents in terms of strings, and that's
// what go:embed does under the hood, but going through fs.FS will cause
// copying to []byte and back.

// Go: embed.go:35 wrappedFS
struct WrappedFs {
    fs: Rc<dyn Fs>,
}

// Go: embed.go:41 wrapFS
pub fn wrap_fs(fs: Rc<dyn Fs>) -> Rc<dyn Fs> {
    Rc::new(WrappedFs { fs })
}

impl Fs for WrappedFs {
    // Go: embed.go:45 UseCaseSensitiveFileNames
    fn use_case_sensitive_file_names(&self) -> bool {
        self.fs.use_case_sensitive_file_names()
    }

    // Go: embed.go:49 FileExists
    fn file_exists(&self, path: &str) -> bool {
        if let Some(rest) = split_path(path) {
            return embedded_contents(rest).is_some();
        }
        self.fs.file_exists(path)
    }

    // Go: embed.go:57 ReadFile
    // PORT: Go returns the embedded string without a copy. The `Fs` trait
    // returns an owned String, so the text is copied.
    fn read_file(&self, path: &str) -> (String, bool) {
        if let Some(rest) = split_path(path) {
            return match embedded_contents(rest) {
                Some(contents) => (contents.to_string(), true),
                None => (String::new(), false),
            };
        }
        self.fs.read_file(path)
    }

    // Go: embed.go:65 DirectoryExists
    fn directory_exists(&self, path: &str) -> bool {
        if let Some(rest) = split_path(path) {
            return rest == "libs";
        }
        self.fs.directory_exists(path)
    }

    // Go: embed.go:72 GetAccessibleEntries
    // PORT: Go leaves `Symlinks` nil here; that is `None`.
    fn get_accessible_entries(&self, path: &str) -> Entries {
        let mut result = Entries::default();
        if let Some(rest) = split_path(path) {
            if rest.is_empty() {
                result.directories = vec!["libs".to_string()];
            } else if rest == "libs" {
                result.files = LIB_NAMES.iter().map(|name| name.to_string()).collect();
            }
            return result;
        }
        self.fs.get_accessible_entries(path)
    }

    // Go: embed.go:88 Stat
    fn stat(&self, path: &str) -> Option<FileInfo> {
        if let Some(rest) = split_path(path) {
            if rest.is_empty() || rest == "libs" {
                return Some(new_file_info(rest, FileMode::DIR, 0));
            }
            if let Some(lib) = embedded_contents(rest) {
                let lib_name = rest.strip_prefix("libs/").unwrap_or(rest);
                return Some(new_file_info(lib_name, FileMode(0), lib.len() as i64));
            }
            return None;
        }
        self.fs.stat(path)
    }

    // Go: embed.go:102 WalkDir
    fn walk_dir(&self, root: &str, walk_fn: &mut WalkDirFunc<'_>) -> Result<(), FsError> {
        if let Some(rest) = split_path(root) {
            if let Err(err) = self.walk_dir_inner(rest, walk_fn) {
                if err.is_skip_all() {
                    return Ok(());
                }
                return Err(err);
            }
            return Ok(());
        }
        self.fs.walk_dir(root, walk_fn)
    }

    // Go: embed.go:148 Realpath
    fn realpath(&self, path: &str) -> String {
        if split_path(path).is_some() {
            return path.to_string();
        }
        self.fs.realpath(path)
    }

    // Go: embed.go:155 WriteFile
    fn write_file(&self, path: &str, data: &str) -> Result<(), FsError> {
        if split_path(path).is_some() {
            panic!("cannot write to embedded file system");
        }
        self.fs.write_file(path, data)
    }

    // Go: embed.go:162 AppendFile
    fn append_file(&self, path: &str, data: &str) -> Result<(), FsError> {
        if split_path(path).is_some() {
            panic!("cannot write to embedded file system");
        }
        self.fs.append_file(path, data)
    }

    // Go: embed.go:169 Remove
    fn remove(&self, path: &str) -> Result<(), FsError> {
        if split_path(path).is_some() {
            panic!("cannot remove from embedded file system");
        }
        self.fs.remove(path)
    }

    // Go: embed.go:176 Chtimes
    fn chtimes(
        &self,
        path: &str,
        a_time: Option<SystemTime>,
        m_time: Option<SystemTime>,
    ) -> Result<(), FsError> {
        if split_path(path).is_some() {
            panic!("cannot change times on embedded file system");
        }
        self.fs.chtimes(path, a_time, m_time)
    }
}

impl WrappedFs {
    // Go: embed.go:115 walkDir
    // PORT: named `walk_dir_inner`; the Go names `WalkDir` and `walkDir`
    // share a snake name.
    fn walk_dir_inner(&self, rest: &str, walk_fn: &mut WalkDirFunc<'_>) -> Result<(), FsError> {
        let entries = match rest {
            "" => root_entries(),
            "libs" => libs_entries(),
            _ => return Ok(()),
        };

        for entry in &entries {
            let name = format!("{}/{}", rest, entry.name());

            if let Err(err) = walk_fn(&format!("{SCHEME}{name}"), Some(entry), None) {
                if err.is_skip_all() {
                    return Err(FsError::SkipAll);
                }
                if err.is_skip_dir() {
                    continue;
                }
                return Err(err);
            }
            if entry.is_dir() {
                self.walk_dir_inner(name.strip_prefix('/').unwrap_or(&name), walk_fn)?;
            }
        }

        Ok(())
    }
}

// Go: embed.go:84 rootEntries
// PORT: Go builds this slice once at package init; the port builds it per call.
fn root_entries() -> Vec<DirEntry> {
    vec![file_info_to_dir_entry(new_file_info("libs", FileMode::DIR, 0))]
}

// Go: embed.go:183 fileInfo
// PORT: the Go `fileInfo` type is the shared `FileInfo` value. Its
// `ModTime` is the Go zero time (`None`) and `Info()` returns itself
// (`DirEntryInfo::Known`).
fn new_file_info(name: &str, mode: FileMode, size: i64) -> FileInfo {
    FileInfo {
        name: name.to_string(),
        size,
        mode,
        mod_time: None,
    }
}

// Go: embed_generated.go:343 libsEntries
// PORT: Go builds this slice at package init, in `LibNames` order.
fn libs_entries() -> Vec<DirEntry> {
    LIB_NAMES
        .iter()
        .map(|name| {
            let size = embedded_contents(&format!("libs/{name}")).map_or(0, |lib| lib.len() as i64);
            file_info_to_dir_entry(new_file_info(name, FileMode(0), size))
        })
        .collect()
}

// Go: embed_generated.go:232 embeddedContents
// PORT: the Go map is built once from `EMBEDDED_CONTENTS`.
fn embedded_contents(rest: &str) -> Option<&'static str> {
    static MAP: OnceLock<FxHashMap<&'static str, &'static str>> = OnceLock::new();
    MAP.get_or_init(|| EMBEDDED_CONTENTS.iter().copied().collect())
        .get(rest)
        .copied()
}

macro_rules! bundled_lib {
    ($name:literal) => {
        (
            concat!("libs/", $name),
            include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../ts_bundled/libs/", $name)),
        )
    };
}

// Go: embed_generated.go:13 (the go:embed variables)
static EMBEDDED_CONTENTS: &[(&str, &str)] = &[
    bundled_lib!("lib.d.ts"),
    bundled_lib!("lib.decorators.d.ts"),
    bundled_lib!("lib.decorators.legacy.d.ts"),
    bundled_lib!("lib.dom.asynciterable.d.ts"),
    bundled_lib!("lib.dom.d.ts"),
    bundled_lib!("lib.dom.iterable.d.ts"),
    bundled_lib!("lib.es2015.collection.d.ts"),
    bundled_lib!("lib.es2015.core.d.ts"),
    bundled_lib!("lib.es2015.d.ts"),
    bundled_lib!("lib.es2015.generator.d.ts"),
    bundled_lib!("lib.es2015.iterable.d.ts"),
    bundled_lib!("lib.es2015.promise.d.ts"),
    bundled_lib!("lib.es2015.proxy.d.ts"),
    bundled_lib!("lib.es2015.reflect.d.ts"),
    bundled_lib!("lib.es2015.symbol.d.ts"),
    bundled_lib!("lib.es2015.symbol.wellknown.d.ts"),
    bundled_lib!("lib.es2016.array.include.d.ts"),
    bundled_lib!("lib.es2016.d.ts"),
    bundled_lib!("lib.es2016.full.d.ts"),
    bundled_lib!("lib.es2016.intl.d.ts"),
    bundled_lib!("lib.es2017.arraybuffer.d.ts"),
    bundled_lib!("lib.es2017.d.ts"),
    bundled_lib!("lib.es2017.date.d.ts"),
    bundled_lib!("lib.es2017.full.d.ts"),
    bundled_lib!("lib.es2017.intl.d.ts"),
    bundled_lib!("lib.es2017.object.d.ts"),
    bundled_lib!("lib.es2017.sharedmemory.d.ts"),
    bundled_lib!("lib.es2017.string.d.ts"),
    bundled_lib!("lib.es2017.typedarrays.d.ts"),
    bundled_lib!("lib.es2018.asyncgenerator.d.ts"),
    bundled_lib!("lib.es2018.asynciterable.d.ts"),
    bundled_lib!("lib.es2018.d.ts"),
    bundled_lib!("lib.es2018.full.d.ts"),
    bundled_lib!("lib.es2018.intl.d.ts"),
    bundled_lib!("lib.es2018.promise.d.ts"),
    bundled_lib!("lib.es2018.regexp.d.ts"),
    bundled_lib!("lib.es2019.array.d.ts"),
    bundled_lib!("lib.es2019.d.ts"),
    bundled_lib!("lib.es2019.full.d.ts"),
    bundled_lib!("lib.es2019.intl.d.ts"),
    bundled_lib!("lib.es2019.object.d.ts"),
    bundled_lib!("lib.es2019.string.d.ts"),
    bundled_lib!("lib.es2019.symbol.d.ts"),
    bundled_lib!("lib.es2020.bigint.d.ts"),
    bundled_lib!("lib.es2020.d.ts"),
    bundled_lib!("lib.es2020.date.d.ts"),
    bundled_lib!("lib.es2020.full.d.ts"),
    bundled_lib!("lib.es2020.intl.d.ts"),
    bundled_lib!("lib.es2020.number.d.ts"),
    bundled_lib!("lib.es2020.promise.d.ts"),
    bundled_lib!("lib.es2020.sharedmemory.d.ts"),
    bundled_lib!("lib.es2020.string.d.ts"),
    bundled_lib!("lib.es2020.symbol.wellknown.d.ts"),
    bundled_lib!("lib.es2021.d.ts"),
    bundled_lib!("lib.es2021.full.d.ts"),
    bundled_lib!("lib.es2021.intl.d.ts"),
    bundled_lib!("lib.es2021.promise.d.ts"),
    bundled_lib!("lib.es2021.string.d.ts"),
    bundled_lib!("lib.es2021.weakref.d.ts"),
    bundled_lib!("lib.es2022.array.d.ts"),
    bundled_lib!("lib.es2022.d.ts"),
    bundled_lib!("lib.es2022.error.d.ts"),
    bundled_lib!("lib.es2022.full.d.ts"),
    bundled_lib!("lib.es2022.intl.d.ts"),
    bundled_lib!("lib.es2022.object.d.ts"),
    bundled_lib!("lib.es2022.regexp.d.ts"),
    bundled_lib!("lib.es2022.string.d.ts"),
    bundled_lib!("lib.es2023.array.d.ts"),
    bundled_lib!("lib.es2023.collection.d.ts"),
    bundled_lib!("lib.es2023.d.ts"),
    bundled_lib!("lib.es2023.full.d.ts"),
    bundled_lib!("lib.es2023.intl.d.ts"),
    bundled_lib!("lib.es2024.arraybuffer.d.ts"),
    bundled_lib!("lib.es2024.collection.d.ts"),
    bundled_lib!("lib.es2024.d.ts"),
    bundled_lib!("lib.es2024.full.d.ts"),
    bundled_lib!("lib.es2024.object.d.ts"),
    bundled_lib!("lib.es2024.promise.d.ts"),
    bundled_lib!("lib.es2024.regexp.d.ts"),
    bundled_lib!("lib.es2024.sharedmemory.d.ts"),
    bundled_lib!("lib.es2024.string.d.ts"),
    bundled_lib!("lib.es2025.collection.d.ts"),
    bundled_lib!("lib.es2025.d.ts"),
    bundled_lib!("lib.es2025.float16.d.ts"),
    bundled_lib!("lib.es2025.full.d.ts"),
    bundled_lib!("lib.es2025.intl.d.ts"),
    bundled_lib!("lib.es2025.iterator.d.ts"),
    bundled_lib!("lib.es2025.promise.d.ts"),
    bundled_lib!("lib.es2025.regexp.d.ts"),
    bundled_lib!("lib.es5.d.ts"),
    bundled_lib!("lib.es6.d.ts"),
    bundled_lib!("lib.esnext.array.d.ts"),
    bundled_lib!("lib.esnext.collection.d.ts"),
    bundled_lib!("lib.esnext.d.ts"),
    bundled_lib!("lib.esnext.date.d.ts"),
    bundled_lib!("lib.esnext.decorators.d.ts"),
    bundled_lib!("lib.esnext.disposable.d.ts"),
    bundled_lib!("lib.esnext.error.d.ts"),
    bundled_lib!("lib.esnext.full.d.ts"),
    bundled_lib!("lib.esnext.intl.d.ts"),
    bundled_lib!("lib.esnext.sharedmemory.d.ts"),
    bundled_lib!("lib.esnext.temporal.d.ts"),
    bundled_lib!("lib.esnext.typedarrays.d.ts"),
    bundled_lib!("lib.scripthost.d.ts"),
    bundled_lib!("lib.webworker.asynciterable.d.ts"),
    bundled_lib!("lib.webworker.d.ts"),
    bundled_lib!("lib.webworker.importscripts.d.ts"),
    bundled_lib!("lib.webworker.iterable.d.ts"),
];

// Go: libs_generated.go:7 LibNames
// LibNames is the list of all bundled lib files, sorted by name.
// For the list of libs sorted by load order, use [tsoptions.Libs].
pub static LIB_NAMES: &[&str] = &[
    "lib.d.ts",
    "lib.decorators.d.ts",
    "lib.decorators.legacy.d.ts",
    "lib.dom.asynciterable.d.ts",
    "lib.dom.d.ts",
    "lib.dom.iterable.d.ts",
    "lib.es2015.collection.d.ts",
    "lib.es2015.core.d.ts",
    "lib.es2015.d.ts",
    "lib.es2015.generator.d.ts",
    "lib.es2015.iterable.d.ts",
    "lib.es2015.promise.d.ts",
    "lib.es2015.proxy.d.ts",
    "lib.es2015.reflect.d.ts",
    "lib.es2015.symbol.d.ts",
    "lib.es2015.symbol.wellknown.d.ts",
    "lib.es2016.array.include.d.ts",
    "lib.es2016.d.ts",
    "lib.es2016.full.d.ts",
    "lib.es2016.intl.d.ts",
    "lib.es2017.arraybuffer.d.ts",
    "lib.es2017.d.ts",
    "lib.es2017.date.d.ts",
    "lib.es2017.full.d.ts",
    "lib.es2017.intl.d.ts",
    "lib.es2017.object.d.ts",
    "lib.es2017.sharedmemory.d.ts",
    "lib.es2017.string.d.ts",
    "lib.es2017.typedarrays.d.ts",
    "lib.es2018.asyncgenerator.d.ts",
    "lib.es2018.asynciterable.d.ts",
    "lib.es2018.d.ts",
    "lib.es2018.full.d.ts",
    "lib.es2018.intl.d.ts",
    "lib.es2018.promise.d.ts",
    "lib.es2018.regexp.d.ts",
    "lib.es2019.array.d.ts",
    "lib.es2019.d.ts",
    "lib.es2019.full.d.ts",
    "lib.es2019.intl.d.ts",
    "lib.es2019.object.d.ts",
    "lib.es2019.string.d.ts",
    "lib.es2019.symbol.d.ts",
    "lib.es2020.bigint.d.ts",
    "lib.es2020.d.ts",
    "lib.es2020.date.d.ts",
    "lib.es2020.full.d.ts",
    "lib.es2020.intl.d.ts",
    "lib.es2020.number.d.ts",
    "lib.es2020.promise.d.ts",
    "lib.es2020.sharedmemory.d.ts",
    "lib.es2020.string.d.ts",
    "lib.es2020.symbol.wellknown.d.ts",
    "lib.es2021.d.ts",
    "lib.es2021.full.d.ts",
    "lib.es2021.intl.d.ts",
    "lib.es2021.promise.d.ts",
    "lib.es2021.string.d.ts",
    "lib.es2021.weakref.d.ts",
    "lib.es2022.array.d.ts",
    "lib.es2022.d.ts",
    "lib.es2022.error.d.ts",
    "lib.es2022.full.d.ts",
    "lib.es2022.intl.d.ts",
    "lib.es2022.object.d.ts",
    "lib.es2022.regexp.d.ts",
    "lib.es2022.string.d.ts",
    "lib.es2023.array.d.ts",
    "lib.es2023.collection.d.ts",
    "lib.es2023.d.ts",
    "lib.es2023.full.d.ts",
    "lib.es2023.intl.d.ts",
    "lib.es2024.arraybuffer.d.ts",
    "lib.es2024.collection.d.ts",
    "lib.es2024.d.ts",
    "lib.es2024.full.d.ts",
    "lib.es2024.object.d.ts",
    "lib.es2024.promise.d.ts",
    "lib.es2024.regexp.d.ts",
    "lib.es2024.sharedmemory.d.ts",
    "lib.es2024.string.d.ts",
    "lib.es2025.collection.d.ts",
    "lib.es2025.d.ts",
    "lib.es2025.float16.d.ts",
    "lib.es2025.full.d.ts",
    "lib.es2025.intl.d.ts",
    "lib.es2025.iterator.d.ts",
    "lib.es2025.promise.d.ts",
    "lib.es2025.regexp.d.ts",
    "lib.es5.d.ts",
    "lib.es6.d.ts",
    "lib.esnext.array.d.ts",
    "lib.esnext.collection.d.ts",
    "lib.esnext.d.ts",
    "lib.esnext.date.d.ts",
    "lib.esnext.decorators.d.ts",
    "lib.esnext.disposable.d.ts",
    "lib.esnext.error.d.ts",
    "lib.esnext.full.d.ts",
    "lib.esnext.intl.d.ts",
    "lib.esnext.sharedmemory.d.ts",
    "lib.esnext.temporal.d.ts",
    "lib.esnext.typedarrays.d.ts",
    "lib.scripthost.d.ts",
    "lib.webworker.asynciterable.d.ts",
    "lib.webworker.d.ts",
    "lib.webworker.importscripts.d.ts",
    "lib.webworker.iterable.d.ts",
];
