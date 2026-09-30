//! Go: internal/bundled/embed.go and embed_generated.go (the `!noembed`
//! build, the default).
//!
//! PORT: the pinned reference build embeds the libs and names them
//! `bundled:///libs/lib.*.d.ts` (see the oracle `*.files.txt` lists). The
//! lib texts come from `crates/ts_goport/libs`, a copy of the pinned
//! `internal/bundled/libs` (see its PROVENANCE.md).

use super::{SNAPSHOT_TEXT_MIN, const_hash};
use crate::frontend::prelude::*;
use std::sync::OnceLock;
use std::time::SystemTime;

// Go: embed.go:13 embedded
// PORT: renamed; the Go names `Embedded` and `embedded` share a snake name.
pub(super) const EMBEDDED_UNEXPORTED: bool = true;

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

/// The embedded text of bundled path `path` (for example
/// `bundled:///libs/lib.dom.d.ts`), with no copy. `None` for other paths.
// PORT: Go's `ReadFile` returns this string directly; the `Fs` trait copies it.
#[must_use]
pub fn bundled_text(path: &str) -> Option<&'static str> {
    embedded_contents(split_path(path)?)
}

// Go: embed.go:25 IsBundled
pub fn is_bundled(path: &str) -> bool {
    split_path(path).is_some()
}

/// The `const_hash` of `text`, computed at compile time, when `text` is the
/// embedded text of a bundled lib of at least `SNAPSHOT_TEXT_MIN` bytes
/// (the same pointer and length, as `bundled_text` returns it). The lib
/// parse and bind snapshots check their keys with it.
///
/// PERF (rss2): the keys hashed the lib text at each load, and that read
/// brought every page of lib.dom (2.3 MB of the binary) into the RSS of a
/// program that uses it. With this hash a load reads no page of the text.
// PORT: not in Go.
#[must_use]
pub fn embedded_text_hash(text: &str) -> Option<u64> {
    EMBEDDED_CONTENTS
        .iter()
        .find(|&&(_, lib, hash)| hash != 0 && std::ptr::eq(lib, text))
        .map(|&(_, _, hash)| hash)
}

/// The base name of bundled lib path `path` (`bundled:///libs/lib.dom.d.ts`
/// gives `lib.dom.d.ts`). `None` for any other path. The lib parse and bind
/// snapshots find a lib file by this name.
// PORT: not in Go.
#[must_use]
pub fn bundled_lib_name(path: &str) -> Option<&str> {
    split_path(path)?.strip_prefix("libs/")
}

// wrappedFS is implemented directly rather than going through [io/fs.FS].
// Our vfs.FS works with file contents in terms of strings, and that's
// what go:embed does under the hood, but going through fs.FS will cause
// copying to []byte and back.

// Go: embed.go:35 wrappedFS
struct WrappedFs {
    fs: Rc<dyn Fs>,
}

thread_local! {
    /// `wrap_fs(osvfs_fs())` of this thread. The wrapper has no state, so
    /// one value per thread is the same as a new one per call.
    static WRAPPED_OS_FS: std::cell::OnceCell<Rc<dyn Fs>> = const { std::cell::OnceCell::new() };
}

// Go: embed.go:41 wrapFS
// PERF: the wrapper of the OS file system is one value per thread, so
// `is_wrapped_os_fs` can know it (see there).
pub fn wrap_fs(fs: Rc<dyn Fs>) -> Rc<dyn Fs> {
    if Rc::ptr_eq(&fs, &osvfs_fs()) {
        return WRAPPED_OS_FS.with(|os| os.get_or_init(|| Rc::new(WrappedFs { fs })).clone());
    }
    Rc::new(WrappedFs { fs })
}

/// True when `fs` is Go `sys.FS()` of this thread: `wrap_fs(osvfs_fs())`
/// with no OS override installed. Then every thread reads the same bytes
/// for a path (`bundled_text` for bundled paths, the OS file for others),
/// so the loader can use the text that a parse worker read.
// PORT: not in Go (the Go loader reads each file once, on its own task).
pub fn is_wrapped_os_fs(fs: &Rc<dyn Fs>) -> bool {
    !os_override_installed()
        && WRAPPED_OS_FS.with(|os| os.get().is_some_and(|os| Rc::ptr_eq(os, fs)))
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
    vec![file_info_to_dir_entry(new_file_info(
        "libs",
        FileMode::DIR,
        0,
    ))]
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
    MAP.get_or_init(|| {
        EMBEDDED_CONTENTS
            .iter()
            .map(|&(path, text, _)| (path, text))
            .collect()
    })
    .get(rest)
    .copied()
}

// PORT: one `EMBEDDED_CONTENTS` entry, from `crates/ts_goport/libs`: the
// path, the text and its compile-time `snapshot_text_hash`. The include path
// is relative to this file: this file builds in `goport_util`, whose
// manifest dir is not `crates/ts_goport`.
// `crates/ts_goport/scripts/copy-libs.sh` copies the same set for a noembed
// build.
macro_rules! bundled_lib {
    ($name:literal) => {{
        const TEXT: &str = include_str!(concat!("../../../libs/", $name));
        // One compile-time evaluation per lib, so each stays under the
        // rustc step limit.
        const HASH: u64 = snapshot_text_hash(TEXT);
        (concat!("libs/", $name), TEXT, HASH)
    }};
}

/// `const_hash` of `text` for a snapshot lib (`SNAPSHOT_TEXT_MIN`), else 0.
/// Only the three snapshot libs are hashed, so the compile-time evaluation
/// stays short (about 3 s for 3.4 MB).
const fn snapshot_text_hash(text: &str) -> u64 {
    if text.len() >= SNAPSHOT_TEXT_MIN {
        const_hash(text.as_bytes())
    } else {
        0
    }
}

// Go: embed_generated.go:13 (the go:embed variables)
static EMBEDDED_CONTENTS: &[(&str, &str, u64)] = &[
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

#[cfg(test)]
mod tests {
    use super::*;

    /// A snapshot lib has its compile-time hash only as the embedded text
    /// itself: a copy of the text, or a small lib, has none.
    #[test]
    fn embedded_text_hash_is_compile_time_hash() {
        let dom = bundled_text("bundled:///libs/lib.dom.d.ts").expect("lib.dom");
        assert!(dom.len() >= SNAPSHOT_TEXT_MIN);
        assert_eq!(embedded_text_hash(dom), Some(const_hash(dom.as_bytes())));
        assert_eq!(embedded_text_hash(&dom.to_string()), None);
        let small = bundled_text("bundled:///libs/lib.es2015.d.ts").expect("lib.es2015");
        assert_eq!(embedded_text_hash(small), None);
    }
}
