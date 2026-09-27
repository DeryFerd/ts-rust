//! Go: internal/vfs/osvfs/os.go, realpath_linux.go, eintr_unix.go and
//! reparsepoint_other.go (Linux only).
//!
//! The Go standard library pieces that osvfs reaches (`os.DirFS`,
//! `os.RemoveAll`, `filepath.Abs`, `filepath.Clean`) are ported here too.

use crate::frontend::prelude::*;
use std::borrow::Cow;
use std::cell::OnceCell;
use std::ffi::{OsStr, OsString};
use std::io::{self, Write as _};
use std::os::fd::AsRawFd;
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::fs::{DirBuilderExt, FileTypeExt, OpenOptionsExt};
use std::path::{Path as OsPath, PathBuf};
use std::sync::{Arc, OnceLock};
use std::time::SystemTime;

// PORT: a Go path is a Go string, so it can hold any bytes, and Go passes
// those bytes to the OS unchanged. A port string is the port form of a Go
// string (see `scanner_util::GO_STRING_MARKER`). `os_path` gives the OS the
// Go bytes, and `go_string_from_os` turns OS bytes (file names, link
// targets, the working directory, arguments) into the port form. Every OS
// call in the port goes through them.

/// The OS path of the port form path `path`: its Go bytes.
pub fn os_path(path: &str) -> Cow<'_, OsPath> {
    match crate::scanner_util::go_string_bytes(path) {
        Cow::Borrowed(bytes) => Cow::Borrowed(OsPath::new(OsStr::from_bytes(bytes))),
        Cow::Owned(bytes) => Cow::Owned(PathBuf::from(OsString::from_vec(bytes))),
    }
}

/// The value form of the OS string `s` (see `os_path` and
/// `scanner_util::go_value_from_bytes`).
pub fn go_string_from_os(s: impl Into<OsString>) -> String {
    match String::from_utf8(s.into().into_vec()) {
        Ok(text) => crate::scanner_util::go_string_from_utf8(text),
        Err(err) => crate::scanner_util::go_value_from_bytes(err.as_bytes()).into_owned(),
    }
}

/// The process arguments after the program name, in the port form (Go
/// `os.Args[1:]`, see `os_path`).
pub fn os_args() -> Vec<String> {
    std::env::args_os().skip(1).map(go_string_from_os).collect()
}

/// The current directory in the port form (Go `os.Getwd`, see `os_path`).
/// With an OS override installed, the override's directory.
pub fn os_current_dir() -> io::Result<String> {
    if let Some(o) = OS_OVERRIDE.get() {
        return Ok(o.current_directory.clone());
    }
    std::env::current_dir().map(go_string_from_os)
}

// PORT: Go reads files and the current directory through `sys.FS()` and
// `sys.GetCurrentDirectory()`, so a Go test swaps the whole OS for its
// `TestSys`. The port's file system is `Rc`, so the parse, checker and emit
// threads cannot share `sys.FS()`: they call `osvfs_fs()` and
// `os_current_dir()` directly. A test process installs an `OsOverride` once
// at start, and those calls then reach the test file system and directory.
// Only test processes install it; a real run never does and keeps the OS
// behavior below unchanged.

/// The file system and current directory that replace the OS in a test
/// process (see `install_os_override`).
pub struct OsOverride {
    /// Makes the file system for one thread. `osvfs_fs` calls it once per
    /// thread. Each value must share one state (for example a map behind
    /// an `Arc<Mutex>`), so that all threads see the same files. It must
    /// not call `osvfs_fs` itself.
    pub fs: Arc<dyn Fn() -> Rc<dyn Fs> + Send + Sync>,
    /// The value of `os_current_dir`.
    pub current_directory: String,
}

static OS_OVERRIDE: OnceLock<OsOverride> = OnceLock::new();

/// Replaces the OS file system and current directory for the rest of the
/// process. Install it before the first `osvfs_fs` or `os_current_dir`
/// call. Panics when an override is already installed.
pub fn install_os_override(o: OsOverride) {
    assert!(
        OS_OVERRIDE.set(o).is_ok(),
        "osvfs: an OS override is already installed"
    );
}

/// True when `install_os_override` has run in this process.
pub fn os_override_installed() -> bool {
    OS_OVERRIDE.get().is_some()
}

// PORT: the Go semaphores `blockingOpSema`, `readSema` and `writeSema`
// (os.go:20) limit concurrent syscalls. The port is single-threaded, so they
// are not ported.

// Go: os.go:30 FS
// FS creates a new FS from the OS file system.
// PORT: the Go package function `osvfs.FS` is `osvfs_fs`. Go returns one
// package-level value; this returns a clone of one per-thread value. With
// an OS override installed (a test process), the per-thread value is the
// one that the override's `fs` makes on the first call on that thread.
pub fn osvfs_fs() -> Rc<dyn Fs> {
    thread_local! {
        // Go: os.go:34 osVFS
        static OS_VFS: Rc<dyn Fs> = Rc::new(OsFs {
            common: Common {
                root_for: os_dir_fs,
                is_reparse_point: IS_REPARSE_POINT,
            },
        });
        static OVERRIDE_FS: OnceCell<Rc<dyn Fs>> = const { OnceCell::new() };
    }
    if let Some(o) = OS_OVERRIDE.get() {
        return OVERRIDE_FS.with(|cell| Rc::clone(cell.get_or_init(|| (o.fs)())));
    }
    OS_VFS.with(Rc::clone)
}

// Go: reparsepoint_other.go:6 isReparsePoint
// Only Windows has reparse points; leave this nil for other OSes.
const IS_REPARSE_POINT: Option<fn(&str) -> bool> = None;

// Go: os.go:41 osFS
pub struct OsFs {
    common: Common,
}

// Go: os.go:46 isFileSystemCaseSensitive
// We do this right at startup to minimize the chance that executable gets moved or deleted.
// PORT: Go computes this in package init. The port computes it on first use.
// The Windows and wasm branches do not apply to the Linux port.
fn is_file_system_case_sensitive() -> bool {
    static VALUE: OnceLock<bool> = OnceLock::new();
    *VALUE.get_or_init(|| {
        // As a proxy for case-insensitivity, we check if the current executable exists under a different case.
        // This is not entirely correct, since different OSs can have differing case sensitivity in different paths,
        // but this is largely good enough for our purposes (and what sys.ts used to do with __filename).
        let exe = match std::env::current_exe() {
            Ok(exe) => go_string_from_os(exe),
            Err(err) => panic!("vfs: failed to get executable path: {err}"),
        };

        // If the current executable exists under a different case, we must be case-insensitive.
        let swapped = swap_case(&exe);
        if let Err(err) = std::fs::metadata(os_path(&swapped)) {
            if err.kind() == io::ErrorKind::NotFound {
                return true;
            }
            panic!("vfs: failed to stat {swapped:?}: {err}");
        }
        false
    })
}

// Go: os.go:77 swapCase
// Convert all lowercase chars to uppercase, and vice-versa
fn swap_case(str: &str) -> String {
    str.chars()
        .map(|r| {
            let upper = simple_to_upper(r);
            if upper == r {
                simple_to_lower(r)
            } else {
                upper
            }
        })
        .collect()
}

// PORT: Go `unicode.ToUpper` uses the simple one-rune case mapping. Rust
// only has the full mapping; a mapping to more than one char is treated as
// no simple mapping.
fn simple_to_upper(r: char) -> char {
    let mut it = r.to_uppercase();
    match (it.next(), it.next()) {
        (Some(c), None) => c,
        _ => r,
    }
}

// PORT: Go `unicode.ToLower`; see `simple_to_upper`.
fn simple_to_lower(r: char) -> char {
    let mut it = r.to_lowercase();
    match (it.next(), it.next()) {
        (Some(c), None) => c,
        _ => r,
    }
}

impl Fs for OsFs {
    // Go: os.go:88 UseCaseSensitiveFileNames
    fn use_case_sensitive_file_names(&self) -> bool {
        is_file_system_case_sensitive()
    }

    // Go: os.go:92 ReadFile
    fn read_file(&self, path: &str) -> (String, bool) {
        self.common.read_file(path)
    }

    // Go: os.go:97 DirectoryExists
    fn directory_exists(&self, path: &str) -> bool {
        self.common.directory_exists(path)
    }

    // Go: os.go:102 FileExists
    fn file_exists(&self, path: &str) -> bool {
        self.common.file_exists(path)
    }

    // Go: os.go:107 GetAccessibleEntries
    fn get_accessible_entries(&self, path: &str) -> Entries {
        self.common.get_accessible_entries(path)
    }

    // Go: os.go:112 Stat
    fn stat(&self, path: &str) -> Option<FileInfo> {
        self.common.stat(path)
    }

    // Go: os.go:146 WalkDir
    // PORT: Go wraps walkFn in a pooled `limitedWalkDirFunc` (os.go:117 to
    // 144) that only holds the blocking semaphore. The port passes walkFn
    // through.
    fn walk_dir(&self, root: &str, walk_fn: &mut WalkDirFunc<'_>) -> Result<(), FsError> {
        self.common.walk_dir(root, walk_fn)
    }

    // Go: os.go:152 Realpath
    fn realpath(&self, path: &str) -> String {
        os_fs_realpath(path)
    }

    // Go: os.go:205 WriteFile
    fn write_file(&self, path: &str, content: &str) -> Result<(), FsError> {
        self.write_file_ensuring_dir(path, content, WriteFlag::Truncate)
    }

    // Go: os.go:209 AppendFile
    fn append_file(&self, path: &str, content: &str) -> Result<(), FsError> {
        self.write_file_ensuring_dir(path, content, WriteFlag::Append)
    }

    // Go: os.go:213 Remove
    fn remove(&self, path: &str) -> Result<(), FsError> {
        // todo: #701 add retry mechanism?
        os_remove_all(path)
    }

    // Go: os.go:219 Chtimes
    // PORT: Go `os.Chtimes` calls utimensat on the path and leaves a zero
    // time unchanged. Rust std sets times through an open file, so the port
    // opens the path read-only first; a file without read permission fails
    // where Go succeeds. `None` leaves that time unchanged, as in Go.
    fn chtimes(
        &self,
        path: &str,
        a_time: Option<SystemTime>,
        m_time: Option<SystemTime>,
    ) -> Result<(), FsError> {
        let file = std::fs::File::open(os_path(path))
            .map_err(|err| FsError::path("chtimes", path, err))?;
        let mut times = std::fs::FileTimes::new();
        if let Some(a_time) = a_time {
            times = times.set_accessed(a_time);
        }
        if let Some(m_time) = m_time {
            times = times.set_modified(m_time);
        }
        file.set_times(times)
            .map_err(|err| FsError::path("chtimes", path, err))
    }
}

// PORT: the Go `flag int` of `writeFileWithFlag`. Go passes
// `O_WRONLY|O_CREATE|O_TRUNC` or `O_WRONLY|O_CREATE|O_APPEND`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum WriteFlag {
    Truncate,
    Append,
}

// Go: os.go:157 osFSRealpath
pub fn os_fs_realpath(path: &str) -> String {
    let _ = root_length(path); // Assert path is rooted

    let orig = path;
    // PORT: `filepath.FromSlash` is the identity on Linux.
    let path = match realpath(path) {
        Ok(path) => path,
        Err(_) => return orig.to_string(),
    };
    let path = match filepath_abs(&path) {
        Ok(path) => path,
        Err(_) => return orig.to_string(),
    };
    normalize_slashes(&path).into()
}

impl OsFs {
    // Go: os.go:173 writeFileWithFlag
    fn write_file_with_flag(
        &self,
        path: &str,
        content: &str,
        flag: WriteFlag,
    ) -> Result<(), FsError> {
        let mut options = std::fs::OpenOptions::new();
        options.write(true).create(true).mode(0o666);
        match flag {
            WriteFlag::Truncate => options.truncate(true),
            WriteFlag::Append => options.append(true),
        };
        let mut file = options
            .open(os_path(path))
            .map_err(|err| FsError::path("open", path, err))?;

        // PORT: Go writes the string bytes unchanged. `content` is the port
        // form of the Go string (see `scanner_util::GO_STRING_MARKER`), so
        // write its Go bytes.
        file.write_all(&crate::scanner_util::go_string_bytes(content))
            .map_err(|err| FsError::path("write", path, err))?;

        Ok(())
    }

    // Go: os.go:189 ensureDirectoryExists
    // PORT: Go `os.MkdirAll(directoryPath, 0o777)`.
    fn ensure_directory_exists(&self, directory_path: &str) -> Result<(), FsError> {
        std::fs::DirBuilder::new()
            .recursive(true)
            .mode(0o777)
            .create(os_path(directory_path))
            .map_err(|err| FsError::path("mkdir", directory_path, err))
    }

    // Go: os.go:194 writeFileEnsuringDir
    fn write_file_ensuring_dir(
        &self,
        path: &str,
        content: &str,
        flag: WriteFlag,
    ) -> Result<(), FsError> {
        let _ = root_length(path); // Assert path is rooted
        if self.write_file_with_flag(path, content, flag).is_ok() {
            return Ok(());
        }
        let normalized: String = normalize_path(path).into();
        let directory: String = get_directory_path(&normalized).into();
        self.ensure_directory_exists(&directory)?;
        self.write_file_with_flag(path, content, flag)
    }
}

// Go: os.go:224 GetGlobalTypingsCacheLocation
// PORT: not ported. Only the language server (cmd/tsgo/lsp.go) calls it.

// Go: realpath_linux.go:32 _procSelfFD
const PROC_SELF_FD: &str = "/proc/self/fd/";

// PORT: Linux `O_PATH` (0o10000000 on x86-64 and aarch64). The crate has no
// libc dependency, so the value is written here.
const O_PATH: i32 = 0o10000000;

// Go: realpath_linux.go:34 hasProcSelfFD
fn has_proc_self_fd() -> bool {
    static VALUE: OnceLock<bool> = OnceLock::new();
    *VALUE.get_or_init(|| std::fs::metadata(PROC_SELF_FD).is_ok())
}

// Go: realpath_linux.go:39 realpath
// On Linux, we use the O_PATH + /proc/self/fd trick to resolve the canonical
// path in O(1) syscalls (open + readlink + close) instead of Go's
// filepath.EvalSymlinks which does an lstat per path component — O(depth).
//
// Falls back to filepath.EvalSymlinks if /proc is not available (e.g. containers
// or chroots without procfs mounted).
fn realpath(path: &str) -> Result<String, FsError> {
    if !has_proc_self_fd() {
        // PORT: Go `filepath.EvalSymlinks`. For the rooted paths that reach
        // here, `std::fs::canonicalize` gives the same result.
        return std::fs::canonicalize(os_path(path))
            .map(go_string_from_os)
            .map_err(|err| FsError::path("lstat", path, err));
    }

    // PORT: Rust std always adds O_CLOEXEC. The file is closed when it drops
    // (Go `defer unix.Close(fd)`).
    let file = ignoring_eintr(|| {
        std::fs::OpenOptions::new()
            .read(true)
            .custom_flags(O_PATH)
            .open(os_path(path))
    })
    .map_err(|err| FsError::path("open", path, err))?;

    let proc_path = format!("{}{}", PROC_SELF_FD, file.as_raw_fd());

    // PORT: Go grows its readlink buffer until the target fits.
    // `std::fs::read_link` does the same internally.
    let target = ignoring_eintr(|| std::fs::read_link(&proc_path))
        .map_err(|err| FsError::path("readlink", path, err))?;
    Ok(go_string_from_os(target))
}

// Go: eintr_unix.go:7 ignoringEINTR
fn ignoring_eintr<T>(mut f: impl FnMut() -> io::Result<T>) -> io::Result<T> {
    loop {
        match f() {
            Err(err) if err.kind() == io::ErrorKind::Interrupted => continue,
            result => return result,
        }
    }
}

// Go: os/file.go DirFS
// PORT: Go standard library. `os.DirFS(dir)` with the `Stat`, `ReadDir`
// and `ReadFile` methods that `io/fs` helpers use.
pub fn os_dir_fs(dir: &str) -> Option<Box<dyn IoFs>> {
    Some(Box::new(DirFs {
        dir: dir.to_string(),
    }))
}

// Go: os/file.go dirFS
pub struct DirFs {
    dir: String,
}

impl DirFs {
    // Go: os/file.go dirFS.join
    // PORT: Go `filepathlite.Localize` on Unix is `fs.ValidPath` plus a
    // NUL byte check.
    fn join(&self, name: &str) -> Result<String, FsError> {
        if self.dir.is_empty() {
            return Err(FsError::Other("os: DirFS with empty root".to_string()));
        }
        if !io_fs_valid_path(name) || name.contains('\0') {
            return Err(FsError::Invalid);
        }
        if self.dir.ends_with('/') {
            return Ok(format!("{}{}", self.dir, name));
        }
        Ok(format!("{}/{}", self.dir, name))
    }
}

impl IoFs for DirFs {
    // Go: os/file.go dirFS.Stat
    fn stat(&self, name: &str) -> Result<FileInfo, FsError> {
        let fullname = self.join(name)?;
        // Go os.Stat follows symlinks.
        match std::fs::metadata(os_path(&fullname)) {
            Ok(md) => Ok(file_info_from_metadata(basename(&fullname), &md)),
            Err(err) => Err(FsError::path("stat", name, err)),
        }
    }

    // Go: os/file.go dirFS.ReadDir
    fn read_dir(&self, name: &str) -> Result<Vec<DirEntry>, FsError> {
        let fullname = self.join(name)?;
        os_read_dir(&fullname).map_err(|err| FsError::path("readdirent", name, err))
    }

    // Go: os/file.go dirFS.ReadFile
    fn read_file(&self, name: &str) -> Result<Vec<u8>, FsError> {
        let fullname = self.join(name)?;
        std::fs::read(os_path(&fullname)).map_err(|err| FsError::path("open", name, err))
    }
}

// Go: os/dir.go ReadDir
// PORT: Go standard library. Returns the entries sorted by file name. The
// entry type comes from the directory entry (d_type) and does not follow
// symlinks. Go skips an entry that is removed before its `lstat`; so does
// the port. Go returns the entries read before an error; the port returns
// only the error (callers here drop the entries on error).
fn os_read_dir(dirname: &str) -> io::Result<Vec<DirEntry>> {
    let mut entries = Vec::new();
    for entry in std::fs::read_dir(os_path(dirname))? {
        let entry = entry?;
        let file_type = match entry.file_type() {
            Ok(file_type) => file_type,
            Err(err) if err.kind() == io::ErrorKind::NotFound => continue,
            Err(err) => return Err(err),
        };
        let typ = if file_type.is_dir() {
            FileMode::DIR
        } else if file_type.is_symlink() {
            FileMode::SYMLINK
        } else if file_type.is_file() {
            FileMode(0)
        } else if file_type.is_block_device() {
            FileMode::DEVICE
        } else if file_type.is_char_device() {
            FileMode::DEVICE | FileMode::CHAR_DEVICE
        } else if file_type.is_fifo() {
            FileMode::NAMED_PIPE
        } else if file_type.is_socket() {
            FileMode::SOCKET
        } else {
            FileMode::IRREGULAR
        };
        let name = go_string_from_os(entry.file_name());
        let full_path = format!("{}/{}", dirname, name);
        entries.push(DirEntry {
            name,
            typ,
            info: DirEntryInfo::Lstat(full_path),
        });
    }
    // Go sorts by the name bytes.
    entries.sort_by(|a, b| {
        crate::scanner_util::go_string_bytes(&a.name)
            .cmp(&crate::scanner_util::go_string_bytes(&b.name))
    });
    Ok(entries)
}

// Go: os/removeall_at.go RemoveAll
// PORT: Go standard library. Removes path and any children. A missing
// path is not an error. Rust `remove_dir_all` does not follow symlinks,
// like Go.
fn os_remove_all(path: &str) -> Result<(), FsError> {
    if path.is_empty() {
        // fail silently to retain compatibility with previous behavior
        // of RemoveAll. See issue 28830.
        return Ok(());
    }

    // The rmdir system call does not permit removing ".",
    // so we don't permit it either.
    if ends_with_dot(path) {
        return Err(FsError::path(
            "RemoveAll",
            path,
            io::Error::from(io::ErrorKind::InvalidInput),
        ));
    }

    let os = os_path(path);
    let result = match std::fs::symlink_metadata(&os) {
        Err(err) => Err(err),
        Ok(md) if md.is_dir() => std::fs::remove_dir_all(&os),
        Ok(_) => std::fs::remove_file(&os),
    };
    match result {
        Err(err) if err.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(err) => Err(FsError::path("unlinkat", path, err)),
        Ok(()) => Ok(()),
    }
}

// Go: os/path.go endsWithDot
fn ends_with_dot(path: &str) -> bool {
    if path == "." {
        return true;
    }
    let b = path.as_bytes();
    b.len() >= 2 && b[b.len() - 1] == b'.' && b[b.len() - 2] == b'/'
}

// Go: path/filepath/path.go Abs (unix)
// PORT: Go standard library.
fn filepath_abs(path: &str) -> Result<String, FsError> {
    if path.starts_with('/') {
        return Ok(filepath_clean(path));
    }
    let wd = os_current_dir().map_err(|err| FsError::path("getwd", path, err))?;
    // Go: filepath.Join(wd, path)
    if path.is_empty() {
        return Ok(filepath_clean(&wd));
    }
    Ok(filepath_clean(&format!("{wd}/{path}")))
}

// Go: path/filepath/path.go Clean (unix)
// PORT: Go standard library. Lexical cleanup only.
pub fn filepath_clean(path: &str) -> String {
    if path.is_empty() {
        return ".".to_string();
    }
    let p = path.as_bytes();
    let rooted = p[0] == b'/';
    let n = p.len();

    // Invariants:
    //	reading from path; r is index of next byte to process.
    //	writing to out; w is index of next byte to write.
    //	dotdot is index in out where .. must stop, either because
    //		it is the leading slash or it is a leading ../../.. prefix.
    let mut out: Vec<u8> = Vec::with_capacity(n);
    let (mut r, mut dotdot) = (0usize, 0usize);
    if rooted {
        out.push(b'/');
        r = 1;
        dotdot = 1;
    }

    while r < n {
        if p[r] == b'/' {
            // empty path element
            r += 1;
        } else if p[r] == b'.' && (r + 1 == n || p[r + 1] == b'/') {
            // . element
            r += 1;
        } else if p[r] == b'.' && p[r + 1] == b'.' && (r + 2 == n || p[r + 2] == b'/') {
            // .. element: remove to last /
            r += 2;
            if out.len() > dotdot {
                // can backtrack
                let mut w = out.len() - 1;
                while w > dotdot && out[w] != b'/' {
                    w -= 1;
                }
                out.truncate(w);
            } else if !rooted {
                // cannot backtrack, but not rooted, so append .. element.
                if !out.is_empty() {
                    out.push(b'/');
                }
                out.extend_from_slice(b"..");
                dotdot = out.len();
            }
        } else {
            // real path element.
            // add slash if needed
            if (rooted && out.len() != 1) || (!rooted && !out.is_empty()) {
                out.push(b'/');
            }
            // copy element
            while r < n && p[r] != b'/' {
                out.push(p[r]);
                r += 1;
            }
        }
    }

    // Turn empty string into "."
    if out.is_empty() {
        return ".".to_string();
    }
    // The input is valid UTF-8 and the cuts are at ASCII '/' bytes.
    String::from_utf8(out)
        .unwrap_or_else(|err| String::from_utf8_lossy(err.as_bytes()).into_owned())
}
