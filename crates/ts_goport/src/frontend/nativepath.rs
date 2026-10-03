//! Go: internal/nativepath: realpath_linux.go, realpath_other.go,
//! realpath_windows.go, eintr_unix.go, symlink_other.go and
//! symlink_windows.go.
//!
//! OS path helpers that osvfs and fswatch share. Paths are OS paths in the
//! port form (see `vfs::osvfs::os_path`).

use crate::frontend::vfs::FsError;
use crate::frontend::vfs::osvfs::{go_string_from_os, os_path};
use std::io;
#[cfg(target_os = "linux")]
use std::os::fd::AsRawFd;
#[cfg(target_os = "linux")]
use std::os::unix::fs::OpenOptionsExt;
use std::sync::OnceLock;

// Go: realpath_linux.go:32 _procSelfFD
const PROC_SELF_FD: &str = "/proc/self/fd/";

// PORT: Linux `O_PATH`, the value of the target (rustix).
#[cfg(target_os = "linux")]
const O_PATH: i32 = rustix::fs::OFlags::PATH.bits() as i32;

// Go: realpath_linux.go:34 hasProcSelfFD
fn has_proc_self_fd() -> bool {
    static VALUE: OnceLock<bool> = OnceLock::new();
    *VALUE.get_or_init(|| std::fs::metadata(PROC_SELF_FD).is_ok())
}

// Go: realpath_linux.go:39 Realpath
// On Linux, we use the O_PATH + /proc/self/fd trick to resolve the canonical
// path in O(1) syscalls (open + readlink + close) instead of Go's
// filepath.EvalSymlinks which does an lstat per path component — O(depth).
//
// Falls back to filepath.EvalSymlinks if /proc is not available (e.g. containers
// or chroots without procfs mounted).
#[cfg(target_os = "linux")]
pub fn realpath(path: &str) -> Result<String, FsError> {
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

// Go: realpath_other.go:7 Realpath
// PORT: every target but Linux and Windows. The port uses
// `std::fs::canonicalize` (Go `filepath.EvalSymlinks`, as in the Linux
// fallback above).
#[cfg(not(any(target_os = "linux", windows)))]
pub fn realpath(path: &str) -> Result<String, FsError> {
    std::fs::canonicalize(os_path(path))
        .map(go_string_from_os)
        .map_err(|err| FsError::path("lstat", path, err))
}

// Go: realpath_windows.go:13 Realpath
// This implementation is based on what Node's fs.realpath.native does, via libuv: https://github.com/libuv/libuv/blob/ec5a4b54f7da7eeb01679005c615fee9633cdb3b/src/win/fs.c#L2937
// PORT: `std::fs::canonicalize` makes Go's calls: CreateFileW with no access,
// all share modes, OPEN_EXISTING and FILE_FLAG_BACKUP_SEMANTICS (Go
// `openMetadata`), then GetFinalPathNameByHandleW with VOLUME_NAME_DOS. It
// handles long paths itself (Go uses `os.Open` for them). The prefix
// handling below is Go's.
#[cfg(windows)]
pub fn realpath(path: &str) -> Result<String, FsError> {
    let s = std::fs::canonicalize(os_path(path))
        .map(go_string_from_os)
        .map_err(|err| FsError::path("CreateFile", path, err))?;
    if s.len() > 4 && s.starts_with(r"\\?\") {
        let s = &s[4..];
        if s.len() > 3 && s.starts_with("UNC") {
            // return path like \\server\share\...
            return Ok(format!(r"\{}", &s[3..]));
        }
        return Ok(s.to_string());
    }
    Err(FsError::Other(format!(
        "GetFinalPathNameByHandle returned unexpected path: {s}"
    )))
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

// Go: symlink_windows.go:8 IsSymlinkOrReparsePoint
/// Reports whether `path` has FILE_ATTRIBUTE_REPARSE_POINT (a symlink, a
/// junction or another reparse point).
///
/// PORT: Go GetFileAttributesEx (with `\\?\` for a long path) does not
/// follow the reparse point; `std::fs::symlink_metadata` does not either and
/// handles long paths itself.
#[cfg(windows)]
pub fn is_symlink_or_reparse_point(path: &str) -> bool {
    use std::os::windows::fs::MetadataExt;
    const FILE_ATTRIBUTE_REPARSE_POINT: u32 = 0x400;
    std::fs::symlink_metadata(os_path(path))
        .is_ok_and(|info| info.file_attributes() & FILE_ATTRIBUTE_REPARSE_POINT != 0)
}

// Go: symlink_other.go:7 IsSymlinkOrReparsePoint
/// Reports whether `path` itself is a symlink. Go `os.Lstat` does not follow
/// the last link, and a path that cannot be read (missing, empty, holds a NUL
/// byte) is not a symlink.
#[cfg(not(windows))]
pub fn is_symlink_or_reparse_point(path: &str) -> bool {
    std::fs::symlink_metadata(os_path(path)).is_ok_and(|info| info.file_type().is_symlink())
}
