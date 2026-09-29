//! Go: internal/nativepath: realpath_linux.go, realpath_other.go,
//! eintr_unix.go and symlink_other.go. realpath_darwin.go,
//! realpath_windows.go and symlink_windows.go are not ported.
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
// PORT: every target but Linux. Go has its own darwin and Windows files;
// the port uses `std::fs::canonicalize` there too (Go
// `filepath.EvalSymlinks`, as in the Linux fallback above). Not run on
// such a target.
#[cfg(not(target_os = "linux"))]
pub fn realpath(path: &str) -> Result<String, FsError> {
    std::fs::canonicalize(os_path(path))
        .map(go_string_from_os)
        .map_err(|err| FsError::path("lstat", path, err))
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

// Go: symlink_other.go:7 IsSymlinkOrReparsePoint
/// Reports whether `path` itself is a symlink. Go `os.Lstat` does not follow
/// the last link, and a path that cannot be read (missing, empty, holds a NUL
/// byte) is not a symlink.
pub fn is_symlink_or_reparse_point(path: &str) -> bool {
    std::fs::symlink_metadata(os_path(path)).is_ok_and(|info| info.file_type().is_symlink())
}
