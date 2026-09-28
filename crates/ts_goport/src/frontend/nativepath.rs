//! Go: internal/nativepath (Linux only): realpath_linux.go, eintr_unix.go
//! and symlink_other.go.
//!
//! OS path helpers that osvfs and fswatch share. Paths are OS paths in the
//! port form (see `vfs::osvfs::os_path`).

use crate::frontend::vfs::FsError;
use crate::frontend::vfs::osvfs::{go_string_from_os, os_path};
use std::io;
use std::os::fd::AsRawFd;
use std::os::unix::fs::OpenOptionsExt;
use std::sync::OnceLock;

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

// Go: realpath_linux.go:39 Realpath
// On Linux, we use the O_PATH + /proc/self/fd trick to resolve the canonical
// path in O(1) syscalls (open + readlink + close) instead of Go's
// filepath.EvalSymlinks which does an lstat per path component — O(depth).
//
// Falls back to filepath.EvalSymlinks if /proc is not available (e.g. containers
// or chroots without procfs mounted).
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
