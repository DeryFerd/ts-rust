//! The subset of Go package `syscall` that fswatch uses: `Errno`, its
//! `Error` text, and the errno values. There is no Go file for this module
//! in typescript-go. `fswatch::unix` re-exports it, as
//! `golang.org/x/sys/unix` names `syscall.Errno`.
//!
//! PORT: on Linux (and Windows, see below) the values and the texts are
//! Linux's (go1.26 syscall/zerrors_linux_amd64.go; Linux arm64 has the same
//! values). On darwin and the BSDs, where kqueue.go and walkdir_unix.go
//! build, they are darwin's (go1.26 syscall/zerrors_darwin_amd64.go; darwin
//! arm64 and FreeBSD have the same values and texts for these errnos, except
//! that FreeBSD's EOPNOTSUPP is ENOTSUP).
//!
//! PORT divergence: on Windows, Go `syscall.ENOTDIR` is
//! `ERROR_PATH_NOT_FOUND` (3), whose text is the system message ("The system
//! cannot find the path specified.") and which `errors.Is` matches to
//! `fs.ErrNotExist` (go1.26 syscall/zerrors_windows.go). The port uses 0x14
//! and "not a directory" there. Only walkdir.rs and watcher.rs use it on
//! Windows (the Windows backend does not).

use crate::fswatch::prelude::*;

/// Go `syscall.Errno` (`uintptr`), the error type of every syscall.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Errno(pub usize);

pub const ENOENT: Errno = Errno(0x2);
pub const EINTR: Errno = Errno(0x4);
pub const EBADF: Errno = Errno(0x9);
pub const EACCES: Errno = Errno(0xd);
pub const ENODEV: Errno = Errno(0x13);
pub const ENOTDIR: Errno = Errno(0x14);
pub const EINVAL: Errno = Errno(0x16);
#[cfg(any(
    target_vendor = "apple",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd",
    target_os = "dragonfly"
))]
pub use darwin_values::*;
#[cfg(not(any(
    target_vendor = "apple",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd",
    target_os = "dragonfly"
)))]
pub use linux_values::*;

#[cfg(not(any(
    target_vendor = "apple",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd",
    target_os = "dragonfly"
)))]
mod linux_values {
    use super::Errno;
    pub const EAGAIN: Errno = Errno(0xb);
    pub const EOPNOTSUPP: Errno = Errno(0x5f);
    pub const ENOTSUP: Errno = Errno(0x5f);
    pub const EWOULDBLOCK: Errno = Errno(0xb);
}

// Go: syscall/zerrors_darwin_amd64.go (and zerrors_freebsd_amd64.go).
#[cfg(any(
    target_vendor = "apple",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd",
    target_os = "dragonfly"
))]
mod darwin_values {
    use super::Errno;
    pub const EAGAIN: Errno = Errno(0x23);
    #[cfg(target_vendor = "apple")]
    pub const EOPNOTSUPP: Errno = Errno(0x66);
    #[cfg(not(target_vendor = "apple"))]
    pub const EOPNOTSUPP: Errno = Errno(0x2d);
    pub const ENOTSUP: Errno = Errno(0x2d);
    pub const EWOULDBLOCK: Errno = Errno(0x23);
}

impl Errno {
    // Go: syscall/syscall_unix.go Errno.Error (go1.26)
    // PORT: Go's table has every errno; the port lists the ones fswatch
    // names and the ones fanotify_init, fanotify_mark, name_to_handle_at and
    // statfs can return (go1.26 syscall/zerrors_linux_amd64.go `errors`).
    #[cfg(not(any(
        target_vendor = "apple",
        target_os = "freebsd",
        target_os = "openbsd",
        target_os = "netbsd",
        target_os = "dragonfly"
    )))]
    pub fn error(&self) -> String {
        let s = match self.0 {
            0x1 => "operation not permitted",
            0x2 => "no such file or directory",
            0x4 => "interrupted system call",
            0x5 => "input/output error",
            0x9 => "bad file descriptor",
            0xb => "resource temporarily unavailable",
            0xc => "cannot allocate memory",
            0xd => "permission denied",
            0xe => "bad address",
            0x11 => "file exists",
            0x12 => "invalid cross-device link",
            0x13 => "no such device",
            0x14 => "not a directory",
            0x16 => "invalid argument",
            0x18 => "too many open files",
            0x1c => "no space left on device",
            0x24 => "file name too long",
            0x26 => "function not implemented",
            0x28 => "too many levels of symbolic links",
            0x4b => "value too large for defined data type",
            0x5f => "operation not supported",
            _ => "",
        };
        if !s.is_empty() {
            return s.to_string();
        }
        format!("errno {}", self.0)
    }

    // Go: syscall/syscall_unix.go Errno.Error (go1.26), darwin table
    // PORT: the errnos that kqueue.go, walkdir_unix.go and their syscalls
    // can return (go1.26 syscall/zerrors_darwin_amd64.go `errors`).
    #[cfg(any(
        target_vendor = "apple",
        target_os = "freebsd",
        target_os = "openbsd",
        target_os = "netbsd",
        target_os = "dragonfly"
    ))]
    pub fn error(&self) -> String {
        let s = match self.0 {
            0x1 => "operation not permitted",
            0x2 => "no such file or directory",
            0x4 => "interrupted system call",
            0x5 => "input/output error",
            0x9 => "bad file descriptor",
            0xc => "cannot allocate memory",
            0xd => "permission denied",
            0xe => "bad address",
            0x11 => "file exists",
            0x13 => "operation not supported by device",
            0x14 => "not a directory",
            0x16 => "invalid argument",
            0x18 => "too many open files",
            0x1c => "no space left on device",
            0x23 => "resource temporarily unavailable",
            0x2d => "operation not supported",
            0x3e => "too many levels of symbolic links",
            0x3f => "file name too long",
            0x4e => "function not implemented",
            0x54 => "value too large to be stored in data type",
            #[cfg(target_vendor = "apple")]
            0x66 => "operation not supported on socket",
            _ => "",
        };
        if !s.is_empty() {
            return s.to_string();
        }
        format!("errno {}", self.0)
    }
}

impl std::fmt::Display for Errno {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.error())
    }
}
