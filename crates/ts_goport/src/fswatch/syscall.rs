//! The subset of Go package `syscall` that fswatch uses: `Errno`, its
//! `Error` text, and the errno values. There is no Go file for this module
//! in typescript-go. `fswatch::unix` re-exports it, as
//! `golang.org/x/sys/unix` names `syscall.Errno`.
//!
//! PORT: the values and the texts are Linux's (go1.26
//! syscall/zerrors_linux_amd64.go; Linux arm64 has the same values). The
//! portable files (walkdir.rs and watcher.rs) use only `ENOTDIR`, and the
//! other targets use the Linux value too. On darwin that is Go's value and
//! text (0x14, "not a directory").
//!
//! PORT divergence: on Windows, Go `syscall.ENOTDIR` is
//! `ERROR_PATH_NOT_FOUND` (3), whose text is the system message ("The system
//! cannot find the path specified.") and which `errors.Is` matches to
//! `fs.ErrNotExist` (go1.26 syscall/zerrors_windows.go). The port uses 0x14
//! and "not a directory" there. The Windows backend is not ported (D-W1),
//! so no Windows watch reaches it.

use crate::fswatch::prelude::*;

/// Go `syscall.Errno` (`uintptr`), the error type of every syscall.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Errno(pub usize);

pub const ENOENT: Errno = Errno(0x2);
pub const EINTR: Errno = Errno(0x4);
pub const EBADF: Errno = Errno(0x9);
pub const EAGAIN: Errno = Errno(0xb);
pub const EACCES: Errno = Errno(0xd);
pub const ENOTDIR: Errno = Errno(0x14);
pub const EINVAL: Errno = Errno(0x16);
pub const EOPNOTSUPP: Errno = Errno(0x5f);
pub const EWOULDBLOCK: Errno = Errno(0xb);

impl Errno {
    // Go: syscall/syscall_unix.go Errno.Error (go1.26)
    // PORT: Go's table has every errno; the port lists the ones fswatch
    // names and the ones fanotify_init, fanotify_mark, name_to_handle_at and
    // statfs can return (go1.26 syscall/zerrors_linux_amd64.go `errors`).
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
}

impl std::fmt::Display for Errno {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.error())
    }
}
