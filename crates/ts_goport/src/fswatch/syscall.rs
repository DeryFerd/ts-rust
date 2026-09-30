//! The subset of Go package `syscall` that fswatch uses: `Errno`, its
//! `Error` text, and the errno values. There is no Go file for this module
//! in typescript-go. `fswatch::unix` re-exports it, as
//! `golang.org/x/sys/unix` names `syscall.Errno`.
//!
//! The rest of the port prints the Go text of an OS error with
//! `io_error_text` (osvfs, getwd, pprof, tracing, ipc, the tsgo spawn).
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
    // Go: syscall/syscall_unix.go Errno.Error (go1.26), with the texts of
    // go1.26.4 syscall/zerrors_linux_amd64.go `errors` (all of them; Linux
    // arm64 has the same table). Errnos 41, 58 and 133 have no text there.
    #[cfg(not(any(
        target_vendor = "apple",
        target_os = "freebsd",
        target_os = "openbsd",
        target_os = "netbsd",
        target_os = "dragonfly"
    )))]
    pub fn error(&self) -> String {
        let s = match self.0 {
            1 => "operation not permitted",
            2 => "no such file or directory",
            3 => "no such process",
            4 => "interrupted system call",
            5 => "input/output error",
            6 => "no such device or address",
            7 => "argument list too long",
            8 => "exec format error",
            9 => "bad file descriptor",
            10 => "no child processes",
            11 => "resource temporarily unavailable",
            12 => "cannot allocate memory",
            13 => "permission denied",
            14 => "bad address",
            15 => "block device required",
            16 => "device or resource busy",
            17 => "file exists",
            18 => "invalid cross-device link",
            19 => "no such device",
            20 => "not a directory",
            21 => "is a directory",
            22 => "invalid argument",
            23 => "too many open files in system",
            24 => "too many open files",
            25 => "inappropriate ioctl for device",
            26 => "text file busy",
            27 => "file too large",
            28 => "no space left on device",
            29 => "illegal seek",
            30 => "read-only file system",
            31 => "too many links",
            32 => "broken pipe",
            33 => "numerical argument out of domain",
            34 => "numerical result out of range",
            35 => "resource deadlock avoided",
            36 => "file name too long",
            37 => "no locks available",
            38 => "function not implemented",
            39 => "directory not empty",
            40 => "too many levels of symbolic links",
            42 => "no message of desired type",
            43 => "identifier removed",
            44 => "channel number out of range",
            45 => "level 2 not synchronized",
            46 => "level 3 halted",
            47 => "level 3 reset",
            48 => "link number out of range",
            49 => "protocol driver not attached",
            50 => "no CSI structure available",
            51 => "level 2 halted",
            52 => "invalid exchange",
            53 => "invalid request descriptor",
            54 => "exchange full",
            55 => "no anode",
            56 => "invalid request code",
            57 => "invalid slot",
            59 => "bad font file format",
            60 => "device not a stream",
            61 => "no data available",
            62 => "timer expired",
            63 => "out of streams resources",
            64 => "machine is not on the network",
            65 => "package not installed",
            66 => "object is remote",
            67 => "link has been severed",
            68 => "advertise error",
            69 => "srmount error",
            70 => "communication error on send",
            71 => "protocol error",
            72 => "multihop attempted",
            73 => "RFS specific error",
            74 => "bad message",
            75 => "value too large for defined data type",
            76 => "name not unique on network",
            77 => "file descriptor in bad state",
            78 => "remote address changed",
            79 => "can not access a needed shared library",
            80 => "accessing a corrupted shared library",
            81 => ".lib section in a.out corrupted",
            82 => "attempting to link in too many shared libraries",
            83 => "cannot exec a shared library directly",
            84 => "invalid or incomplete multibyte or wide character",
            85 => "interrupted system call should be restarted",
            86 => "streams pipe error",
            87 => "too many users",
            88 => "socket operation on non-socket",
            89 => "destination address required",
            90 => "message too long",
            91 => "protocol wrong type for socket",
            92 => "protocol not available",
            93 => "protocol not supported",
            94 => "socket type not supported",
            95 => "operation not supported",
            96 => "protocol family not supported",
            97 => "address family not supported by protocol",
            98 => "address already in use",
            99 => "cannot assign requested address",
            100 => "network is down",
            101 => "network is unreachable",
            102 => "network dropped connection on reset",
            103 => "software caused connection abort",
            104 => "connection reset by peer",
            105 => "no buffer space available",
            106 => "transport endpoint is already connected",
            107 => "transport endpoint is not connected",
            108 => "cannot send after transport endpoint shutdown",
            109 => "too many references: cannot splice",
            110 => "connection timed out",
            111 => "connection refused",
            112 => "host is down",
            113 => "no route to host",
            114 => "operation already in progress",
            115 => "operation now in progress",
            116 => "stale file handle",
            117 => "structure needs cleaning",
            118 => "not a XENIX named type file",
            119 => "no XENIX semaphores available",
            120 => "is a named type file",
            121 => "remote I/O error",
            122 => "disk quota exceeded",
            123 => "no medium found",
            124 => "wrong medium type",
            125 => "operation canceled",
            126 => "required key not available",
            127 => "key has expired",
            128 => "key has been revoked",
            129 => "key was rejected by service",
            130 => "owner died",
            131 => "state not recoverable",
            132 => "operation not possible due to RF-kill",
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

/// Go `err.Error()` of the `syscall.Errno` in an OS error: the text after
/// "op path: " in a Go `*os.PathError`, or after "op: " in a Go
/// `*os.SyscallError`.
///
/// PORT: on Linux it is Go's table (`Errno::error`). Elsewhere it is the
/// OS text without Rust's " (os error N)": Go's other unix tables are the C
/// texts with a lowercase first letter, and Go on Windows asks
/// FormatMessage, as Rust does. An error with no errno (made by std, not
/// the OS) keeps its Rust text.
pub fn io_error_text(err: &std::io::Error) -> String {
    let Some(code) = err.raw_os_error() else {
        return err.to_string();
    };
    if cfg!(target_os = "linux") {
        return Errno(code as usize).error();
    }
    let text = err.to_string();
    let text = text
        .strip_suffix(&format!(" (os error {code})"))
        .unwrap_or(&text);
    let mut chars = text.chars();
    match chars.next() {
        Some(first) if cfg!(unix) => first.to_lowercase().chain(chars).collect(),
        _ => text.to_string(),
    }
}
