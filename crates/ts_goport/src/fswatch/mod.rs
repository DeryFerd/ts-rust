//! Go package `internal/fswatch`. The platform files are reached by
//! explicit path (`fswatch::unix`, `fswatch::walkdir_unix::walk_dir`,
//! `fswatch::{inotify_linux, fanotify_linux, kqueue, windows}::init`); they
//! are not globbed. walkdir_unix.go and kqueue.go build on darwin and the BSDs
//! (`fswatch::unix` is unix_bsd.rs there), windows.go on Windows. The
//! FSEvents backend (fsevents_darwin*.go) is not ported.

pub mod canonicalize_darwin;
#[cfg(not(all(
    any(target_os = "macos", target_os = "ios"),
    any(target_arch = "x86_64", target_arch = "aarch64")
)))]
pub mod canonicalize_other;
pub mod debounce;
pub mod event;
#[cfg(target_os = "linux")]
pub mod fanotify_linux;
#[cfg(target_os = "linux")]
pub mod inotify_linux;
#[cfg(any(
    target_vendor = "apple",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd",
    target_os = "dragonfly"
))]
pub mod kqueue;
pub mod pathcompare;
pub mod pathkey;
pub mod syscall;
#[cfg(target_os = "linux")]
pub mod unix;
#[cfg(any(
    target_vendor = "apple",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd",
    target_os = "dragonfly"
))]
#[path = "unix_bsd.rs"]
pub mod unix;
pub mod walkdir;
#[cfg(any(
    target_os = "linux",
    target_vendor = "apple",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd",
    target_os = "dragonfly"
))]
pub mod walkdir_unix;
pub mod watcher;
#[cfg(windows)]
pub mod windows;

pub use canonicalize_darwin::*;
#[cfg(not(all(
    any(target_os = "macos", target_os = "ios"),
    any(target_arch = "x86_64", target_arch = "aarch64")
)))]
pub use canonicalize_other::*;
pub use debounce::*;
pub use event::*;
pub use walkdir::*;
pub use watcher::*;

/// Glob import for fswatch files: `use crate::fswatch::prelude::*;`.
pub mod prelude {
    #[cfg(not(all(
        any(target_os = "macos", target_os = "ios"),
        any(target_arch = "x86_64", target_arch = "aarch64")
    )))]
    pub use super::canonicalize_other::*;
    pub use super::{canonicalize_darwin::*, debounce::*, event::*, walkdir::*, watcher::*};
    pub use crate::frontend::json_ext::LspAny;
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::prelude::*;
}
