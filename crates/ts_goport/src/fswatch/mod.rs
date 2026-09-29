//! Go package `internal/fswatch`. Linux and unix files are reached by
//! explicit path (`fswatch::unix`, `fswatch::walkdir_unix::walk_dir`,
//! `fswatch::{inotify_linux, fanotify_linux}::init`); they are not globbed.
//! In the port they are Linux only: Go also builds walkdir_unix.go on darwin
//! and the BSDs, for the kqueue and FSEvents backends, which are not ported.

pub mod canonicalize_other;
pub mod debounce;
pub mod event;
#[cfg(target_os = "linux")]
pub mod fanotify_linux;
#[cfg(target_os = "linux")]
pub mod inotify_linux;
pub mod syscall;
#[cfg(target_os = "linux")]
pub mod unix;
pub mod walkdir;
#[cfg(target_os = "linux")]
pub mod walkdir_unix;
pub mod watcher;

pub use canonicalize_other::*;
pub use debounce::*;
pub use event::*;
pub use walkdir::*;
pub use watcher::*;

/// Glob import for fswatch files: `use crate::fswatch::prelude::*;`.
pub mod prelude {
    pub use super::{canonicalize_other::*, debounce::*, event::*, walkdir::*, watcher::*};
    pub use crate::frontend::json_ext::LspAny;
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::prelude::*;
}
