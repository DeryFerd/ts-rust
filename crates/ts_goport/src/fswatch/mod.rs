//! Go package `internal/fswatch`. Linux and unix files are reached by
//! explicit path (`fswatch::unix`, `fswatch::walkdir_unix::walk_dir`,
//! `fswatch::{inotify_linux, fanotify_linux}::init`); they are not globbed.

pub mod canonicalize_other;
pub mod debounce;
pub mod event;
#[cfg(target_os = "linux")]
pub mod fanotify_linux;
#[cfg(target_os = "linux")]
pub mod inotify_linux;
#[cfg(unix)]
pub mod unix;
pub mod walkdir;
#[cfg(unix)]
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
