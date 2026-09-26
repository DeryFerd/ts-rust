//! Go package `cmd/tsgo` (package main).

pub mod api;
#[cfg(not(unix))]
pub mod isprocessalive_other;
#[cfg(unix)]
pub mod isprocessalive_unix;
pub mod lsp;
pub mod main;

pub use main::run_main;

/// Glob import for cmd/tsgo files: `use crate::cmd::tsgo::prelude::*;`.
/// `lsp` and `api` here are the packages `crate::lsp` and `crate::api`,
/// not the files of the same name.
pub mod prelude {
    #[cfg(not(unix))]
    pub use super::isprocessalive_other::*;
    #[cfg(unix)]
    pub use super::isprocessalive_unix::*;
    pub use super::{api::*, lsp::*, main::*};
    pub use crate::api;
    pub use crate::execute::{self, tsc};
    pub use crate::frontend::bundled;
    pub use crate::frontend::vfs::osvfs;
    pub use crate::frontend::{tspath, vfs};
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::lsp;
    pub use crate::prelude::*;
}
