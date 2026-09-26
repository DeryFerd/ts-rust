//! Go package `internal/lsp/lspwatcher`.

pub mod lspwatcher;

pub use lspwatcher::*;

/// Glob import for lspwatcher files: `use crate::lsp::lspwatcher::prelude::*;`.
pub mod prelude {
    pub use super::lspwatcher::*;
    pub use crate::frontend::json_ext::LspAny;
    pub use crate::frontend::{tspath, vfs};
    pub use crate::fswatch;
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::ls::lsconv;
    pub use crate::lsp::lsproto;
    pub use crate::prelude::*;
    pub use crate::project::logging;
}
