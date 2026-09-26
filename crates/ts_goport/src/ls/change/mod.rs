//! Go package `internal/ls/change`.

pub mod delete;
pub mod tracker;
pub mod trackerimpl;

pub use delete::*;
pub use tracker::*;
pub use trackerimpl::*;

/// Glob import for change files: `use crate::ls::change::prelude::*;`.
pub mod prelude {
    pub use super::{delete::*, tracker::*, trackerimpl::*};
    pub use crate::astnav;
    pub use crate::format;
    pub use crate::frontend::json_ext::LspAny;
    pub use crate::frontend::scanner::scanner_ls;
    pub use crate::frontend::stringutil_ls;
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::ls::{lsconv, lsutil};
    pub use crate::lsp::lsproto;
    pub use crate::prelude::*;

    // Names that the crate prelude also exports. The package item wins.
    pub use super::delete::positions_are_on_same_line;
}
