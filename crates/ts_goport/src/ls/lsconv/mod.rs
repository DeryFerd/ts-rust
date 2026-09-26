//! Go package `internal/ls/lsconv`.

pub mod converters;
pub mod linemap;

pub use converters::*;
pub use linemap::*;

/// Glob import for lsconv files: `use crate::ls::lsconv::prelude::*;`.
pub mod prelude {
    pub use super::{converters::*, linemap::*};
    pub use crate::frontend::json_ext::LspAny;
    pub use crate::frontend::tspath;
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::locale;
    pub use crate::lsp::lsproto;
    pub use crate::prelude::*;
}
