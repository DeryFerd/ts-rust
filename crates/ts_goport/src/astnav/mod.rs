//! Go package `internal/astnav`.

pub mod tokens;

pub use tokens::*;

/// Glob import for astnav files: `use crate::astnav::prelude::*;`.
pub mod prelude {
    pub use super::tokens::*;
    pub use crate::frontend::json_ext::LspAny;
    pub use crate::frontend::scanner::scanner_ls;
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::prelude::*;
}
