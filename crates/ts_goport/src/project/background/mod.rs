//! Go package `internal/project/background`.

pub mod queue;
pub mod race;

pub use queue::*;

/// Glob import for background files: `use crate::project::background::prelude::*;`.
pub mod prelude {
    pub use super::queue::*;
    pub use crate::frontend::json_ext::LspAny;
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::prelude::*;
}
