//! Go package `internal/execute/watchmanager`.

pub mod watchbackend;
pub mod watchmanager;

pub use watchbackend::*;
pub use watchmanager::*;

/// Glob import for watchmanager files:
/// `use crate::execute::watchmanager::prelude::*;`.
pub mod prelude {
    pub use super::{watchbackend::*, watchmanager::*};
    pub use crate::frontend::json_ext::LspAny;
    pub use crate::frontend::tspath;
    pub use crate::fswatch;
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::prelude::*;
}
