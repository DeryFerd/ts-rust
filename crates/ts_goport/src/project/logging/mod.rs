//! Go package `internal/project/logging`.

pub mod logcollector;
pub mod logger;
pub mod logtree;

pub use logcollector::*;
pub use logger::*;
pub use logtree::*;

/// Glob import for logging files: `use crate::project::logging::prelude::*;`.
pub mod prelude {
    pub use super::{logcollector::*, logger::*, logtree::*};
    pub use crate::frontend::json_ext::LspAny;
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::prelude::*;
}
