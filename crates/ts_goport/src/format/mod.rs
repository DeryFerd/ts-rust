//! Go package `internal/format`.

pub mod api;
pub mod context;
pub mod indent;
pub mod rule;
pub mod rulecontext;
pub mod rules;
pub mod rulesmap;
pub mod scanner;
pub mod span;
pub mod util;

#[cfg(test)]
mod api_test;
#[cfg(test)]
mod comment_test;
#[cfg(test)]
mod format_test;
#[cfg(test)]
mod indent_getindentation_test;
#[cfg(test)]
mod indent_test;

pub use api::*;
pub use context::*;
pub use indent::*;
pub use rule::*;
pub use rulecontext::*;
pub use rules::*;
pub use rulesmap::*;
pub use scanner::*;
pub use span::*;
pub use util::*;

/// Glob import for format files: `use crate::format::prelude::*;`.
/// `Context` is the gostd context; the file module `context` is not
/// re-exported by name.
pub mod prelude {
    pub use super::{
        api::*, context::*, indent::*, rule::*, rulecontext::*, rules::*, rulesmap::*, scanner::*,
        span::*, util::*,
    };
    pub use crate::astnav;
    pub use crate::frontend::json_ext::LspAny;
    pub use crate::frontend::scanner::scanner_ls;
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::ls::lsutil;
    pub use crate::prelude::*;
}
