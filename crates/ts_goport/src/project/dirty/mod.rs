//! Go package `internal/project/dirty`. `dirty::Box` shadows std `Box` for
//! these files only; never glob this package into another prelude.

pub mod box_;
pub mod cloneablemap;
pub mod entry;
pub mod interfaces;
pub mod map;
pub mod mapbuilder;
pub mod syncmap;
pub mod util;

pub use box_::*;
pub use cloneablemap::*;
pub use entry::*;
pub use interfaces::*;
pub use map::*;
pub use mapbuilder::*;
pub use syncmap::*;
pub use util::*;

/// Glob import for dirty files: `use crate::project::dirty::prelude::*;`.
pub mod prelude {
    pub use super::{
        box_::*, cloneablemap::*, entry::*, interfaces::*, map::*, mapbuilder::*, syncmap::*,
        util::*,
    };
    pub use crate::frontend::json_ext::LspAny;
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::prelude::*;
}
