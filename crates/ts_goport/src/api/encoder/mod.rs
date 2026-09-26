//! Go package `internal/api/encoder`.

pub mod decoder;
pub mod decoder_generated;
pub mod encoder;
pub mod encoder_generated;
pub mod stringtable;

pub use decoder::*;
pub use decoder_generated::*;
pub use encoder::*;
pub use encoder_generated::*;
pub use stringtable::*;

/// Glob import for encoder files: `use crate::api::encoder::prelude::*;`.
pub mod prelude {
    pub use super::{
        decoder::*, decoder_generated::*, encoder::*, encoder_generated::*, stringtable::*,
    };
    pub use crate::frontend::json_ext::LspAny;
    pub use crate::frontend::tspath;
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::prelude::*;
}
