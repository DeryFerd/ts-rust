//! Go package `internal/lsp/lsproto`. The protocol types in `lsp_generated`
//! come from `_generate/generate.mts`; never edit them by hand.

pub mod baseproto;
pub mod jsonrpc;
pub mod lsp;
pub mod lsp_generated;
pub mod util;

#[cfg(test)]
mod baseproto_test;
#[cfg(test)]
mod lsp_json_test;
#[cfg(test)]
mod lsp_test;

pub use baseproto::*;
pub use jsonrpc::*;
pub use lsp::*;
pub use lsp_generated::*;
pub use util::*;

/// Glob import for lsproto files: `use crate::lsp::lsproto::prelude::*;`.
/// It does not include the crate prelude: that one exports `Diagnostic`,
/// `FormattingOptions` and `Message`, and lsproto defines the same names.
pub mod prelude {
    pub use super::{baseproto::*, jsonrpc::*, lsp::*, lsp_generated::*, util::*};
    pub use crate::frontend::json::{
        JsonDecoder, JsonError, JsonOption, JsonToken, MarshalerTo, UnmarshalerFrom, json_marshal,
        json_new_decoder, json_unmarshal, json_unmarshal_decode,
    };
    pub use crate::frontend::json_ext::{self, *};
    pub use crate::frontend::tspath;
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::unported;
    pub use indexmap::IndexMap;
    pub use rustc_hash::FxHashMap;
    pub use std::borrow::Cow;
    pub use std::sync::Arc;
}
