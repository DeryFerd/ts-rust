//! Go package `internal/jsonrpc`.

pub mod baseproto;
pub mod jsonrpc;

pub use baseproto::*;
pub use jsonrpc::*;

/// Glob import for jsonrpc files: `use crate::jsonrpc::prelude::*;`.
pub mod prelude {
    pub use super::{baseproto::*, jsonrpc::*};
    pub use crate::frontend::json::{
        JsonDecoder, JsonError, JsonOption, JsonToken, MarshalerTo, UnmarshalerFrom, json_marshal,
        json_new_decoder, json_unmarshal, json_unmarshal_decode,
    };
    pub use crate::frontend::json_ext::{self, LspAny};
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::prelude::*;
}
