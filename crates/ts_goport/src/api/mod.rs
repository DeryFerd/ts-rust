//! Go package `internal/api`.
//!
//! tsgo#4712 moved the connection, protocol, timing and transport code to
//! `crate::ipc` (Go `internal/ipc`). The msgpack protocol stays here.

pub mod callbackfs;
pub mod encoder;
pub mod module_resolution;
pub mod proto;
pub mod protocol_msgpack;
pub mod requestfilesystem;
pub mod server;
pub mod session_p1;
pub mod session_p2;
pub mod stringer_generated;

pub use callbackfs::*;
pub use module_resolution::*;
pub use proto::*;
pub use protocol_msgpack::*;
pub use server::*;
pub use session_p1::*;
pub use session_p2::*;
pub use stringer_generated::*;

/// Glob import for api files: `use crate::api::prelude::*;`.
pub mod prelude {
    pub use super::{
        callbackfs::*, module_resolution::*, proto::*, protocol_msgpack::*, server::*,
        session_p1::*, session_p2::*, stringer_generated::*,
    };
    pub use crate::api::encoder;
    pub use crate::astnav;
    pub use crate::frontend::bundled;
    pub use crate::frontend::json_ext::{self, LspAny};
    pub use crate::frontend::vfs::osvfs;
    pub use crate::frontend::{compiler, tsoptions, tspath, vfs};
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::ipc;
    pub use crate::jsonrpc;
    pub use crate::locale;
    pub use crate::ls::{self, lsconv};
    pub use crate::lsp::lsproto;
    pub use crate::prelude::*;
    pub use crate::program::ls_program;
    pub use crate::project;
}
