//! Go package `internal/api`.

pub mod callbackfs;
pub mod conn;
pub mod conn_async;
pub mod conn_sync;
pub mod encoder;
pub mod proto;
pub mod protocol;
pub mod protocol_jsonrpc;
pub mod protocol_msgpack;
pub mod server;
pub mod session_p1;
pub mod session_p2;
pub mod stringer_generated;
pub mod timing;
pub mod transport;
#[cfg(unix)]
pub mod transport_unix;

pub use callbackfs::*;
pub use conn::*;
pub use conn_async::*;
pub use conn_sync::*;
pub use proto::*;
pub use protocol::*;
pub use protocol_jsonrpc::*;
pub use protocol_msgpack::*;
pub use server::*;
pub use session_p1::*;
pub use session_p2::*;
pub use stringer_generated::*;
pub use timing::*;
pub use transport::*;
#[cfg(unix)]
pub use transport_unix::*;

/// Glob import for api files: `use crate::api::prelude::*;`.
pub mod prelude {
    #[cfg(unix)]
    pub use super::transport_unix::*;
    pub use super::{
        callbackfs::*, conn::*, conn_async::*, conn_sync::*, proto::*, protocol::*,
        protocol_jsonrpc::*, protocol_msgpack::*, server::*, session_p1::*, session_p2::*,
        stringer_generated::*, timing::*, transport::*,
    };
    pub use crate::api::encoder;
    pub use crate::astnav;
    pub use crate::frontend::bundled;
    pub use crate::frontend::json_ext::{self, LspAny};
    pub use crate::frontend::vfs::osvfs;
    pub use crate::frontend::{compiler, tsoptions, tspath, vfs};
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::jsonrpc;
    pub use crate::locale;
    pub use crate::ls::{self, lsconv};
    pub use crate::lsp::lsproto;
    pub use crate::prelude::*;
    pub use crate::program::ls_program;
    pub use crate::project;
}
