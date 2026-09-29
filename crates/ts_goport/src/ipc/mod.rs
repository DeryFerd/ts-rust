//! Go package `internal/ipc`.
//!
//! tsgo#4712 moved the connection, protocol, timing and transport code here
//! from `internal/api`, so the API server and the content mapper host share
//! it. The msgpack protocol stays in `api`.

pub mod conn;
pub mod conn_async;
pub mod conn_sync;
pub mod protocol;
pub mod protocol_jsonrpc;
pub mod timing;
pub mod transport;
#[cfg(unix)]
pub mod transport_unix;

pub use conn::*;
pub use conn_async::*;
pub use conn_sync::*;
pub use protocol::*;
pub use protocol_jsonrpc::*;
pub use timing::*;
pub use transport::*;
#[cfg(unix)]
pub use transport_unix::*;

/// Glob import for ipc files: `use crate::ipc::prelude::*;`.
pub mod prelude {
    #[cfg(unix)]
    pub use super::transport_unix::*;
    pub use super::{
        conn::*, conn_async::*, conn_sync::*, protocol::*, protocol_jsonrpc::*, timing::*,
        transport::*,
    };
    pub use crate::frontend::json_ext::{self, LspAny};
    pub use crate::gostd::{self, Context, GoError};
    pub use crate::jsonrpc;
    pub use crate::prelude::*;
}
