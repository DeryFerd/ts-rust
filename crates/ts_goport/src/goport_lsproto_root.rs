//! Crate root of `goport_lsproto`: Go `internal/lsp/lsproto` with the
//! generated protocol types. Its files stay in `crates/ts_goport/src/lsp` and
//! keep their module paths. `ts_goport`'s `lsp/mod.rs` re-exports `lsproto`.
//! The `goport_util` modules that lsproto files reach with `crate::` paths
//! are re-exported here.

#![allow(
    dead_code,
    unused_imports,
    unused_variables,
    unused_mut,
    clippy::pedantic,
    clippy::all,
    non_snake_case
)]

pub use goport_util::{core, frontend, gostd, jsonrpc, unported};

/// The lsproto part of `crate::lsp`.
pub mod lsp {
    pub mod lsproto;
}
