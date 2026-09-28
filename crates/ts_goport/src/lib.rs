//! Faithful Rust port of the pinned typescript-go binder and checker.
//! Read `crates/ts_goport/PORTING.md` before editing.
//!
//! Two parts of `src` build as their own crates (`parts/`): `goport_util`
//! (`src/goport_util_root.rs`) and `goport_lsproto`
//! (`src/goport_lsproto_root.rs`). Their root files declare their modules;
//! this crate re-exports them at the same paths.

#![allow(
    dead_code,
    unused_imports,
    unused_variables,
    unused_mut,
    clippy::pedantic,
    clippy::all,
    non_snake_case
)]

pub mod ast;
pub mod baseline;
pub mod binder;
pub mod checker;
pub mod cmd;
pub mod core;
pub mod declarations;
pub use goport_util::diag;
pub mod diagnostics_loc;
pub mod emitter;
pub mod evaluator;
pub mod execute;
pub mod flags;
/// `go_enum!` and `go_flags!` (`#[macro_export]` in goport_util).
mod flags_macros {
    pub(crate) use goport_util::{go_enum, go_flags};
}
pub mod frontend;
pub use goport_util::locale;
pub mod modulespecifiers;
pub mod options;
pub mod pprof;
pub mod prelude;
pub mod printer;
pub mod program;
pub mod pseudochecker;
pub mod scanner_util;
pub mod sourcemap;
pub mod thp_guard;
pub mod tracing;
pub mod transformers;

// Macros that goport_util exports. `crate::go_assert` and `crate::unported`
// keep working.
pub use goport_util::{go_assert, unported};

// Language-service port (Go `internal/{ls,lsp,project,format,astnav,fswatch,jsonrpc,api}`).
pub mod api;
pub mod astnav;
pub mod format;
pub use goport_util::{fswatch, gostd, jsonrpc};
pub mod ls;
pub mod lsp;
pub mod project;
