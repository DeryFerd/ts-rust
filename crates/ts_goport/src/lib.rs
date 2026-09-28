//! Faithful Rust port of the pinned typescript-go binder and checker.
//! Read `crates/ts_goport/PORTING.md` before editing.

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
// Go `internal/contentmapper` and `internal/spanmap` (tsgo#4712).
pub mod contentmapper;
pub mod core;
pub mod declarations;
pub mod diag;
pub mod diagnostics_loc;
pub mod emitter;
pub mod evaluator;
pub mod execute;
pub mod flags;
mod flags_macros;
pub mod frontend;
pub mod locale;
pub mod modulespecifiers;
pub mod options;
pub mod pprof;
pub mod prelude;
pub mod printer;
pub mod program;
pub mod pseudochecker;
pub mod scanner_util;
pub mod sourcemap;
pub mod spanmap;
pub mod thp_guard;
pub mod tracing;
pub mod transformers;
pub mod transpile;

// Language-service port (Go `internal/{ls,lsp,project,format,astnav,fswatch,jsonrpc,api}`).
pub mod api;
pub mod astnav;
pub mod format;
pub mod fswatch;
pub mod gostd;
pub mod jsonrpc;
pub mod ls;
pub mod lsp;
pub mod project;
