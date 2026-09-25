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
pub mod binder;
pub mod checker;
pub mod core;
pub mod declarations;
pub mod diag;
pub mod evaluator;
pub mod flags;
mod flags_macros;
pub mod frontend;
pub mod modulespecifiers;
pub mod options;
pub mod prelude;
pub mod printer;
pub mod program;
pub mod pseudochecker;
pub mod scanner_util;
