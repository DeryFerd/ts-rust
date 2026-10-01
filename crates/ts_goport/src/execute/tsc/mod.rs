//! Go `internal/execute/tsc`. `tsgo`, `goport`, `goport_emit` and
//! `goport_build` all compile and report through this module, as Go `tsc`
//! does.

pub mod compile;
pub mod diagnostics;
pub mod emit;
pub mod help;
pub mod init;
pub mod statistics;
pub mod stdio;

pub use compile::*;
pub use diagnostics::*;
pub use emit::*;
pub use help::*;
pub use init::*;
pub use statistics::*;
