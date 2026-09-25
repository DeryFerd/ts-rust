//! Go `internal/execute/tsc`. `goport`, `goport_emit` and `goport_build`
//! all compile and report through this module, as Go `tsc` does.

pub mod compile;
pub mod diagnostics;
pub mod emit;
pub mod statistics;

pub use compile::*;
pub use diagnostics::*;
pub use emit::*;
pub use statistics::*;
