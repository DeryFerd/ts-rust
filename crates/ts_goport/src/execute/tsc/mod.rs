//! Go `internal/execute/tsc`.

pub mod compile;
pub mod diagnostics;
pub mod emit;

pub use compile::*;
pub use diagnostics::*;
pub use emit::*;
