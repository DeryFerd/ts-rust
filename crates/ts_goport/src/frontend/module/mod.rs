//! Go package `module`.
pub mod cache;
pub mod entrypoints;
pub mod resolver_p1;
pub mod resolver_p2;
pub mod staticresolver;
pub mod types;
pub mod util;
pub use cache::*;
pub use entrypoints::*;
pub use resolver_p1::*;
pub use resolver_p2::*;
pub use staticresolver::*;
pub use types::*;
pub use util::*;
