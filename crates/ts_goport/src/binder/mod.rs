//! Go package `binder`. One file per ported Go range.

pub mod binder_p1;
pub mod binder_p2;
pub mod binder_p3;
pub mod reference_resolver;

pub use binder_p1::*;
pub use binder_p2::*;
pub use binder_p3::*;
