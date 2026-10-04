//! Go package `scanner`.
//!
//! PORT: Go scanner/utilities.go is ported in `crate::scanner_util` only.
pub mod comment_ranges;
pub mod regexp;
pub mod scanner_p1;
pub mod scanner_p2;
pub mod unicode_properties;
// Language-service scanner helpers. Not glob-exported.
pub mod scanner_ls;
pub use comment_ranges::*;
pub use regexp::*;
pub use scanner_p1::*;
pub use scanner_p2::*;
pub use unicode_properties::*;
