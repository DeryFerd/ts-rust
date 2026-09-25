//! Go package `scanner`.
pub mod scanner_p1;
pub mod scanner_p2;
pub mod regexp;
pub mod unicode_properties;
// PORT: scanner/utilities.go is also in crate::scanner_util (legacy path),
// so this copy is not glob-exported.
pub mod utilities;
pub mod comment_ranges;
pub use comment_ranges::*;
pub use scanner_p1::*;
pub use scanner_p2::*;
pub use regexp::*;
pub use unicode_properties::*;
