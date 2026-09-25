//! Go `transformers/inliners` package.

pub mod const_enum;

pub use const_enum::{ConstEnumInliningTransformer, new_const_enum_inlining_transformer};
