//! Go `transformers/estransforms` package.
//!
//! PORT: each Go transformer struct embeds `transformers.Transformer` and
//! builds one or more `*ast.NodeVisitor` fields in its constructor. Here a
//! visitor holds `&mut` to its transformer (`NodeVisitor::ctx`), so the
//! visitors are built on demand by `TxVisitors::with_visitor` (see
//! `utilities.rs`). Go `tx.Visitor().VisitX(n)` is `self.visit_x(n)`; Go
//! `tx.fooVisitor.VisitX(n)` is
//! `self.with_visitor(Self::visit_foo, |v| v.visit_x(n))`.

pub mod class_fields;
pub mod class_fields_p2;
pub mod class_this;
pub mod definitions;
pub mod es_decorator;
pub mod es_decorator_p2;
pub mod named_evaluation;
pub mod use_strict;
pub mod using;
pub mod utilities;

pub mod async_;
pub mod exponentiation;
pub mod for_await;
pub mod logical_assignment;
pub mod nullish_coalescing;
pub mod object_rest_spread;
pub mod optional_catch;
pub mod optional_chain;
pub mod tagged_template;

pub use definitions::*;
pub use use_strict::new_use_strict_transformer;

/// The shared transformer contract of the `emitter` unit. Kept in one place so
/// a rename there is a one-line change here.
pub(crate) mod contract {
    pub(crate) use crate::transformers::chain::chain;
    pub(crate) use crate::transformers::transformer::{
        TransformOptions, TransformReferenceResolver, Transformer, TransformerBox,
    };
}
