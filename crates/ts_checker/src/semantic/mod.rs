//! Canonical typescript-go semantic core under construction.
//!
//! This module is intentionally separate from the legacy structural checker.
//! Values from the two cores must not be mixed inside one program. In
//! particular, the IDs re-exported here are one-based canonical semantic IDs
//! branded by their aggregate [`SemanticStore`]; they have no conversion to
//! same-named legacy checker IDs.

pub mod ids;
pub mod signatures;
mod store;
pub mod type_records;
pub mod types;

pub use ids::{
    ConditionalRootId, IndexInfoId, SemanticStoreId, SemanticSymbolId, SignatureId, TypeAliasId,
    TypeId, TypeMapperId, TypePredicateId,
};
pub use store::{AstScope, SemanticStore};
pub use type_records::{CanonicalSemanticStore, TypeData, TypeDataKind, TypeRecord};
