//! Canonical typescript-go semantic core under construction.
//!
//! This module is intentionally separate from the legacy structural checker.
//! Values from the two cores must not be mixed inside one program. In
//! particular, the IDs re-exported here are one-based canonical semantic IDs;
//! they have no conversion to same-named legacy checker IDs.

pub mod ids;
pub mod signatures;
pub mod types;

pub use ids::{
    IndexInfoId, SemanticSymbolArena, SemanticSymbolId, SignatureId, TypeArena, TypeId,
    TypeMapperArena, TypeMapperId, TypePredicateId,
};
