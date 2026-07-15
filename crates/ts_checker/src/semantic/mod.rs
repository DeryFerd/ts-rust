//! Canonical typescript-go semantic core under construction.
//!
//! This module is intentionally separate from the legacy structural checker.
//! Values from the two cores must not be mixed inside one program. In
//! particular, the IDs re-exported here are one-based canonical semantic IDs
//! branded by their aggregate [`SemanticStore`]; they have no conversion to
//! same-named legacy checker IDs.

pub mod ids;
pub mod links;
pub mod mapper;
pub mod signatures;
mod store;
pub mod type_records;
pub mod types;

pub use ts_binder::{AstScope, SemanticStoreId, SemanticSymbolId, SymbolTableId};

pub use ids::{
    ConditionalRootId, IndexInfoId, SignatureId, TypeAliasId, TypeId, TypeMapperId, TypePredicateId,
};
pub use links::{
    AliasSymbolLinks, DeclaredTypeLinks, LinkHandle, LinkStore, NodeCheckFlags, NodeLinks,
    ResolutionState, SignatureLinks, SymbolNodeLinks, SymbolReferenceLinks, Tristate,
    TypeAliasLinks, TypeNodeLinks, TypeResolutionTarget, TypeResolutionTargetError,
    TypeSystemPropertyName, ValueSymbolLinks,
};
pub use mapper::{CanonicalTypeMapperStore, TypeMapper, TypeMapperKind};
pub use store::SemanticStore;
pub use type_records::{CacheHashKey, CanonicalSemanticStore, TypeData, TypeDataKind, TypeRecord};
