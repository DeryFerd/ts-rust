//! Canonical typescript-go semantic core under construction.
//!
//! This module is intentionally separate from the legacy structural checker.
//! Values from the two cores must not be mixed inside one program. In
//! particular, the IDs re-exported here are one-based canonical semantic IDs
//! branded by their aggregate [`SemanticStore`]; they have no conversion to
//! same-named legacy checker IDs.

pub mod alias;
pub mod alias_flags;
pub mod alias_provider;
pub mod bootstrap;
pub mod declared;
pub mod diagnostics;
mod global_types;
pub mod ids;
pub mod links;
pub mod mapper;
mod merge;
pub mod module_resolution;
pub mod name_resolution;
pub mod production;
pub mod relation;
pub mod relater;
pub mod signatures;
mod store;
pub mod type_nodes;
pub mod type_records;
pub mod types;

pub use ts_binder::{AstScope, SemanticStoreId, SemanticSymbolId, SymbolTableId};

pub use bootstrap::{
    CheckerLinkCounts, CheckerStateSnapshot, IntrinsicBootstrap, IntrinsicBootstrapError,
    IntrinsicBootstrapOptions, SemanticArenaCounts, TypeResolutionStateSnapshot,
};
pub use alias_provider::{ProductionAliasTargetHost, ProductionAliasTargetHostError};
pub use declared::{
    DeclaredTypeError, DeclaredTypeHost, DeclaredTypeHostError, DeclaredTypeUnavailable,
    UnsupportedDeclaredTypeKind, UnsupportedOuterTypeParameterContext,
};
pub use diagnostics::{
    CanonicalCheckerDiagnostic, CanonicalCheckerDiagnostics, CanonicalCheckerRelatedInformation,
};
pub use global_types::{
    CanonicalGlobalTypeDiagnostic, CanonicalGlobalTypeInitializationError, CanonicalGlobalTypes,
};
pub use ids::{
    ConditionalRootId, IndexInfoId, SignatureId, TypeAliasId, TypeId, TypeMapperId, TypePredicateId,
};
pub use links::{
    AccessibleChainCacheKey, AliasSymbolLinks, AliasTargetState, ArrayLiteralLinks, AssertionLinks,
    ContainingSymbolLinks, DeclaredTypeLinks, DecoratorSignatureState, DeferredSymbolLinks,
    EffectsSignatureState, EntityNameNode, EntityNameRef, EnumMemberLinks, EvaluatorResult,
    EvaluatorValue, ExhaustiveState, ExportTypeLinks, ExtendedContainersState, ExternalEmitHelpers,
    JsxElementLinks, JsxFlags, LateBoundLinks, LinkHandle, LinkStore, MappedSymbolLinks,
    MarkedAssignmentSymbolLinks, MembersAndExportsLinks, MembersOrExportsResolutionKind,
    ModuleSymbolLinks, NodeCheckFlags, NodeLinks, OptionalSymbolSequence, OrderedNodeSet,
    ResolvedSignatureState, ReverseMappedSymbolLinks, SignatureLinks, SourceFileLinks,
    SourceFileRef, SpreadLinks, SwitchStatementLinks, SymbolNodeLinks, SymbolReferenceLinks,
    Tristate, TypeAliasLinks, TypeNodeLinks, TypeResolutionBoundary, TypeResolutionTarget,
    TypeResolutionTargetError, TypeSystemPropertyName, ValueSymbolLinks, VarianceLinks,
};
pub use mapper::{CanonicalTypeMapperStore, TypeMapper, TypeMapperKind};
pub use merge::{
    CheckerDiagnosticMergeHost, FailClosedSymbolMergeHost, SymbolMergeDiagnostic,
    SymbolMergeDiagnosticKind, SymbolMergeError, SymbolMergeHost, get_excluded_symbol_flags,
};
pub use module_resolution::{
    CanonicalModuleResolutionEntry, CanonicalModuleResolutionInput,
    CanonicalModuleResolutionLookup, CanonicalModuleResolutionManifest,
    CanonicalModuleResolutionManifestError, CanonicalModuleResolutionManifestInput,
    CanonicalModuleResolutionMode, CanonicalResolvedModule, CanonicalResolvedModuleInput,
};
pub use name_resolution::{ProductionNameResolverHost, ProductionNameResolverHostError};
pub use production::{
    CanonicalAliasQueryError, CanonicalCheckerContext, CanonicalCheckerContextError,
    CanonicalCheckerOptions, CanonicalGlobalInitializationError,
};
pub use relation::{
    ExpandingFlags, IntersectionState, MinArgumentCountFlags, RecursionFlags,
    RelationCacheSnapshot, RelationComparisonResult, RelationKind, RelationStateSnapshot,
    SignatureCheckMode,
};
pub use relater::RelationUnavailable;
pub use store::SemanticStore;
pub use type_nodes::TypeNodeUnavailable;
pub use type_records::{CacheHashKey, CanonicalSemanticStore, TypeData, TypeDataKind, TypeRecord};
pub use types::VarianceFlags;
