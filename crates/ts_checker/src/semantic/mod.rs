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
mod array_diagnostics;
mod array_types;
mod assignment;
pub mod bootstrap;
mod callables;
mod contextual;
pub mod declared;
mod derived_types;
pub mod diagnostics;
pub mod formatter;
mod functions;
mod global_types;
pub mod ids;
pub mod links;
pub mod mapper;
mod merge;
pub mod module_resolution;
pub mod name_resolution;
mod object_diagnostics;
mod object_members;
pub mod production;
pub mod relater;
pub mod relation;
pub mod signatures;
pub mod source;
mod spelling;
mod store;
pub mod type_nodes;
pub mod type_records;
pub mod types;
mod variables;

pub use ts_binder::{AstScope, SemanticStoreId, SemanticSymbolId, SymbolTableId};

pub use alias_provider::{ProductionAliasTargetHost, ProductionAliasTargetHostError};
pub use array_types::ArrayTypeError;
pub use assignment::{AssignmentInvariant, AssignmentSyntaxRole, AssignmentUnsupported};
pub use bootstrap::{
    CheckerLinkCounts, CheckerStateSnapshot, IntrinsicBootstrap, IntrinsicBootstrapError,
    IntrinsicBootstrapOptions, SemanticArenaCounts, TypeResolutionStateSnapshot,
};
pub use declared::{
    DeclaredTypeError, DeclaredTypeHost, DeclaredTypeHostError, DeclaredTypeUnavailable,
    UnsupportedDeclaredTypeKind, UnsupportedOuterTypeParameterContext,
};
pub use derived_types::DerivedTypeError;
pub use diagnostics::{
    CanonicalCheckerDiagnostic, CanonicalCheckerDiagnostics, CanonicalCheckerRelatedInformation,
};
pub use formatter::{
    AssignabilityErrorDisplay, CanonicalTypeFormatFlags, TypeDisplayUnavailable,
    get_type_names_for_assignability_error, get_type_names_for_assignability_error_with_flags,
    get_type_names_for_assignability_error_with_global_types,
    get_type_names_for_assignability_error_with_global_types_and_flags, type_to_string,
    type_to_string_with_flags, type_to_string_with_global_types,
    type_to_string_with_global_types_and_flags,
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
pub use relater::RelationUnavailable;
pub use relation::{
    ExpandingFlags, IntersectionState, MinArgumentCountFlags, RecursionFlags,
    RelationCacheSnapshot, RelationComparisonResult, RelationKind, RelationStateSnapshot,
    SignatureCheckMode,
};
pub use source::{
    SourceAssertionError, SourceCheckError, SourceCheckProvenanceError, SourceLiteralCacheError,
    SourceObjectLiteralError, SourceSyntaxRole, UnsupportedSourceSyntax,
};
pub use variables::{VariableInvariant, VariableUnsupported};
pub use store::SemanticStore;
pub use type_nodes::TypeNodeUnavailable;
pub use type_records::{CacheHashKey, CanonicalSemanticStore, TypeData, TypeDataKind, TypeRecord};
pub use types::VarianceFlags;
