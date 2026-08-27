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
pub mod artifact_queries;
mod assignment;
pub mod bootstrap;
mod callable_sets;
mod callables;
mod calls;
#[allow(dead_code)] // Incremental class cuts retain accessors reserved for later source stages.
mod classes;
mod conditional_types;
mod constraints;
mod contextual;
pub mod declared;
mod declared_values;
mod derived_types;
pub mod diagnostics;
mod enums;
pub mod formatter;
mod functions;
mod generic_calls;
mod global_types;
pub mod ids;
mod indexed_access_types;
mod inference;
mod instantiate;
mod instantiated_members;
mod interface_heritage;
#[allow(dead_code)] // Array binding owns the integration of this index query.
mod interface_indexes;
mod intersection_types;
mod iteration_types;
pub mod jsdoc;
mod jsx;
#[allow(dead_code)] // Root owns the checker-cache and type-node integration adapter.
mod keyof_types;
pub mod links;
mod logical_operators;
mod mapped_types;
pub mod mapper;
mod member_resolution;
mod merge;
mod module_exports;
pub mod module_resolution;
pub mod name_resolution;
mod object_diagnostics;
mod object_members;
mod primitive_operators;
pub mod production;
mod reference_types;
pub mod relater;
pub mod relation;
pub mod signatures;
pub mod source;
mod source_arrows;
mod source_callables;
mod source_calls;
mod source_elements;
mod source_enums;
mod source_flow;
mod source_functions;
mod source_imports;
mod source_namespaces;
mod source_new;
mod source_overloads;
mod source_properties;
mod source_statements;
mod spelling;
mod store;
mod structured_members;
mod symbol_display;
pub mod template_types;
mod tuple_type_nodes;
mod tuple_types;
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
pub use classes::{
    ClassBaseIdentities, ClassError, ClassInvariant, ClassMembers, ClassShells, ClassUnsupported,
};
pub use declared::{
    DeclaredTypeError, DeclaredTypeHost, DeclaredTypeHostError, DeclaredTypeUnavailable,
    UnsupportedDeclaredTypeKind, UnsupportedOuterTypeParameterContext,
};
pub use derived_types::DerivedTypeError;
pub use diagnostics::{
    CanonicalCheckerDiagnostic, CanonicalCheckerDiagnosticRange, CanonicalCheckerDiagnostics,
    CanonicalCheckerRelatedInformation,
};
pub use enums::{
    CanonicalEnumMemberSemantics, CanonicalEnumMemberValue, CanonicalEnumSemantics, EnumTypeError,
    EnumTypeInvariant, EnumTypeUnsupported,
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
pub use instantiated_members::{
    GenericInterfaceArrayTarget, GenericInterfaceMemberError, InstantiatedInterfaceMembers,
    InstantiatedInterfaceProperty,
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
pub use mapped_types::{
    MappedTypeError, MappedTypeModifiers, MappedTypeRequest, ResolvedMappedProperty,
    ResolvedMappedTypeMembers,
};
pub use mapper::{CanonicalTypeMapperStore, TypeMapper, TypeMapperKind};
pub use member_resolution::{CanonicalUnionPropertyError, ResolvedUnionProperty};
pub use merge::{
    CheckerDiagnosticMergeHost, FailClosedSymbolMergeHost, SymbolMergeDiagnostic,
    SymbolMergeDiagnosticKind, SymbolMergeError, SymbolMergeHost, get_excluded_symbol_flags,
};
pub use module_exports::CanonicalModuleExportQueryError;
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
pub use reference_types::DirectGenericReferenceError;
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
pub use source_functions::{SourceFunctionInvariant, SourceFunctionUnsupported};
pub use store::SemanticStore;
pub use symbol_display::SymbolDisplayError;
pub use tuple_types::EmptyTupleTypeError;
pub use type_nodes::TypeNodeUnavailable;
pub use type_records::{CacheHashKey, CanonicalSemanticStore, TypeData, TypeDataKind, TypeRecord};
pub use types::VarianceFlags;
pub use variables::{VariableInvariant, VariableUnsupported};
