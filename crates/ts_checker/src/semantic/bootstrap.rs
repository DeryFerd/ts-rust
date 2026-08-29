//! Exact dependency-closed `NewChecker` intrinsic bootstrap.
//!
//! This module is pinned to `internal/checker/checker.go` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`, from the checker-owned symbols
//! through `typeofType` (approximately lines 953-1050). It deliberately stops
//! at semantic boundaries that the canonical graph cannot yet represent:
//!
//! - `uniqueLiteralMapper`, the report mappers, and the restrictive/permissive
//!   mappers own executable Go callbacks. [`TypeMapper`] intentionally has no
//!   callback-shaped variant, so those five fields and their APIs remain absent.
//! - name resolvers, file-global merges, global-library lookup, relation-key
//!   construction and relation algorithms, flow caches, and
//!   `initializeChecker` depend on Program/host behavior. The relation cache
//!   owners exist as exact empty state, but no relation result is fabricated.
//!   The empty globals table and `globalThis` insertion performed by
//!   `NewChecker` itself are included; resolving or augmenting that table is
//!   not.
//! - template-literal reduction remains outside this module. The closed
//!   bootstrap cases below encode its pinned normalized results. Literal and
//!   dependency-closed union cache ownership stays here; the expression-union
//!   prefix additionally admits recursively canonical unions and fresh,
//!   property-only object literals for exact array-literal subtype reduction,
//!   their authenticated regular and widened counterparts, plus resolved
//!   nongeneric declared property objects as canonical array elements.

use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
};

use ts_ast::{NodeRef, SyntaxKind};
use ts_binder::{
    CheckFlags, EscapedName, InternalSymbolName, SemanticStoreId, SemanticSymbolId, SymbolFlags,
    SymbolTableId,
};
use ts_jsnum::{Number, PseudoBigInt};

use super::{
    CanonicalGlobalTypes, CanonicalTypeMapperStore,
    array_types::{ArrayTypeError, CanonicalArrayTargets},
    callable_sets::{
        StoredCallableSetValidation, validate_stored_callable_set,
        validate_stored_declared_method_callable_set, validated_method_annotation_type,
    },
    callables::CallableFamily,
    classes::{ClassHeritageMembersValidation, validate_class_heritage_members},
    declared::{cached_class_type, cached_interface_type, cached_ordinary_type_parameter_owner},
    derived_types::DerivedObjectLiteralValidation,
    enums::{validate_enum_type_union_constituent, validate_enum_value_union_constituent},
    functions::{self, PendingFunctionTypeProof},
    ids::{IndexInfoId, SignatureId, TypeAliasId, TypeId, TypePredicateId},
    indexed_access_types::cached_deferred_indexed_access_type,
    links::{LateBoundLinks, SignatureLinks, TypeNodeLinks, ValueSymbolLinks},
    mapper::{TypeMapper, TypeMapperApplication},
    object_members,
    reference_types::{
        validate_direct_generic_reference, validate_nongeneric_interface_argument_origin,
    },
    relation::RelationStateSnapshot,
    signatures::{IndexFlags, SignatureFlags, TypePredicateKind},
    store::{SemanticStore, SourceNodeParent},
    structured_members::{
        InterfaceHeritageMembersValidation, inherited_generic_property_reference,
        valid_declared_member_table, validate_interface_heritage_members_with_array_targets,
    },
    tuple_types::PreparedCanonicalTupleType,
    type_records::{
        ConstituentMapState, ConstrainedTypeData, IndexedAccessTypeData, InterfaceTypeData,
        LiteralValue, ObjectTypeData, RegularLiteralLink, StructuredTypeData, TypeCacheState,
        TypeData, TypeRecord,
    },
    types::{AccessFlags, ObjectFlags, TypeFlags},
};

/// The two compiler options that alter pinned intrinsic bootstrap identity.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct IntrinsicBootstrapOptions {
    pub strict_null_checks: bool,
    pub exact_optional_property_types: bool,
}

/// Arena counts captured before a rejected bootstrap attempt.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SemanticArenaCounts {
    pub types: usize,
    pub mappers: usize,
    pub signatures: usize,
    pub predicates: usize,
    pub index_infos: usize,
    pub type_aliases: usize,
    pub conditional_roots: usize,
    pub entity_names: usize,
}

impl SemanticArenaCounts {
    const fn is_empty(self) -> bool {
        self.types == 0
            && self.mappers == 0
            && self.signatures == 0
            && self.predicates == 0
            && self.index_infos == 0
            && self.type_aliases == 0
            && self.conditional_roots == 0
            && self.entity_names == 0
    }
}

/// Allocated record counts for the canonical sparse checker link stores.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CheckerLinkCounts {
    pub node: usize,
    pub symbol_node: usize,
    pub type_node: usize,
    pub enum_member: usize,
    pub assertion: usize,
    pub array_literal: usize,
    pub switch_statement: usize,
    pub jsx_element: usize,
    pub signature: usize,
    pub symbol_reference: usize,
    pub value_symbol: usize,
    pub mapped_symbol: usize,
    pub deferred_symbol: usize,
    pub alias_symbol: usize,
    pub module_symbol: usize,
    pub late_bound: usize,
    pub export_type: usize,
    pub members_and_exports: usize,
    pub type_alias: usize,
    pub declared_type: usize,
    pub spread: usize,
    pub variance: usize,
    pub reverse_mapped_symbol: usize,
    pub marked_assignment_symbol: usize,
    pub containing_symbol: usize,
    pub source_file: usize,
}

impl CheckerLinkCounts {
    const fn is_empty(self) -> bool {
        self.node == 0
            && self.symbol_node == 0
            && self.type_node == 0
            && self.enum_member == 0
            && self.assertion == 0
            && self.array_literal == 0
            && self.switch_statement == 0
            && self.jsx_element == 0
            && self.signature == 0
            && self.symbol_reference == 0
            && self.value_symbol == 0
            && self.mapped_symbol == 0
            && self.deferred_symbol == 0
            && self.alias_symbol == 0
            && self.module_symbol == 0
            && self.late_bound == 0
            && self.export_type == 0
            && self.members_and_exports == 0
            && self.type_alias == 0
            && self.declared_type == 0
            && self.spread == 0
            && self.variance == 0
            && self.reverse_mapped_symbol == 0
            && self.marked_assignment_symbol == 0
            && self.containing_symbol == 0
            && self.source_file == 0
    }
}

/// Observable and fail-closed history of the type-resolution stack.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct TypeResolutionStateSnapshot {
    pub entries: usize,
    pub resolution_start: usize,
    pub boundaries: usize,
    pub next_boundary_serial: u64,
}

impl TypeResolutionStateSnapshot {
    const fn is_pristine(self) -> bool {
        self.entries == 0
            && self.resolution_start == 0
            && self.boundaries == 0
            && self.next_boundary_serial == 0
    }
}

/// All checker-owned state that must be pristine before `NewChecker` bootstrap.
///
/// Binder-owned symbols/tables, their lazy global IDs, and registered AST
/// scopes may predate checker construction. Checker-transient symbols are
/// counted separately and therefore fail closed.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct CheckerStateSnapshot {
    pub checker_symbols: usize,
    pub merged_symbols: usize,
    pub source_callable_types: usize,
    pub source_callable_declarations: usize,
    pub source_callable_owners: usize,
    pub source_callable_signatures: usize,
    pub source_callable_type_parameters: usize,
    pub cached_signatures: usize,
    pub callable_signature_parameter_types: usize,
    pub semantic_arenas: SemanticArenaCounts,
    pub links: CheckerLinkCounts,
    pub type_resolution: TypeResolutionStateSnapshot,
    pub relations: RelationStateSnapshot,
}

impl CheckerStateSnapshot {
    const fn is_pristine(self) -> bool {
        self.checker_symbols == 0
            && self.merged_symbols == 0
            && self.source_callable_types == 0
            && self.source_callable_declarations == 0
            && self.source_callable_owners == 0
            && self.source_callable_signatures == 0
            && self.source_callable_type_parameters == 0
            && self.cached_signatures == 0
            && self.callable_signature_parameter_types == 0
            && self.semantic_arenas.is_empty()
            && self.links.is_empty()
            && self.type_resolution.is_pristine()
            && self.relations.is_pristine()
    }
}

/// A bootstrap request rejected before any semantic allocation is performed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum IntrinsicBootstrapError {
    /// The store already owns the singleton set under different compiler options.
    OptionsMismatch {
        initialized: IntrinsicBootstrapOptions,
        requested: IntrinsicBootstrapOptions,
    },
    /// `NewChecker` bootstrap must precede every checker-owned write.
    NonPristineCheckerState(Box<CheckerStateSnapshot>),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct NumberLiteralCacheKey(u64);

impl NumberLiteralCacheKey {
    fn from_number(value: Number) -> Option<Self> {
        if value.is_nan() {
            return None;
        }
        let value = value.value();
        // Go map equality treats -0 and +0 as the same key. NaN has a separate
        // upstream slot and is never populated by NewChecker bootstrap.
        Some(Self(if value == 0.0 { 0 } else { value.to_bits() }))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum LiteralTypeCacheError {
    BootstrapUninitialized,
    InvalidValue,
    InvalidCachedLiteral(TypeId),
    InvalidCachedUnion(TypeId),
    UnsupportedUnionConstituent(TypeId),
    ArrayType {
        type_: TypeId,
        error: ArrayTypeError,
    },
    InvalidUnionAlias(SemanticSymbolId),
    InvalidPreparedQuery,
    Capacity,
}

impl std::fmt::Display for LiteralTypeCacheError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BootstrapUninitialized => {
                formatter.write_str("literal type cache requires intrinsic bootstrap")
            }
            Self::InvalidValue => {
                formatter.write_str("literal type cache received an invalid value")
            }
            Self::InvalidCachedLiteral(type_id) => {
                write!(
                    formatter,
                    "literal type {type_id:?} has invalid cache links"
                )
            }
            Self::InvalidCachedUnion(type_id) => {
                write!(
                    formatter,
                    "union type {type_id:?} has an invalid cache entry"
                )
            }
            Self::UnsupportedUnionConstituent(type_id) => write!(
                formatter,
                "type {type_id:?} is outside the installed union constituent domain"
            ),
            Self::ArrayType { error, .. } => error.fmt(formatter),
            Self::InvalidUnionAlias(symbol) => {
                write!(formatter, "union alias {symbol:?} is invalid")
            }
            Self::InvalidPreparedQuery => {
                formatter.write_str("literal type cache received an invalid prepared query")
            }
            Self::Capacity => formatter.write_str("literal type cache capacity was exhausted"),
        }
    }
}

impl std::error::Error for LiteralTypeCacheError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::ArrayType { error, .. } => Some(error),
            _ => None,
        }
    }
}

/// Pinned `UnionReduction` modes supported by canonical union construction.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum UnionReduction {
    None,
    Literal,
    Subtype,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct UnionAliasCacheKey {
    symbol: SemanticSymbolId,
    type_arguments: Vec<TypeId>,
}

impl UnionAliasCacheKey {
    fn new(symbol: SemanticSymbolId, type_arguments: &[TypeId]) -> Self {
        Self {
            symbol,
            type_arguments: type_arguments.to_vec(),
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum UnionOriginCacheKey {
    /// Pinned `getUnionKey` writes `|` followed by the denormalized union
    /// constituents. The origin shell itself is intentionally not part of the
    /// key and may therefore be allocated only after a cache miss.
    DenormalizedUnion(Vec<TypeId>),
    /// Pinned `getUnionKey` writes `#`, the exact index-origin identity, and
    /// then the normalized constituent list already stored on the enclosing
    /// [`UnionTypeCacheKey`].
    Index(TypeId),
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum UnionOriginPlan {
    DenormalizedUnion(Vec<TypeId>),
    ExistingIndex(TypeId),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct UnionTypeCacheKey {
    types: Vec<TypeId>,
    /// `Some` is the exact pinned origin branch. `None` uses the normalized
    /// constituent list, matching pinned `getUnionKey`.
    origin: Option<UnionOriginCacheKey>,
    alias: Option<UnionAliasCacheKey>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct UnionAliasSourceOwner {
    symbol: SemanticSymbolId,
    flags: SymbolFlags,
    parent: Option<SemanticSymbolId>,
    declarations: Option<Vec<NodeRef>>,
}

/// Created only by canonical union construction and kept outside mutable caches.
#[derive(Debug, Eq, PartialEq)]
pub(super) struct CanonicalUnionCreationProof {
    union: TypeId,
    key: UnionTypeCacheKey,
    owners: Vec<UnionAliasSourceOwner>,
}

impl CanonicalUnionCreationProof {
    pub(super) const fn type_id(&self) -> TypeId {
        self.union
    }
}

impl UnionTypeCacheKey {
    fn anonymous(types: Vec<TypeId>) -> Self {
        Self {
            types,
            origin: None,
            alias: None,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct UnionOfUnionCacheKey {
    first: TypeId,
    second: TypeId,
    reduction: UnionReduction,
    alias: Option<UnionAliasCacheKey>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum UnionPlan {
    Existing(TypeId),
    Union {
        types: Vec<TypeId>,
        object_flags: ObjectFlags,
        alias: Option<UnionAliasCacheKey>,
        origin: Option<UnionOriginPlan>,
    },
}

enum UnionMembersPlan {
    Existing(TypeId),
    Members {
        types: Vec<TypeId>,
        includes: TypeFlags,
    },
}

#[derive(Clone, Copy)]
enum UnionArrayValidation<'globals> {
    None,
    GlobalTypes(&'globals CanonicalGlobalTypes),
    Targets(super::array_types::CanonicalArrayTargets),
}

impl<'globals> UnionArrayValidation<'globals> {
    const fn from_global_types(global_types: Option<&'globals CanonicalGlobalTypes>) -> Self {
        match global_types {
            Some(global_types) => Self::GlobalTypes(global_types),
            None => Self::None,
        }
    }

    const fn targets(self) -> Option<CanonicalArrayTargets> {
        match self {
            Self::None => None,
            Self::GlobalTypes(globals) => Some(CanonicalArrayTargets::from_global_types(globals)),
            Self::Targets(targets) => Some(targets),
        }
    }

    const fn global_types(self) -> Option<&'globals CanonicalGlobalTypes> {
        match self {
            Self::GlobalTypes(globals) => Some(globals),
            Self::None | Self::Targets(_) => None,
        }
    }
}

/// Store-branded, single-owner proof and budget for one dependency-closed
/// type-node execution's completed cache validation and reservation.
#[derive(Debug, Eq, PartialEq)]
pub(super) struct PreparedTypeQueryTypes {
    store: SemanticStoreId,
    array_targets: Option<CanonicalArrayTargets>,
    union_operations_remaining: usize,
    named_union_operations_remaining: usize,
    pending_function_types: HashSet<TypeId>,
    canonical_tuple_types: HashMap<NodeRef, PreparedCanonicalTupleType>,
}

impl PreparedTypeQueryTypes {
    pub(super) fn accepts_tuple_preparation(
        &self,
        store: SemanticStoreId,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> bool {
        self.store == store
            && self.array_targets == array_targets
            && self.canonical_tuple_types.is_empty()
    }

    pub(super) fn install_canonical_tuple_types(
        &mut self,
        store: SemanticStoreId,
        array_targets: Option<CanonicalArrayTargets>,
        prepared: HashMap<NodeRef, PreparedCanonicalTupleType>,
    ) -> Result<(), LiteralTypeCacheError> {
        if !self.accepts_tuple_preparation(store, array_targets) {
            return Err(LiteralTypeCacheError::InvalidPreparedQuery);
        }
        self.canonical_tuple_types = prepared;
        Ok(())
    }

    pub(super) fn take_canonical_tuple_type(
        &mut self,
        store: SemanticStoreId,
        node: NodeRef,
    ) -> Result<PreparedCanonicalTupleType, LiteralTypeCacheError> {
        if self.store != store {
            return Err(LiteralTypeCacheError::InvalidPreparedQuery);
        }
        self.canonical_tuple_types
            .remove(&node)
            .ok_or(LiteralTypeCacheError::InvalidPreparedQuery)
    }

    fn consume_union(
        &mut self,
        store: SemanticStoreId,
        named: bool,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> Result<(), LiteralTypeCacheError> {
        if self.store != store
            || self.array_targets != array_targets
            || self.union_operations_remaining == 0
            || named && self.named_union_operations_remaining == 0
        {
            return Err(LiteralTypeCacheError::InvalidPreparedQuery);
        }
        self.union_operations_remaining -= 1;
        if named {
            self.named_union_operations_remaining -= 1;
        }
        Ok(())
    }

    pub(super) fn clear_pending_function_types(&mut self) {
        self.pending_function_types.clear();
    }

    pub(super) fn authorize_pending_function(
        &mut self,
        store: &CanonicalTypeMapperStore,
        proof: &PendingFunctionTypeProof,
    ) -> Result<(), LiteralTypeCacheError> {
        if proof.store() != self.store
            || proof.array_targets() != self.array_targets
            || !functions::validate_pending_function_type_proof(store, proof)
        {
            return Err(LiteralTypeCacheError::InvalidPreparedQuery);
        }
        self.pending_function_types.insert(proof.type_());
        Ok(())
    }

    pub(super) fn finish_pending_function(
        &mut self,
        proof: &PendingFunctionTypeProof,
    ) -> Result<(), LiteralTypeCacheError> {
        if proof.store() != self.store || !self.pending_function_types.remove(&proof.type_()) {
            return Err(LiteralTypeCacheError::InvalidPreparedQuery);
        }
        Ok(())
    }

    pub(super) fn preflight_union_operations(
        &self,
        store: &CanonicalTypeMapperStore,
        targets: Option<CanonicalArrayTargets>,
        count: usize,
    ) -> Result<(), LiteralTypeCacheError> {
        if self.store != store.id()
            || self.array_targets != targets
            || self.union_operations_remaining < count
        {
            return Err(LiteralTypeCacheError::InvalidPreparedQuery);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct TemplateLiteralCacheKey {
    texts: Vec<String>,
    types: Vec<TypeId>,
}

/// Store-owned identities initialized by pinned `NewChecker`.
///
/// Fields are IDs rather than cloned semantic records. Distinct fields remain
/// distinct even when their flags and names match; option-controlled upstream
/// pointer aliases remain equal IDs.
#[derive(Debug, Eq, PartialEq)]
pub struct IntrinsicBootstrap {
    pub options: IntrinsicBootstrapOptions,

    pub globals: SymbolTableId,
    pub undefined_symbol: SemanticSymbolId,
    pub arguments_symbol: SemanticSymbolId,
    pub require_symbol: SemanticSymbolId,
    pub unknown_symbol: SemanticSymbolId,
    pub global_this_symbol: SemanticSymbolId,

    pub any_type: TypeId,
    pub auto_type: TypeId,
    pub wildcard_type: TypeId,
    pub blocked_string_type: TypeId,
    pub error_type: TypeId,
    pub unresolved_type: TypeId,
    pub non_inferrable_any_type: TypeId,
    pub intrinsic_marker_type: TypeId,
    pub unknown_type: TypeId,
    pub undefined_type: TypeId,
    pub undefined_widening_type: TypeId,
    pub missing_type: TypeId,
    pub undefined_or_missing_type: TypeId,
    pub optional_type: TypeId,
    pub null_type: TypeId,
    pub null_widening_type: TypeId,
    pub string_type: TypeId,
    pub number_type: TypeId,
    pub bigint_type: TypeId,
    pub regular_false_type: TypeId,
    pub false_type: TypeId,
    pub regular_true_type: TypeId,
    pub true_type: TypeId,
    pub boolean_type: TypeId,
    pub es_symbol_type: TypeId,
    pub void_type: TypeId,
    pub never_type: TypeId,
    pub silent_never_type: TypeId,
    pub implicit_never_type: TypeId,
    pub unreachable_never_type: TypeId,
    pub non_primitive_type: TypeId,
    pub string_or_number_type: TypeId,
    pub string_number_symbol_type: TypeId,
    pub number_or_bigint_type: TypeId,
    pub numeric_string_type: TypeId,
    pub template_constraint_type: TypeId,
    pub unique_literal_type: TypeId,

    pub empty_object_type: TypeId,
    pub empty_jsx_object_type: TypeId,
    pub empty_fresh_jsx_object_type: TypeId,
    pub empty_type_literal_symbol: SemanticSymbolId,
    pub empty_type_literal_type: TypeId,
    pub unknown_empty_object_type: TypeId,
    pub unknown_union_type: TypeId,
    pub empty_generic_type: TypeId,
    pub any_function_type: TypeId,
    pub no_constraint_type: TypeId,
    pub circular_constraint_type: TypeId,
    pub resolving_default_type: TypeId,
    pub marker_super_type: TypeId,
    pub marker_sub_type: TypeId,
    pub marker_other_type: TypeId,
    pub marker_super_type_for_check: TypeId,
    pub marker_sub_type_for_check: TypeId,

    pub no_type_predicate: TypePredicateId,
    pub any_signature: SignatureId,
    pub unknown_signature: SignatureId,
    pub resolving_signature: SignatureId,
    pub silent_never_signature: SignatureId,
    pub enum_number_index_info: IndexInfoId,
    pub any_base_type_index_info: IndexInfoId,

    pub empty_string_type: TypeId,
    pub zero_type: TypeId,
    pub zero_bigint_type: TypeId,
    pub typeof_type: TypeId,

    string_literal_types: HashMap<String, TypeId>,
    number_literal_types: HashMap<NumberLiteralCacheKey, TypeId>,
    bigint_literal_types: Vec<(PseudoBigInt, TypeId)>,
    union_types: HashMap<UnionTypeCacheKey, TypeId>,
    union_of_union_types: HashMap<UnionOfUnionCacheKey, TypeId>,
    template_literal_types: HashMap<TemplateLiteralCacheKey, TypeId>,
}

impl SemanticStore<TypeRecord, TypeMapper> {
    /// Returns the already-initialized singleton set, if any.
    #[must_use]
    pub fn intrinsic_bootstrap(&self) -> Option<&IntrinsicBootstrap> {
        self.intrinsic_bootstrap.as_ref()
    }

    #[cfg(test)]
    pub(super) const fn union_cache_validation_scan_count(&self) -> usize {
        self.union_cache_validation_scans
    }

    /// Reserves one dependency-closed batch of regular/fresh literal pairs.
    ///
    /// This is the mutation barrier for literal type-node execution. Every
    /// existing cache entry and fresh/regular link is validated before any
    /// semantic record is allocated, and every fallible backing allocation is
    /// completed before the caller starts publishing query results.
    #[allow(clippy::too_many_lines)] // One atomic reservation matrix covers all literal caches.
    pub(super) fn prepare_regular_literal_types(
        &mut self,
        strings: &[String],
        numbers: &[Number],
        bigints: &[PseudoBigInt],
    ) -> Result<(), LiteralTypeCacheError> {
        self.prepare_type_query_types(strings, numbers, bigints, 0, 0)
            .map(|_| ())
    }

    /// Preflights one complete literal/union query before its first semantic
    /// write. Each union operation can allocate one denormalized origin and
    /// one normalized result; named results additionally allocate one alias
    /// shell. The conservative counts keep recursive execution infallible even
    /// when a cache hit later makes some reservations unnecessary.
    pub(super) fn prepare_type_query_types(
        &mut self,
        strings: &[String],
        numbers: &[Number],
        bigints: &[PseudoBigInt],
        union_operations: usize,
        named_union_operations: usize,
    ) -> Result<PreparedTypeQueryTypes, LiteralTypeCacheError> {
        self.prepare_type_query_types_worker(
            strings,
            numbers,
            bigints,
            union_operations,
            named_union_operations,
            UnionArrayValidation::None,
            &[],
            0,
            0,
        )
    }

    pub(super) fn prepare_type_query_types_with_global_types(
        &mut self,
        strings: &[String],
        numbers: &[Number],
        bigints: &[PseudoBigInt],
        union_operations: usize,
        named_union_operations: usize,
        global_types: &CanonicalGlobalTypes,
    ) -> Result<PreparedTypeQueryTypes, LiteralTypeCacheError> {
        self.prepare_type_query_types_worker(
            strings,
            numbers,
            bigints,
            union_operations,
            named_union_operations,
            UnionArrayValidation::GlobalTypes(global_types),
            &[],
            0,
            0,
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn prepare_type_query_types_with_pending_functions(
        &mut self,
        strings: &[String],
        numbers: &[Number],
        bigints: &[PseudoBigInt],
        union_operations: usize,
        named_union_operations: usize,
        global_types: Option<&CanonicalGlobalTypes>,
        pending_function_types: &[PendingFunctionTypeProof],
        pending_function_capacity: usize,
        additional_type_aliases: usize,
    ) -> Result<PreparedTypeQueryTypes, LiteralTypeCacheError> {
        self.prepare_type_query_types_worker(
            strings,
            numbers,
            bigints,
            union_operations,
            named_union_operations,
            UnionArrayValidation::from_global_types(global_types),
            pending_function_types,
            pending_function_capacity,
            additional_type_aliases,
        )
    }

    #[allow(clippy::too_many_arguments)] // One atomic reservation matrix carries every query budget.
    fn prepare_type_query_types_worker(
        &mut self,
        strings: &[String],
        numbers: &[Number],
        bigints: &[PseudoBigInt],
        union_operations: usize,
        named_union_operations: usize,
        array_validation: UnionArrayValidation<'_>,
        pending_function_types: &[PendingFunctionTypeProof],
        pending_function_capacity: usize,
        additional_type_aliases: usize,
    ) -> Result<PreparedTypeQueryTypes, LiteralTypeCacheError> {
        if numbers.iter().any(|value| value.is_nan())
            || bigints.iter().any(|value| {
                value.base10_value.is_empty() && value.negative
                    || !value.base10_value.is_empty()
                        && (value.base10_value.starts_with('0')
                            || !value
                                .base10_value
                                .bytes()
                                .all(|digit| digit.is_ascii_digit()))
            })
        {
            return Err(LiteralTypeCacheError::InvalidValue);
        }
        let array_targets = array_validation.targets();
        let pending_ids =
            self.proven_pending_function_types(array_targets, pending_function_types)?;
        if union_operations != 0 && self.union_cache_needs_validation {
            self.validate_union_cache(
                array_validation,
                &pending_ids.iter().copied().collect::<Vec<_>>(),
            )?;
            if pending_function_types.is_empty() {
                self.union_cache_needs_validation = false;
            }
        }
        let bootstrap = self
            .intrinsic_bootstrap
            .as_ref()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        let mut additional_types = union_operations
            .checked_mul(2)
            .ok_or(LiteralTypeCacheError::Capacity)?;
        let mut additional_strings = 0usize;
        let mut additional_numbers = 0usize;
        let mut additional_bigints = 0usize;

        for (index, value) in strings.iter().enumerate() {
            if strings[..index].contains(value) {
                continue;
            }
            if let Some(cached) = bootstrap.cached_string_literal_type(value) {
                additional_types = additional_types
                    .checked_add(self.validate_regular_literal_cache_entry(
                        cached,
                        TypeFlags::STRING_LITERAL,
                        &LiteralValue::String(value.clone()),
                    )?)
                    .ok_or(LiteralTypeCacheError::Capacity)?;
            } else {
                additional_types = additional_types
                    .checked_add(2)
                    .ok_or(LiteralTypeCacheError::Capacity)?;
                additional_strings = additional_strings
                    .checked_add(1)
                    .ok_or(LiteralTypeCacheError::Capacity)?;
            }
        }
        for (index, value) in numbers.iter().copied().enumerate() {
            if numbers[..index].iter().copied().any(|candidate| {
                NumberLiteralCacheKey::from_number(candidate)
                    == NumberLiteralCacheKey::from_number(value)
            }) {
                continue;
            }
            if let Some(cached) = bootstrap.cached_number_literal_type(value) {
                additional_types = additional_types
                    .checked_add(self.validate_regular_literal_cache_entry(
                        cached,
                        TypeFlags::NUMBER_LITERAL,
                        &LiteralValue::Number(value),
                    )?)
                    .ok_or(LiteralTypeCacheError::Capacity)?;
            } else {
                additional_types = additional_types
                    .checked_add(2)
                    .ok_or(LiteralTypeCacheError::Capacity)?;
                additional_numbers = additional_numbers
                    .checked_add(1)
                    .ok_or(LiteralTypeCacheError::Capacity)?;
            }
        }
        for (index, value) in bigints.iter().enumerate() {
            if bigints[..index].contains(value) {
                continue;
            }
            if let Some(cached) = bootstrap.cached_bigint_literal_type(value) {
                additional_types = additional_types
                    .checked_add(self.validate_regular_literal_cache_entry(
                        cached,
                        TypeFlags::BIG_INT_LITERAL,
                        &LiteralValue::BigInt(value.clone()),
                    )?)
                    .ok_or(LiteralTypeCacheError::Capacity)?;
            } else {
                additional_types = additional_types
                    .checked_add(2)
                    .ok_or(LiteralTypeCacheError::Capacity)?;
                additional_bigints = additional_bigints
                    .checked_add(1)
                    .ok_or(LiteralTypeCacheError::Capacity)?;
            }
        }

        let type_aliases = named_union_operations
            .checked_add(additional_type_aliases)
            .ok_or(LiteralTypeCacheError::Capacity)?;
        if !self.try_reserve_types(additional_types)
            || !self.try_reserve_type_aliases(type_aliases)
            || !self.try_reserve_canonical_union_creations(union_operations)
        {
            return Err(LiteralTypeCacheError::Capacity);
        }
        let Some(bootstrap) = self.intrinsic_bootstrap.as_mut() else {
            return Err(LiteralTypeCacheError::BootstrapUninitialized);
        };
        if bootstrap
            .string_literal_types
            .try_reserve(additional_strings)
            .is_err()
            || bootstrap
                .number_literal_types
                .try_reserve(additional_numbers)
                .is_err()
            || bootstrap
                .bigint_literal_types
                .try_reserve(additional_bigints)
                .is_err()
            || bootstrap.union_types.try_reserve(union_operations).is_err()
            || bootstrap
                .union_of_union_types
                .try_reserve(union_operations)
                .is_err()
        {
            return Err(LiteralTypeCacheError::Capacity);
        }
        let mut pending = HashSet::new();
        pending
            .try_reserve(pending_function_capacity)
            .map_err(|_| LiteralTypeCacheError::Capacity)?;
        pending.extend(pending_ids);
        if pending.len() != pending_function_types.len()
            || pending
                .iter()
                .any(|type_| self.type_payload(*type_).is_none())
        {
            return Err(LiteralTypeCacheError::InvalidPreparedQuery);
        }
        Ok(PreparedTypeQueryTypes {
            store: self.id(),
            array_targets,
            union_operations_remaining: union_operations,
            named_union_operations_remaining: named_union_operations,
            pending_function_types: pending,
            canonical_tuple_types: HashMap::new(),
        })
    }

    pub(super) fn regular_string_literal_type(
        &mut self,
        value: String,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        self.prepare_regular_literal_types(std::slice::from_ref(&value), &[], &[])?;
        if let Some(cached) = self
            .intrinsic_bootstrap
            .as_ref()
            .and_then(|bootstrap| bootstrap.cached_string_literal_type(&value))
        {
            return self.ensure_fresh_literal(cached);
        }
        let regular = self.allocate_regular_literal(
            TypeFlags::STRING_LITERAL,
            LiteralValue::String(value.clone()),
        )?;
        let bootstrap = self
            .intrinsic_bootstrap
            .as_mut()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        let previous = bootstrap.string_literal_types.insert(value, regular);
        if let Some(previous) = previous {
            return Err(LiteralTypeCacheError::InvalidCachedLiteral(previous));
        }
        Ok(regular)
    }

    pub(super) fn regular_number_literal_type(
        &mut self,
        value: Number,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        self.prepare_regular_literal_types(&[], std::slice::from_ref(&value), &[])?;
        if let Some(cached) = self
            .intrinsic_bootstrap
            .as_ref()
            .and_then(|bootstrap| bootstrap.cached_number_literal_type(value))
        {
            return self.ensure_fresh_literal(cached);
        }
        let Some(key) = NumberLiteralCacheKey::from_number(value) else {
            return Err(LiteralTypeCacheError::InvalidValue);
        };
        let regular =
            self.allocate_regular_literal(TypeFlags::NUMBER_LITERAL, LiteralValue::Number(value))?;
        let bootstrap = self
            .intrinsic_bootstrap
            .as_mut()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        let previous = bootstrap.number_literal_types.insert(key, regular);
        if let Some(previous) = previous {
            return Err(LiteralTypeCacheError::InvalidCachedLiteral(previous));
        }
        Ok(regular)
    }

    pub(super) fn regular_bigint_literal_type(
        &mut self,
        value: PseudoBigInt,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        self.prepare_regular_literal_types(&[], &[], std::slice::from_ref(&value))?;
        if let Some(cached) = self
            .intrinsic_bootstrap
            .as_ref()
            .and_then(|bootstrap| bootstrap.cached_bigint_literal_type(&value))
        {
            return self.ensure_fresh_literal(cached);
        }
        let regular = self.allocate_regular_literal(
            TypeFlags::BIG_INT_LITERAL,
            LiteralValue::BigInt(value.clone()),
        )?;
        let bootstrap = self
            .intrinsic_bootstrap
            .as_mut()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        bootstrap.bigint_literal_types.push((value, regular));
        Ok(regular)
    }

    /// Returns the validated fresh half of one regular literal pair.
    ///
    /// Expression checking calls this only after one of the regular literal
    /// interning entry points above. Keeping the validation in the store makes
    /// a malformed global literal cache a typed failure instead of allowing a
    /// foreign or stale fresh identity to escape.
    pub(super) fn fresh_type_of_literal_type(
        &self,
        regular: TypeId,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        let Some(record) = self.type_payload(regular) else {
            return Err(LiteralTypeCacheError::InvalidCachedLiteral(regular));
        };
        let TypeData::Literal(literal) = record.data() else {
            return Err(LiteralTypeCacheError::InvalidCachedLiteral(regular));
        };
        if record.flags().intersects(TypeFlags::ENUM_LIKE) {
            validate_enum_type_union_constituent(self, regular)
                .ok_or(LiteralTypeCacheError::InvalidCachedLiteral(regular))?;
            return (literal.regular_type == regular)
                .then_some(literal.fresh_type)
                .flatten()
                .ok_or(LiteralTypeCacheError::InvalidCachedLiteral(regular));
        }
        if literal.regular_type != regular
            || self.validate_regular_literal_cache_entry(regular, record.flags(), &literal.value)?
                != 0
        {
            return Err(LiteralTypeCacheError::InvalidCachedLiteral(regular));
        }
        literal
            .fresh_type
            .ok_or(LiteralTypeCacheError::InvalidCachedLiteral(regular))
    }

    fn validate_regular_literal_cache_entry(
        &self,
        regular: TypeId,
        expected_flags: TypeFlags,
        expected_value: &LiteralValue,
    ) -> Result<usize, LiteralTypeCacheError> {
        let Some(regular_record) = self.type_payload(regular) else {
            return Err(LiteralTypeCacheError::InvalidCachedLiteral(regular));
        };
        let TypeData::Literal(regular_data) = regular_record.data() else {
            return Err(LiteralTypeCacheError::InvalidCachedLiteral(regular));
        };
        if regular_record.flags() != expected_flags
            || regular_record.object_flags() != ObjectFlags::NONE
            || regular_record.symbol().is_some()
            || regular_record.alias().is_some()
            || &regular_data.value != expected_value
            || regular_data.regular_type != regular
        {
            return Err(LiteralTypeCacheError::InvalidCachedLiteral(regular));
        }
        let Some(fresh) = regular_data.fresh_type else {
            return Ok(1);
        };
        let Some(fresh_record) = self.type_payload(fresh) else {
            return Err(LiteralTypeCacheError::InvalidCachedLiteral(regular));
        };
        let TypeData::Literal(fresh_data) = fresh_record.data() else {
            return Err(LiteralTypeCacheError::InvalidCachedLiteral(regular));
        };
        if fresh == regular
            || fresh_record.flags() != expected_flags
            || fresh_record.object_flags() != ObjectFlags::NONE
            || fresh_record.symbol().is_some()
            || fresh_record.alias().is_some()
            || &fresh_data.value != expected_value
            || fresh_data.fresh_type != Some(fresh)
            || fresh_data.regular_type != regular
        {
            return Err(LiteralTypeCacheError::InvalidCachedLiteral(regular));
        }
        Ok(0)
    }

    fn allocate_regular_literal(
        &mut self,
        flags: TypeFlags,
        value: LiteralValue,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        let Some(regular) = self.alloc_literal_type(flags, value, RegularLiteralLink::SelfType)
        else {
            return Err(LiteralTypeCacheError::InvalidValue);
        };
        self.ensure_fresh_literal(regular)
    }

    fn ensure_fresh_literal(&mut self, regular: TypeId) -> Result<TypeId, LiteralTypeCacheError> {
        let (flags, value, fresh) = {
            let Some(record) = self.type_payload(regular) else {
                return Err(LiteralTypeCacheError::InvalidCachedLiteral(regular));
            };
            let TypeData::Literal(data) = record.data() else {
                return Err(LiteralTypeCacheError::InvalidCachedLiteral(regular));
            };
            (record.flags(), data.value.clone(), data.fresh_type)
        };
        if fresh.is_some() {
            return Ok(regular);
        }
        let Some(fresh) = self.alloc_literal_type(flags, value, RegularLiteralLink::Type(regular))
        else {
            return Err(LiteralTypeCacheError::InvalidCachedLiteral(regular));
        };
        let cache_was_dirty = self.union_cache_needs_validation;
        if !self.set_literal_links(fresh, Some(fresh), regular)
            || !self.set_literal_links(regular, Some(fresh), regular)
        {
            return Err(LiteralTypeCacheError::InvalidCachedLiteral(regular));
        }
        self.union_cache_needs_validation = cache_was_dirty;
        Ok(regular)
    }

    fn validate_union_cache(
        &mut self,
        array_validation: UnionArrayValidation<'_>,
        pending_function_types: &[TypeId],
    ) -> Result<(), LiteralTypeCacheError> {
        #[cfg(test)]
        {
            self.union_cache_validation_scans = self
                .union_cache_validation_scans
                .checked_add(1)
                .ok_or(LiteralTypeCacheError::Capacity)?;
        }
        let (unions, unions_of_unions) = {
            let bootstrap = self
                .intrinsic_bootstrap
                .as_ref()
                .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
            (
                bootstrap
                    .union_types
                    .iter()
                    .map(|(key, union)| (key.clone(), *union))
                    .collect::<Vec<_>>(),
                bootstrap
                    .union_of_union_types
                    .iter()
                    .map(|(key, result)| (key.clone(), *result))
                    .collect::<Vec<_>>(),
            )
        };
        let allowed_pending = pending_function_types
            .iter()
            .copied()
            .collect::<HashSet<_>>();
        for (key, union) in unions {
            self.validate_union_cache_entry(
                &key,
                union,
                array_validation,
                &mut HashSet::new(),
                &allowed_pending,
            )?;
        }
        for (key, result) in unions_of_unions {
            self.validate_union_of_union_cache_entry(
                key,
                result,
                array_validation,
                &allowed_pending,
            )?;
        }
        Ok(())
    }

    fn validate_union_cache_entry(
        &self,
        key: &UnionTypeCacheKey,
        union: TypeId,
        array_validation: UnionArrayValidation<'_>,
        array_visited: &mut HashSet<TypeId>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        self.validate_union_cache_entry_metadata(key, union)?;
        let TypeData::Union(data) = self
            .type_payload(union)
            .expect("validated union metadata")
            .data()
        else {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        };
        let mut visiting = HashSet::new();
        for constituent in &data.union.types {
            self.validate_union_constituent_worker(
                *constituent,
                array_validation,
                &mut visiting,
                array_visited,
                allowed_pending,
            )?;
        }
        if let Some(alias) = key.alias.as_ref() {
            for argument in &alias.type_arguments {
                self.validate_cached_array_capability_worker(
                    *argument,
                    array_validation,
                    array_visited,
                    allowed_pending,
                )?;
            }
        }
        Ok(())
    }

    fn validate_union_cache_entry_metadata(
        &self,
        key: &UnionTypeCacheKey,
        union: TypeId,
    ) -> Result<(), LiteralTypeCacheError> {
        self.validate_union_structure(union)?;
        let record = self
            .type_payload(union)
            .ok_or(LiteralTypeCacheError::InvalidCachedUnion(union))?;
        let TypeData::Union(data) = record.data() else {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        };
        if data.union.types != key.types
            || self.checked_union_alias(union, record.alias())? != key.alias
            || !self.union_origin_matches(union, data.origin, key.origin.as_ref())
        {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        }
        Ok(())
    }

    /// Checks a cached union without traversing unused member types.
    /// Query providers validate each member they consume.
    pub(super) fn validate_union_query_metadata(
        &self,
        union: TypeId,
    ) -> Result<(), LiteralTypeCacheError> {
        if self
            .intrinsic_bootstrap
            .as_ref()
            .is_some_and(|bootstrap| union == bootstrap.boolean_type)
        {
            return self.validate_union_constituent(union);
        }
        let record = self
            .type_payload(union)
            .ok_or(LiteralTypeCacheError::InvalidCachedUnion(union))?;
        let TypeData::Union(data) = record.data() else {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        };
        let key = self.validated_union_cache_key(union, record, data)?;
        self.validate_union_cache_entry_metadata(&key, union)
    }

    fn validate_union_of_union_cache_entry(
        &mut self,
        key: UnionOfUnionCacheKey,
        result: TypeId,
        array_validation: UnionArrayValidation<'_>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        if !self.valid_union_alias_key(key.alias.as_ref()) {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(result));
        }
        for candidate in [key.first, key.second, result] {
            self.validate_union_constituent_worker(
                candidate,
                array_validation,
                &mut HashSet::new(),
                &mut HashSet::new(),
                allowed_pending,
            )?;
        }
        let expected = match self.plan_union_type(
            &[key.first, key.second],
            key.reduction,
            key.alias,
            array_validation.global_types(),
            true,
        )? {
            UnionPlan::Existing(expected) => expected,
            UnionPlan::Union {
                types,
                object_flags: _,
                alias,
                origin,
            } => {
                let expected_key = UnionTypeCacheKey {
                    types,
                    origin: origin.map(|origin| match origin {
                        UnionOriginPlan::DenormalizedUnion(types) => {
                            UnionOriginCacheKey::DenormalizedUnion(types)
                        }
                        UnionOriginPlan::ExistingIndex(index) => UnionOriginCacheKey::Index(index),
                    }),
                    alias,
                };
                let expected = self
                    .intrinsic_bootstrap
                    .as_ref()
                    .and_then(|bootstrap| bootstrap.union_types.get(&expected_key))
                    .copied()
                    .ok_or(LiteralTypeCacheError::InvalidCachedUnion(result))?;
                self.validate_union_cache_entry(
                    &expected_key,
                    expected,
                    array_validation,
                    &mut HashSet::new(),
                    allowed_pending,
                )?;
                expected
            }
        };
        if result != expected {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(result));
        }
        Ok(())
    }

    fn valid_union_alias_key(&self, alias: Option<&UnionAliasCacheKey>) -> bool {
        alias.is_none_or(|alias| {
            self.valid_union_alias_symbol(alias.symbol)
                && self
                    .type_alias_links(alias.symbol)
                    .and_then(|links| links.type_parameters.as_deref())
                    .is_none_or(|parameters| parameters.len() == alias.type_arguments.len())
                && alias
                    .type_arguments
                    .iter()
                    .all(|argument| self.type_payload(*argument).is_some())
        })
    }

    fn valid_union_alias_symbol(&self, symbol: SemanticSymbolId) -> bool {
        self.get_merged_symbol(symbol) == Some(symbol)
            && self.symbol(symbol).is_some_and(|symbol| {
                let flags = symbol.flags();
                flags.contains(SymbolFlags::TYPE_ALIAS)
                    && !(flags.contains(SymbolFlags::ALIAS)
                        && flags.without(SymbolFlags::ALIAS) != SymbolFlags::NONE)
            })
    }

    fn checked_union_alias(
        &self,
        union: TypeId,
        alias: Option<TypeAliasId>,
    ) -> Result<Option<UnionAliasCacheKey>, LiteralTypeCacheError> {
        let Some(alias) = alias else {
            return Ok(None);
        };
        let alias = self
            .type_alias(alias)
            .ok_or(LiteralTypeCacheError::InvalidCachedUnion(union))?;
        let symbol = alias
            .symbol()
            .filter(|symbol| self.valid_union_alias_symbol(*symbol))
            .ok_or(LiteralTypeCacheError::InvalidCachedUnion(union))?;
        let key = UnionAliasCacheKey::new(symbol, alias.type_arguments().unwrap_or_default());
        if !self.valid_union_alias_key(Some(&key)) {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        }
        Ok(Some(key))
    }

    fn union_alias_source_owners(
        &self,
        alias: &UnionAliasCacheKey,
    ) -> Result<Vec<UnionAliasSourceOwner>, LiteralTypeCacheError> {
        let symbols = std::iter::once(alias.symbol).chain(alias.type_arguments.iter().filter_map(
            |argument| {
                let record = self.type_payload(*argument)?;
                if matches!(record.data(), TypeData::TypeParameter(_)) {
                    record.symbol()
                } else {
                    None
                }
            },
        ));
        symbols
            .map(|symbol| {
                let owner = self
                    .symbol(symbol)
                    .ok_or(LiteralTypeCacheError::InvalidUnionAlias(alias.symbol))?;
                Ok(UnionAliasSourceOwner {
                    symbol,
                    flags: owner.flags(),
                    parent: owner.parent(),
                    declarations: owner.declarations().map(<[NodeRef]>::to_vec),
                })
            })
            .collect()
    }

    fn validate_union_creation(
        &self,
        union: TypeId,
        record: &TypeRecord,
        data: &super::type_records::UnionTypeData,
    ) -> Result<(), LiteralTypeCacheError> {
        let alias = self.checked_union_alias(union, record.alias())?;
        let Some(proof) = self.canonical_union_creation(union) else {
            return if alias.is_none() && data.origin.is_none() {
                Ok(())
            } else {
                Err(LiteralTypeCacheError::InvalidCachedUnion(union))
            };
        };
        if proof.key.alias != alias
            || proof.key.types != data.union.types
            || !self.union_origin_matches(union, data.origin, proof.key.origin.as_ref())
            || proof.owners.iter().any(|expected| {
                self.symbol(expected.symbol).is_none_or(|owner| {
                    self.get_merged_symbol(expected.symbol) != Some(expected.symbol)
                        || owner.flags() != expected.flags
                        || owner.parent() != expected.parent
                        || owner.declarations() != expected.declarations.as_deref()
                })
            })
        {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        }
        Ok(())
    }

    fn union_origin_matches(
        &self,
        union: TypeId,
        origin: Option<TypeId>,
        expected: Option<&UnionOriginCacheKey>,
    ) -> bool {
        match (origin, expected) {
            (None, None) => true,
            (Some(origin), Some(UnionOriginCacheKey::DenormalizedUnion(expected))) => {
                let Some(record) = self.type_payload(origin) else {
                    return false;
                };
                let TypeData::Union(data) = record.data() else {
                    return false;
                };
                record.flags() == TypeFlags::UNION
                    && Self::valid_union_lazy_object_flags(record.object_flags())
                    && record.symbol().is_none()
                    && record.alias().is_none()
                    && data.origin.is_none()
                    && data.union.types == *expected
            }
            (Some(origin), Some(UnionOriginCacheKey::Index(expected))) => origin == *expected
                && self.valid_index_union_origin(origin)
                && self.type_payload(origin).is_some_and(
                    |record| matches!(record.data(), TypeData::Index(data) if data.target != union),
                ),
            _ => false,
        }
    }

    fn valid_index_union_origin(&self, origin: TypeId) -> bool {
        let Some(record) = self.type_payload(origin) else {
            return false;
        };
        let TypeData::Index(data) = record.data() else {
            return false;
        };
        let Some(target) = self.type_payload(data.target) else {
            return false;
        };
        record.flags() == TypeFlags::INDEX
            && record.object_flags() == ObjectFlags::NONE
            && record.symbol().is_none()
            && record.alias().is_none()
            && data.index_flags == IndexFlags::NONE
            && target.flags() == TypeFlags::OBJECT
            && (target
                .object_flags()
                .intersects(ObjectFlags::CLASS_OR_INTERFACE | ObjectFlags::REFERENCE)
                || target.alias().is_some())
    }

    fn union_types_are_strictly_sorted(&self, types: &[TypeId]) -> bool {
        types.windows(2).all(|pair| {
            self.compare_union_types(pair[0], pair[1])
                .is_ok_and(|ordering| ordering == Ordering::Less)
        })
    }

    fn valid_union_lazy_object_flags(flags: ObjectFlags) -> bool {
        Self::valid_union_cache_lazy_object_flags(flags)
    }

    fn expected_union_type_flags(
        &self,
        types: &[TypeId],
    ) -> Result<TypeFlags, LiteralTypeCacheError> {
        let mut flags = TypeFlags::UNION;
        if types.len() == 2
            && types.iter().all(|constituent| {
                self.type_payload(*constituent)
                    .is_some_and(|record| record.flags() == TypeFlags::BOOLEAN_LITERAL)
            })
        {
            flags |= TypeFlags::BOOLEAN;
        }
        if types
            .iter()
            .any(|constituent| self.type_payload(*constituent).is_none())
        {
            return Err(LiteralTypeCacheError::InvalidValue);
        }
        Ok(flags)
    }

    fn expected_union_immutable_object_flags(
        &self,
        types: &[TypeId],
    ) -> Result<ObjectFlags, LiteralTypeCacheError> {
        let mut includes = TypeFlags::NONE;
        let mut propagating = ObjectFlags::NONE;
        for type_ in types {
            let record = self
                .type_payload(*type_)
                .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(*type_))?;
            includes |= record.flags() & TypeFlags::INCLUDES_MASK;
            if record.flags().intersects(TypeFlags::INSTANTIABLE) {
                includes |= TypeFlags::INCLUDES_INSTANTIABLE;
            }
            if !record.flags().intersects(TypeFlags::NULLABLE) {
                propagating |= record.object_flags();
            }
        }
        let mut expected = if includes.intersects(TypeFlags::NOT_PRIMITIVE_UNION) {
            ObjectFlags::NONE
        } else {
            ObjectFlags::PRIMITIVE_UNION
        };
        if includes.intersects(TypeFlags::INTERSECTION) {
            expected |= ObjectFlags::CONTAINS_INTERSECTIONS;
        }
        Ok(expected | propagating & ObjectFlags::PROPAGATING_FLAGS)
    }

    fn union_object_flags_match(
        &self,
        types: &[TypeId],
        actual: ObjectFlags,
    ) -> Result<bool, LiteralTypeCacheError> {
        let immutable_mask = ObjectFlags::PRIMITIVE_UNION
            | ObjectFlags::CONTAINS_INTERSECTIONS
            | ObjectFlags::PROPAGATING_FLAGS;
        let expected = self.expected_union_immutable_object_flags(types)?;
        Ok(actual & immutable_mask == expected
            && Self::valid_union_lazy_object_flags(actual & !immutable_mask))
    }

    fn validate_union_origin_structure(
        &self,
        union: TypeId,
        origin: TypeId,
    ) -> Result<(), LiteralTypeCacheError> {
        let Some(record) = self.type_payload(origin) else {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        };
        if origin == union {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        }
        match record.data() {
            TypeData::Union(data)
                if record.flags() == TypeFlags::UNION
                    && Self::valid_union_lazy_object_flags(record.object_flags())
                    && record.symbol().is_none()
                    && record.alias().is_none()
                    && data.origin.is_none()
                    && !data.union.types.is_empty()
                    && data
                        .union
                        .types
                        .iter()
                        .all(|constituent| self.type_payload(*constituent).is_some())
                    && self.union_types_are_strictly_sorted(&data.union.types) =>
            {
                Ok(())
            }
            TypeData::Index(data)
                if data.target != union && self.valid_index_union_origin(origin) =>
            {
                Ok(())
            }
            _ => Err(LiteralTypeCacheError::InvalidCachedUnion(union)),
        }
    }

    fn validate_union_structure(&self, union: TypeId) -> Result<(), LiteralTypeCacheError> {
        let Some(record) = self.type_payload(union) else {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        };
        let TypeData::Union(data) = record.data() else {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        };
        if data.union.types.len() < 2
            || record.symbol().is_some()
            || data
                .union
                .types
                .iter()
                .any(|constituent| self.type_payload(*constituent).is_none())
            || record.flags() != self.expected_union_type_flags(&data.union.types)?
            || !self.union_object_flags_match(&data.union.types, record.object_flags())?
            || !self.union_types_are_strictly_sorted(&data.union.types)
        {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        }
        self.validate_union_creation(union, record, data)?;
        if let Some(origin) = data.origin {
            self.validate_union_origin_structure(union, origin)?;
        }
        Ok(())
    }

    /// Validates an anonymous union's exact cache identity without following its constituents.
    /// The caller must validate each constituent independently.
    pub(super) fn validate_canonical_union_metadata(
        &self,
        union: TypeId,
        expected: &[TypeId],
    ) -> Result<(), LiteralTypeCacheError> {
        self.validate_union_structure(union)?;
        let record = self
            .type_payload(union)
            .ok_or(LiteralTypeCacheError::InvalidCachedUnion(union))?;
        let TypeData::Union(data) = record.data() else {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        };
        if record.alias().is_some()
            || data.origin.is_some()
            || data.union.types != expected
            || self
                .intrinsic_bootstrap
                .as_ref()
                .and_then(|bootstrap| bootstrap.cached_union_type(expected))
                != Some(union)
        {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        }
        Ok(())
    }

    /// Validates the optional wrapper while leaving annotation graph validation to its owner.
    pub(super) fn validate_optional_parameter_type_metadata(
        &self,
        base: TypeId,
        resolved: TypeId,
    ) -> Result<(), LiteralTypeCacheError> {
        let invalid = || LiteralTypeCacheError::InvalidCachedUnion(resolved);
        let bootstrap = self
            .intrinsic_bootstrap
            .as_ref()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        if bootstrap.cached_optional_parameter_type(base) != Some(resolved) {
            return Err(invalid());
        }
        let base_record = self.type_payload(base).ok_or_else(invalid)?;
        let mut expected = match base_record.data() {
            TypeData::Union(data) => data.union.types.clone(),
            _ if base_record.flags().intersects(TypeFlags::ANY_OR_UNKNOWN) => {
                if base != resolved {
                    return Err(invalid());
                }
                return self.validate_union_constituent(base);
            }
            _ if base_record.flags().intersects(TypeFlags::NEVER) => Vec::new(),
            _ => vec![base],
        };
        expected.push(bootstrap.undefined_type);
        expected.retain(|type_| *type_ != bootstrap.missing_type);
        expected.sort_unstable();
        expected.dedup();
        match expected.as_slice() {
            [single] if *single == resolved => {}
            _ => {
                let Some(TypeData::Union(data)) = self.type_payload(resolved).map(TypeRecord::data)
                else {
                    return Err(invalid());
                };
                if data.union.types != expected {
                    return Err(invalid());
                }
            }
        }
        for type_ in [base, resolved] {
            if matches!(
                self.type_payload(type_).map(TypeRecord::data),
                Some(TypeData::Union(_))
            ) {
                let mut found = false;
                for (key, value) in &bootstrap.union_types {
                    if *value == type_ {
                        self.validate_union_cache_entry_metadata(key, type_)?;
                        found = true;
                    }
                }
                if !found {
                    return Err(invalid());
                }
            }
        }
        self.validate_union_constituent(bootstrap.undefined_type)
    }

    pub(super) fn validate_union_constituent(
        &self,
        type_: TypeId,
    ) -> Result<(), LiteralTypeCacheError> {
        self.validate_union_constituent_worker(
            type_,
            UnionArrayValidation::None,
            &mut HashSet::new(),
            &mut HashSet::new(),
            &HashSet::new(),
        )
    }

    pub(super) fn validate_union_constituent_with_global_types(
        &self,
        global_types: &CanonicalGlobalTypes,
        type_: TypeId,
    ) -> Result<(), LiteralTypeCacheError> {
        self.validate_union_constituent_worker(
            type_,
            UnionArrayValidation::GlobalTypes(global_types),
            &mut HashSet::new(),
            &mut HashSet::new(),
            &HashSet::new(),
        )
    }

    pub(super) fn validate_union_constituent_with_array_targets(
        &self,
        targets: super::array_types::CanonicalArrayTargets,
        type_: TypeId,
    ) -> Result<(), LiteralTypeCacheError> {
        self.validate_union_constituent_worker(
            type_,
            UnionArrayValidation::Targets(targets),
            &mut HashSet::new(),
            &mut HashSet::new(),
            &HashSet::new(),
        )
    }

    pub(super) fn validate_cached_union_result(
        &self,
        type_: TypeId,
        expected_alias: Option<SemanticSymbolId>,
    ) -> Result<(), LiteralTypeCacheError> {
        self.validate_cached_union_result_worker(
            type_,
            expected_alias,
            UnionArrayValidation::None,
            &HashSet::new(),
        )
    }

    pub(super) fn validate_union_alias_identity(
        &self,
        type_: TypeId,
        symbol: SemanticSymbolId,
        arguments: &[TypeId],
    ) -> Result<(), LiteralTypeCacheError> {
        let record = self
            .type_payload(type_)
            .ok_or(LiteralTypeCacheError::InvalidCachedUnion(type_))?;
        // Union reduction returns the remaining type without a new alias.
        if matches!(record.data(), TypeData::Union(_)) {
            self.validate_union_structure(type_)?;
            if self.checked_union_alias(type_, record.alias())?
                != Some(UnionAliasCacheKey::new(symbol, arguments))
            {
                return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
            }
        }
        Ok(())
    }

    pub(super) fn validate_cached_union_result_with_array_targets(
        &self,
        targets: super::array_types::CanonicalArrayTargets,
        type_: TypeId,
        expected_alias: Option<SemanticSymbolId>,
    ) -> Result<(), LiteralTypeCacheError> {
        self.validate_cached_union_result_worker(
            type_,
            expected_alias,
            UnionArrayValidation::Targets(targets),
            &HashSet::new(),
        )
    }

    pub(super) fn validate_cached_union_result_with_pending_functions(
        &self,
        targets: Option<CanonicalArrayTargets>,
        type_: TypeId,
        expected_alias: Option<SemanticSymbolId>,
        pending_function_types: &[PendingFunctionTypeProof],
    ) -> Result<(), LiteralTypeCacheError> {
        let pending_function_types =
            self.proven_pending_function_types(targets, pending_function_types)?;
        self.validate_cached_union_result_worker(
            type_,
            expected_alias,
            targets.map_or(UnionArrayValidation::None, UnionArrayValidation::Targets),
            &pending_function_types,
        )
    }

    pub(super) fn validate_optional_union_of_union_result(
        &self,
        targets: Option<CanonicalArrayTargets>,
        base: TypeId,
        undefined: TypeId,
        resolved: TypeId,
    ) -> Result<(), LiteralTypeCacheError> {
        let (first, second) = if base < undefined {
            (base, undefined)
        } else {
            (undefined, base)
        };
        let key = UnionOfUnionCacheKey {
            first,
            second,
            reduction: UnionReduction::Literal,
            alias: None,
        };
        if self
            .intrinsic_bootstrap
            .as_ref()
            .and_then(|bootstrap| bootstrap.union_of_union_types.get(&key))
            .copied()
            != Some(resolved)
        {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(resolved));
        }
        let array_validation =
            targets.map_or(UnionArrayValidation::None, UnionArrayValidation::Targets);
        self.validate_union_constituent_worker(
            base,
            array_validation,
            &mut HashSet::new(),
            &mut HashSet::new(),
            &HashSet::new(),
        )?;
        self.validate_union_constituent_worker(
            undefined,
            array_validation,
            &mut HashSet::new(),
            &mut HashSet::new(),
            &HashSet::new(),
        )?;
        self.validate_cached_union_result_worker(resolved, None, array_validation, &HashSet::new())
    }

    /// Validates every cached canonical-array edge reachable from `type_`
    /// without granting an array capability. Unrelated semantic families are
    /// opaque; a reference to the registered global `Array` or
    /// `ReadonlyArray` target fails closed.
    pub(super) fn validate_cached_array_capability(
        &self,
        type_: TypeId,
    ) -> Result<(), LiteralTypeCacheError> {
        self.validate_cached_array_capability_worker(
            type_,
            UnionArrayValidation::None,
            &mut HashSet::new(),
            &HashSet::new(),
        )
    }

    /// Validates every cached canonical-array edge reachable from `type_`
    /// against the explicitly installed targets. This is deliberately a
    /// selective graph walk: generic reference arguments, union constituents,
    /// and proven declared-property types are followed, while unrelated
    /// leaves stay outside the array capability boundary.
    pub(super) fn validate_cached_array_capability_with_array_targets(
        &self,
        targets: CanonicalArrayTargets,
        type_: TypeId,
    ) -> Result<(), LiteralTypeCacheError> {
        self.validate_cached_array_capability_worker(
            type_,
            UnionArrayValidation::Targets(targets),
            &mut HashSet::new(),
            &HashSet::new(),
        )
    }

    pub(super) fn validate_cached_array_capability_with_pending_functions(
        &self,
        targets: Option<CanonicalArrayTargets>,
        type_: TypeId,
        pending_function_types: &[PendingFunctionTypeProof],
    ) -> Result<(), LiteralTypeCacheError> {
        let pending_function_types =
            self.proven_pending_function_types(targets, pending_function_types)?;
        self.validate_cached_array_capability_worker(
            type_,
            targets.map_or(UnionArrayValidation::None, UnionArrayValidation::Targets),
            &mut HashSet::new(),
            &pending_function_types,
        )
    }

    pub(super) fn validate_cached_array_capability_prepared(
        &self,
        type_: TypeId,
        global_types: Option<&CanonicalGlobalTypes>,
        prepared: &PreparedTypeQueryTypes,
    ) -> Result<(), LiteralTypeCacheError> {
        let targets = global_types.map(CanonicalArrayTargets::from_global_types);
        if prepared.store != self.id() || prepared.array_targets != targets {
            return Err(LiteralTypeCacheError::InvalidPreparedQuery);
        }
        self.validate_cached_array_capability_worker(
            type_,
            targets.map_or(UnionArrayValidation::None, UnionArrayValidation::Targets),
            &mut HashSet::new(),
            &prepared.pending_function_types,
        )
    }

    fn proven_pending_function_types(
        &self,
        targets: Option<CanonicalArrayTargets>,
        proofs: &[PendingFunctionTypeProof],
    ) -> Result<HashSet<TypeId>, LiteralTypeCacheError> {
        let mut pending = HashSet::with_capacity(proofs.len());
        for proof in proofs {
            let type_ = proof.type_();
            if proof.store() != self.id()
                || proof.array_targets() != targets
                || !functions::validate_pending_function_type_proof(self, proof)
                || !pending.insert(type_)
            {
                return Err(LiteralTypeCacheError::InvalidPreparedQuery);
            }
        }
        Ok(pending)
    }

    fn validate_cached_union_result_worker(
        &self,
        type_: TypeId,
        expected_alias: Option<SemanticSymbolId>,
        array_validation: UnionArrayValidation<'_>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        self.validate_union_constituent_worker(
            type_,
            array_validation,
            &mut HashSet::new(),
            &mut HashSet::new(),
            allowed_pending,
        )?;
        if let Some(expected_alias) = expected_alias
            && let Some(record) = self.type_payload(type_)
            && matches!(record.data(), TypeData::Union(_))
            && self
                .checked_union_alias(type_, record.alias())?
                .map(|alias| alias.symbol)
                != Some(expected_alias)
        {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
        }
        Ok(())
    }

    fn validate_supported_intrinsic(
        &self,
        type_: TypeId,
        record: &TypeRecord,
        intrinsic_name: &str,
    ) -> Result<(), LiteralTypeCacheError> {
        let bootstrap = self
            .intrinsic_bootstrap
            .as_ref()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        let expected = [
            (bootstrap.any_type, TypeFlags::ANY, "any", ObjectFlags::NONE),
            (
                bootstrap.wildcard_type,
                TypeFlags::ANY,
                "any",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.error_type,
                TypeFlags::ANY,
                "error",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.intrinsic_marker_type,
                TypeFlags::ANY,
                "intrinsic",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.unknown_type,
                TypeFlags::UNKNOWN,
                "unknown",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.undefined_type,
                TypeFlags::UNDEFINED,
                "undefined",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.undefined_widening_type,
                TypeFlags::UNDEFINED,
                "undefined",
                if bootstrap.undefined_widening_type == bootstrap.undefined_type {
                    ObjectFlags::NONE
                } else {
                    ObjectFlags::CONTAINS_WIDENING_TYPE
                },
            ),
            (
                bootstrap.null_type,
                TypeFlags::NULL,
                "null",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.null_widening_type,
                TypeFlags::NULL,
                "null",
                if bootstrap.null_widening_type == bootstrap.null_type {
                    ObjectFlags::NONE
                } else {
                    ObjectFlags::CONTAINS_WIDENING_TYPE
                },
            ),
            (
                bootstrap.string_type,
                TypeFlags::STRING,
                "string",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.number_type,
                TypeFlags::NUMBER,
                "number",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.bigint_type,
                TypeFlags::BIG_INT,
                "bigint",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.es_symbol_type,
                TypeFlags::ES_SYMBOL,
                "symbol",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.void_type,
                TypeFlags::VOID,
                "void",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.never_type,
                TypeFlags::NEVER,
                "never",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.non_primitive_type,
                TypeFlags::NON_PRIMITIVE,
                "object",
                ObjectFlags::NONE,
            ),
        ]
        .into_iter()
        .find_map(|(candidate, flags, name, object_flags)| {
            (candidate == type_).then_some((flags, name, object_flags))
        })
        .or_else(|| {
            (type_ == bootstrap.missing_type).then_some((
                TypeFlags::UNDEFINED,
                "undefined",
                ObjectFlags::NONE,
            ))
        });
        if expected != Some((record.flags(), intrinsic_name, record.object_flags()))
            || record.symbol().is_some()
            || record.alias().is_some()
        {
            return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
        }
        Ok(())
    }

    fn validate_supported_literal_identity(
        &self,
        type_: TypeId,
        regular: TypeId,
        fresh: Option<TypeId>,
        value: &LiteralValue,
    ) -> Result<(), LiteralTypeCacheError> {
        let bootstrap = self
            .intrinsic_bootstrap
            .as_ref()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        let (canonical_regular, canonical_fresh) = match value {
            LiteralValue::String(value) => (bootstrap.cached_string_literal_type(value), None),
            LiteralValue::Number(value) => (bootstrap.cached_number_literal_type(*value), None),
            LiteralValue::BigInt(value) => (bootstrap.cached_bigint_literal_type(value), None),
            LiteralValue::Boolean(false) => (
                Some(bootstrap.regular_false_type),
                Some(bootstrap.false_type),
            ),
            LiteralValue::Boolean(true) => {
                (Some(bootstrap.regular_true_type), Some(bootstrap.true_type))
            }
            LiteralValue::ComputedEnum => (None, None),
        };
        if canonical_regular != Some(regular)
            || canonical_fresh.is_some_and(|canonical| fresh != Some(canonical))
            || type_ != regular && fresh != Some(type_)
        {
            return Err(LiteralTypeCacheError::InvalidCachedLiteral(type_));
        }
        Ok(())
    }

    fn validate_supported_union_cache_identity(
        &self,
        union: TypeId,
        record: &TypeRecord,
        data: &super::type_records::UnionTypeData,
        array_validation: UnionArrayValidation<'_>,
        array_visited: &mut HashSet<TypeId>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        let key = self.validated_union_cache_key(union, record, data)?;
        self.validate_union_cache_entry(
            &key,
            union,
            array_validation,
            array_visited,
            allowed_pending,
        )
    }

    fn validated_union_cache_key(
        &self,
        union: TypeId,
        record: &TypeRecord,
        data: &super::type_records::UnionTypeData,
    ) -> Result<UnionTypeCacheKey, LiteralTypeCacheError> {
        let alias = self.checked_union_alias(union, record.alias())?;
        let origin = data.origin.map(|origin| {
            let Some(record) = self.type_payload(origin) else {
                return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
            };
            match record.data() {
                TypeData::Union(origin) => Ok(UnionOriginCacheKey::DenormalizedUnion(
                    origin.union.types.clone(),
                )),
                TypeData::Index(_) if self.valid_index_union_origin(origin) => {
                    Ok(UnionOriginCacheKey::Index(origin))
                }
                _ => Err(LiteralTypeCacheError::InvalidCachedUnion(union)),
            }
        });
        let origin = match origin {
            Some(origin) => Some(origin?),
            None => None,
        };
        let key = UnionTypeCacheKey {
            types: data.union.types.clone(),
            origin,
            alias,
        };
        let cached = self
            .intrinsic_bootstrap
            .as_ref()
            .and_then(|bootstrap| bootstrap.union_types.get(&key))
            .copied();
        if cached != Some(union) {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        }
        Ok(key)
    }

    #[allow(clippy::too_many_arguments)] // Structural cycles and member visits need separate sets.
    fn validate_supported_fresh_property_object(
        &self,
        type_: TypeId,
        record: &TypeRecord,
        object: &ObjectTypeData,
        array_validation: UnionArrayValidation<'_>,
        visiting: &mut HashSet<TypeId>,
        array_visited: &mut HashSet<TypeId>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        if !visiting.insert(type_) {
            return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
        }
        let result = (|| {
            let owner = record
                .symbol()
                .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
            let owner_record = self
                .symbol(owner)
                .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
            let [owner_declaration] = owner_record.declarations().unwrap_or_default() else {
                return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
            };
            if record.flags() != TypeFlags::OBJECT
                || record.alias().is_some()
                || !Self::valid_supported_property_object_tail(object)
                || self.get_merged_symbol(owner) != Some(owner)
                || owner_record.flags() != SymbolFlags::OBJECT_LITERAL
                || owner_record.check_flags() != CheckFlags::NONE
                || owner_record.name() != InternalSymbolName::Object.as_ref()
                || owner_record.value_declaration() != Some(*owner_declaration)
                || owner_record.parent().is_some()
                || owner_record.exports().is_some()
                || owner_record.export_symbol().is_some()
                || self.source_node_kind(*owner_declaration)
                    != Some(SyntaxKind::ObjectLiteralExpression)
            {
                return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
            }

            let members = object
                .structured
                .members
                .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
            if owner_record.members() == Some(members) {
                return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
            }
            let table = self
                .symbol_table(members)
                .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
            let properties =
                Self::supported_nonempty_cache_slice(object.structured.properties.as_deref())
                    .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
            if table.len() != properties.len()
                || owner_record.members().is_some() == properties.is_empty()
            {
                return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
            }
            let raw_table = match owner_record.members() {
                Some(raw_members) => Some(
                    self.symbol_table(raw_members)
                        .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?,
                ),
                None => None,
            };
            if raw_table.is_some_and(|raw| raw.len() != properties.len()) {
                return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
            }

            let mut expected_flags = ObjectFlags::ANONYMOUS
                | ObjectFlags::OBJECT_LITERAL
                | ObjectFlags::FRESH_LITERAL
                | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL
                | ObjectFlags::MEMBERS_RESOLVED;
            let mut seen_properties = HashSet::with_capacity(properties.len());
            let mut seen_raw = HashSet::with_capacity(properties.len());
            for property in properties {
                if !seen_properties.insert(*property) {
                    return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
                }
                let property_record = self
                    .symbol(*property)
                    .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
                let property_links = self
                    .value_symbol_links(*property)
                    .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
                let property_type = property_links
                    .resolved_type
                    .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
                let property_type_record = self
                    .type_payload(property_type)
                    .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
                let raw = property_links
                    .target
                    .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
                if raw == *property || !seen_raw.insert(raw) {
                    return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
                }
                let raw_record = self
                    .symbol(raw)
                    .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
                let expected_links = ValueSymbolLinks {
                    resolved_type: Some(property_type),
                    target: Some(raw),
                    ..ValueSymbolLinks::default()
                };
                if property_links != &expected_links
                    || property_record.flags() != (SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT)
                    || property_record.check_flags() != CheckFlags::NONE
                    || property_record.parent() != Some(owner)
                    || property_record.members().is_some()
                    || property_record.exports().is_some()
                    || property_record.export_symbol().is_some()
                    || self.get_merged_symbol(*property) != Some(*property)
                    || raw_record.flags() != SymbolFlags::PROPERTY
                    || raw_record.check_flags() != CheckFlags::NONE
                    || raw_record.name() != property_record.name()
                    || raw_record.declarations() != property_record.declarations()
                    || raw_record.value_declaration() != property_record.value_declaration()
                    || raw_record.parent() != Some(owner)
                    || raw_record.members().is_some()
                    || raw_record.exports().is_some()
                    || raw_record.export_symbol().is_some()
                    || self.get_merged_symbol(raw) != Some(raw)
                    || self
                        .value_symbol_links(raw)
                        .is_some_and(|links| links != &ValueSymbolLinks::default())
                {
                    return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
                }
                let [declaration] = property_record.declarations().unwrap_or_default() else {
                    return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
                };
                if property_record.value_declaration() != Some(*declaration)
                    || !matches!(
                        self.source_node_kind(*declaration),
                        Some(
                            SyntaxKind::PropertyAssignment
                                | SyntaxKind::ShorthandPropertyAssignment
                        )
                    )
                    || table.get(property_record.name()) != Some(*property)
                    || raw_table.and_then(|raw| raw.get(raw_record.name())) != Some(raw)
                {
                    return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
                }
                self.validate_union_constituent_worker(
                    property_type,
                    array_validation,
                    visiting,
                    array_visited,
                    allowed_pending,
                )?;
                expected_flags |=
                    property_type_record.object_flags() & ObjectFlags::PROPAGATING_FLAGS;
            }
            if record.object_flags() != expected_flags
                || raw_table.is_some_and(|raw| raw.iter().any(|(_, id)| !seen_raw.contains(&id)))
            {
                return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
            }
            Ok(())
        })();
        visiting.remove(&type_);
        result
    }

    fn validate_supported_unknown_empty_object(
        &self,
        type_: TypeId,
        record: &TypeRecord,
        object: &ObjectTypeData,
    ) -> bool {
        self.intrinsic_bootstrap.as_ref().is_some_and(|bootstrap| {
            type_ == bootstrap.unknown_empty_object_type
                && record.flags() == TypeFlags::OBJECT
                && record.object_flags() == ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED
                && record.symbol().is_none()
                && record.alias().is_none()
                && Self::valid_supported_property_object_tail(object)
                && object.structured.members.is_none()
                && object.structured.properties.is_none()
        })
    }

    #[allow(clippy::too_many_arguments)] // Structural cycles and member visits need separate sets.
    fn validate_supported_derived_property_object(
        &self,
        type_: TypeId,
        record: &TypeRecord,
        object: &ObjectTypeData,
        array_validation: UnionArrayValidation<'_>,
        visiting: &mut HashSet<TypeId>,
        array_visited: &mut HashSet<TypeId>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<bool, LiteralTypeCacheError> {
        let derived = match array_validation {
            UnionArrayValidation::None => self.validate_derived_object_literal_for_relation(type_),
            UnionArrayValidation::GlobalTypes(global_types) => {
                self.validate_derived_object_literal_with_global_types(type_, global_types)
            }
            UnionArrayValidation::Targets(targets) => {
                self.validate_derived_object_literal_with_array_targets(type_, targets)
            }
        };
        match derived {
            DerivedObjectLiteralValidation::NotDerived => Ok(false),
            DerivedObjectLiteralValidation::Invalid => {
                Err(LiteralTypeCacheError::InvalidCachedUnion(type_))
            }
            DerivedObjectLiteralValidation::Valid { owner, .. } => {
                if record.symbol() != Some(owner) {
                    return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
                }
                if !visiting.insert(type_) {
                    return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
                }
                let result = object
                    .structured
                    .properties
                    .as_deref()
                    .unwrap_or_default()
                    .iter()
                    .try_for_each(|property| {
                        let property_type = self
                            .value_symbol_links(*property)
                            .and_then(|links| links.resolved_type)
                            .ok_or(LiteralTypeCacheError::InvalidCachedUnion(type_))?;
                        self.validate_union_constituent_worker(
                            property_type,
                            array_validation,
                            visiting,
                            array_visited,
                            allowed_pending,
                        )
                    });
                visiting.remove(&type_);
                result.map(|()| true)
            }
        }
    }

    fn valid_supported_property_object_tail(object: &ObjectTypeData) -> bool {
        object.target.is_none()
            && object.mapper.is_none()
            && object.instantiations == TypeCacheState::Unallocated
            && object.structured.constrained == ConstrainedTypeData::default()
            && object.structured.signatures.is_none()
            && object.structured.call_signature_count == 0
            && object.structured.index_infos.is_none()
            && object
                .structured
                .object_type_without_abstract_construct_signatures
                .is_none()
    }

    fn supported_nonempty_cache_slice<T>(value: Option<&[T]>) -> Option<&[T]> {
        match value {
            None => Some(&[]),
            Some(value) if !value.is_empty() => Some(value),
            Some(_) => None,
        }
    }

    fn validate_cached_array_capability_worker(
        &self,
        type_: TypeId,
        array_validation: UnionArrayValidation<'_>,
        visited: &mut HashSet<TypeId>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        if !visited.insert(type_) {
            return Ok(());
        }
        let Some(record) = self.type_payload(type_) else {
            return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
        };
        match record.data() {
            TypeData::Tuple(_) => self.validate_supported_canonical_tuple(
                type_,
                array_validation,
                &mut HashSet::new(),
                visited,
                allowed_pending,
            ),
            TypeData::TypeReference(reference) => {
                if reference.object.target.is_some_and(|target| {
                    matches!(
                        self.type_payload(target).map(TypeRecord::data),
                        Some(TypeData::Tuple(_))
                    )
                }) {
                    self.validate_supported_canonical_tuple(
                        type_,
                        array_validation,
                        &mut HashSet::new(),
                        visited,
                        allowed_pending,
                    )
                } else {
                    self.validate_cached_type_reference_array_capability(
                        type_,
                        record,
                        reference,
                        array_validation,
                        visited,
                        allowed_pending,
                    )
                }
            }
            TypeData::Union(data) => {
                self.validate_union_structure(type_)?;
                for constituent in &data.union.types {
                    self.validate_cached_array_capability_worker(
                        *constituent,
                        array_validation,
                        visited,
                        allowed_pending,
                    )?;
                }
                if let Some(alias) = record.alias().and_then(|alias| self.type_alias(alias)) {
                    for argument in alias.type_arguments().unwrap_or_default() {
                        self.validate_cached_array_capability_worker(
                            *argument,
                            array_validation,
                            visited,
                            allowed_pending,
                        )?;
                    }
                }
                Ok(())
            }
            TypeData::Object(_) | TypeData::Interface(_) => {
                let recognized_library_interface = matches!(record.data(), TypeData::Interface(_))
                    && !record.object_flags().contains(ObjectFlags::REFERENCE)
                    && record.symbol().is_some_and(|symbol| {
                        object_members::authenticated_default_library_interface_owner(self, symbol)
                            && self.source_has_only_interface_property_members(symbol)
                    });
                if let TypeData::Interface(interface) = record.data()
                    && !record.object_flags().contains(ObjectFlags::REFERENCE)
                    && let Some(edges) = self.lazy_default_library_interface_union_edges(
                        type_,
                        record,
                        interface,
                        array_validation.targets(),
                    )
                {
                    for edge in edges {
                        self.validate_cached_array_capability_worker(
                            edge,
                            array_validation,
                            visited,
                            allowed_pending,
                        )?;
                    }
                    return Ok(());
                }
                let unsupported_callable = matches!(
                    record.data(),
                    TypeData::Object(object)
                        if object.structured.signatures.is_some()
                            || object.structured.call_signature_count != 0
                );
                match validate_stored_callable_set(self, type_) {
                    StoredCallableSetValidation::Valid { edges, .. } => {
                        for edge in edges {
                            self.validate_cached_array_capability_worker(
                                edge,
                                array_validation,
                                visited,
                                allowed_pending,
                            )?;
                        }
                        return Ok(());
                    }
                    StoredCallableSetValidation::Pending {
                        family:
                            CallableFamily::FunctionType | CallableFamily::DeclaredCallSignatures,
                    } if allowed_pending.contains(&type_) => {
                        return Ok(());
                    }
                    StoredCallableSetValidation::Malformed { .. }
                    | StoredCallableSetValidation::Pending { .. } => {
                        return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
                    }
                    StoredCallableSetValidation::NotCallable if unsupported_callable => {
                        return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
                    }
                    StoredCallableSetValidation::NotCallable => {}
                }
                if let TypeData::Interface(interface) = record.data()
                    && self.direct_interface_heritage_provenance(type_).is_some()
                {
                    match validate_interface_heritage_members_with_array_targets(
                        self,
                        type_,
                        array_validation.targets(),
                    ) {
                        InterfaceHeritageMembersValidation::Valid => {
                            for property in interface
                                .reference
                                .object
                                .structured
                                .properties
                                .as_deref()
                                .unwrap_or_default()
                            {
                                let links = self
                                    .value_symbol_links(*property)
                                    .ok_or(LiteralTypeCacheError::InvalidCachedUnion(type_))?;
                                if let Some(target) = links.target {
                                    let reference = inherited_generic_property_reference(
                                        self,
                                        type_,
                                        *property,
                                        array_validation.targets(),
                                    )
                                    .ok_or(LiteralTypeCacheError::InvalidCachedUnion(type_))?;
                                    let template = self
                                        .value_symbol_links(target)
                                        .and_then(|links| links.resolved_type)
                                        .ok_or(LiteralTypeCacheError::InvalidCachedUnion(type_))?;
                                    // The proxy can stay lazy, but its template and substitutions cannot be skipped.
                                    for edge in [template, reference] {
                                        self.validate_cached_array_capability_worker(
                                            edge,
                                            array_validation,
                                            visited,
                                            allowed_pending,
                                        )?;
                                    }
                                } else if links.resolved_type.is_none() {
                                    return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
                                }
                                if let Some(property_type) = links.resolved_type {
                                    self.validate_cached_array_capability_worker(
                                        property_type,
                                        array_validation,
                                        visited,
                                        allowed_pending,
                                    )?;
                                }
                            }
                            for index in interface
                                .reference
                                .object
                                .structured
                                .index_infos
                                .as_deref()
                                .unwrap_or_default()
                            {
                                let value_type = self
                                    .index_info(*index)
                                    .ok_or(LiteralTypeCacheError::InvalidCachedUnion(type_))?
                                    .value_type();
                                self.validate_cached_array_capability_worker(
                                    value_type,
                                    array_validation,
                                    visited,
                                    allowed_pending,
                                )?;
                            }
                            return Ok(());
                        }
                        InterfaceHeritageMembersValidation::Malformed
                        | InterfaceHeritageMembersValidation::NotHeritage => {
                            return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
                        }
                    }
                }
                match object_members::validate_resolved_declared_property_type_graph(self, type_) {
                    object_members::DeclaredPropertyTypeGraphValidation::Traversable(
                        property_types,
                    ) => {
                        for property_type in property_types {
                            self.validate_cached_array_capability_worker(
                                property_type,
                                array_validation,
                                visited,
                                allowed_pending,
                            )?;
                        }
                        Ok(())
                    }
                    object_members::DeclaredPropertyTypeGraphValidation::Opaque
                        if recognized_library_interface =>
                    {
                        // A failed library proof must not hide its member type edges.
                        Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))
                    }
                    object_members::DeclaredPropertyTypeGraphValidation::Opaque => Ok(()),
                    object_members::DeclaredPropertyTypeGraphValidation::Malformed => {
                        Err(LiteralTypeCacheError::InvalidCachedUnion(type_))
                    }
                }
            }
            _ => Ok(()),
        }
    }

    /// The full-member proof owns only source property and method declarations.
    fn source_has_only_interface_property_members(&self, symbol: SemanticSymbolId) -> bool {
        let Some(declarations) = self.symbol(symbol).and_then(|owner| owner.declarations()) else {
            return false;
        };
        for &declaration in declarations {
            if self.source_node_kind(declaration) != Some(SyntaxKind::InterfaceDeclaration) {
                continue;
            }
            let Some(children) = self.source_direct_children(declaration) else {
                return false;
            };
            if children.iter().any(|child| {
                !matches!(
                    self.source_node_kind(*child),
                    Some(
                        SyntaxKind::Identifier
                            | SyntaxKind::DeclareKeyword
                            | SyntaxKind::MethodSignature
                            | SyntaxKind::PropertyDeclaration
                            | SyntaxKind::PropertySignature
                    )
                )
            }) {
                return false;
            }
        }
        true
    }

    fn validate_cached_type_reference_array_capability(
        &self,
        type_: TypeId,
        record: &TypeRecord,
        reference: &super::type_records::TypeReferenceData,
        array_validation: UnionArrayValidation<'_>,
        visited: &mut HashSet<TypeId>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        let targets = match array_validation {
            UnionArrayValidation::None => None,
            UnionArrayValidation::GlobalTypes(global_types) => {
                Some(CanonicalArrayTargets::from_global_types(global_types))
            }
            UnionArrayValidation::Targets(targets) => Some(targets),
        };
        let target = reference.object.target;
        let configured_target = targets.is_some_and(|targets| {
            target == Some(targets.array_type()) || target == Some(targets.readonly_array_type())
        });
        let global_named_target = record
            .symbol()
            .is_some_and(|symbol| self.symbol_is_registered_global_array(symbol))
            || target
                .and_then(|target| self.type_payload(target))
                .and_then(TypeRecord::symbol)
                .is_some_and(|symbol| self.symbol_is_registered_global_array(symbol));
        let is_array_candidate = configured_target || global_named_target;

        if let Some(targets) = targets {
            if is_array_candidate {
                let array = self
                    .canonical_array_reference_with_targets(targets, type_)
                    .map_err(|error| LiteralTypeCacheError::ArrayType { type_, error })?
                    .ok_or(LiteralTypeCacheError::ArrayType {
                        type_,
                        error: ArrayTypeError::InvalidReference(type_),
                    })?;
                return self.validate_cached_array_capability_worker(
                    array.element_type,
                    array_validation,
                    visited,
                    allowed_pending,
                );
            }
        } else if is_array_candidate {
            let target = target.ok_or(LiteralTypeCacheError::ArrayType {
                type_,
                error: ArrayTypeError::InvalidReference(type_),
            })?;
            self.canonical_array_reference_with_targets(
                CanonicalArrayTargets::for_single_target_validation(target),
                type_,
            )
            .map_err(|error| LiteralTypeCacheError::ArrayType { type_, error })?
            .ok_or(LiteralTypeCacheError::ArrayType {
                type_,
                error: ArrayTypeError::InvalidReference(type_),
            })?;
            return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
        }

        for argument in reference
            .resolved_type_arguments
            .as_deref()
            .unwrap_or_default()
        {
            self.validate_cached_array_capability_worker(
                *argument,
                array_validation,
                visited,
                allowed_pending,
            )?;
        }
        Ok(())
    }

    fn symbol_is_registered_global_array(&self, symbol: SemanticSymbolId) -> bool {
        let Some(globals) = self
            .intrinsic_bootstrap
            .as_ref()
            .and_then(|bootstrap| self.symbol_table(bootstrap.globals))
        else {
            return false;
        };
        let canonical = self.get_merged_symbol(symbol);
        ["Array", "ReadonlyArray"].into_iter().any(|name| {
            globals.get_source(name).is_some_and(|global| {
                global == symbol
                    || canonical.is_some() && self.get_merged_symbol(global) == canonical
            })
        })
    }

    fn validate_supported_canonical_array(
        &self,
        type_: TypeId,
        array_validation: UnionArrayValidation<'_>,
        visiting: &mut HashSet<TypeId>,
        array_visited: &mut HashSet<TypeId>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        let reference = match array_validation {
            UnionArrayValidation::None => None,
            UnionArrayValidation::GlobalTypes(global_types) => self
                .canonical_array_reference(global_types, type_)
                .map_err(|error| LiteralTypeCacheError::ArrayType { type_, error })?,
            UnionArrayValidation::Targets(targets) => self
                .canonical_array_reference_with_targets(targets, type_)
                .map_err(|error| LiteralTypeCacheError::ArrayType { type_, error })?,
        }
        .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
        if !visiting.insert(type_) {
            return Err(LiteralTypeCacheError::ArrayType {
                type_,
                error: ArrayTypeError::InvalidReference(type_),
            });
        }
        // The element remains inside the installed union domain. In
        // particular, declared interface and type-literal elements are proved
        // by their resolved property shells without recursively forcing legal
        // self-references such as `Node.next: Node` through this domain.
        let result = self.validate_union_constituent_worker(
            reference.element_type,
            array_validation,
            visiting,
            array_visited,
            allowed_pending,
        );
        visiting.remove(&type_);
        result
    }

    fn validate_supported_generic_interface_reference(
        &self,
        type_: TypeId,
        array_validation: UnionArrayValidation<'_>,
        visiting: &mut HashSet<TypeId>,
        array_visited: &mut HashSet<TypeId>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        let reference = super::reference_types::validate_direct_generic_reference(self, type_)
            .map_err(|_| LiteralTypeCacheError::InvalidCachedUnion(type_))?;
        if !visiting.insert(type_) {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
        }
        let result = reference.type_arguments.iter().try_for_each(|argument| {
            self.validate_union_constituent_worker(
                *argument,
                array_validation,
                visiting,
                array_visited,
                allowed_pending,
            )
        });
        visiting.remove(&type_);
        result
    }

    /// Library annotations keep their declared identity as member queries populate caches.
    fn lazy_default_library_interface_union_edges(
        &self,
        type_: TypeId,
        record: &TypeRecord,
        interface: &InterfaceTypeData,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> Option<Vec<TypeId>> {
        let symbol = record.symbol()?;
        if !object_members::authenticated_default_library_interface_owner(self, symbol)
            || self.direct_interface_heritage_provenance(type_).is_some()
            || interface.resolved_base_constructor_type.is_some()
            || interface.resolved_base_types.is_some()
            || interface.declared_call_signatures.is_some()
            || interface.declared_construct_signatures.is_some()
            || interface.declared_index_infos.is_some()
        {
            return None;
        }
        let flags = record.object_flags()
            & !(ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
                | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES);
        let structured = &interface.reference.object.structured;
        let cold = structured == &StructuredTypeData::default()
            && !interface.declared_members_resolved
            && interface.declared_members.is_none();
        let reference = flags == ObjectFlags::INTERFACE | ObjectFlags::REFERENCE
            && cold
            && !interface.base_types_resolved
            && validate_nongeneric_interface_argument_origin(self, type_).is_ok();
        if reference {
            return Some(Vec::new());
        }
        let resolved = flags == ObjectFlags::INTERFACE | ObjectFlags::MEMBERS_RESOLVED
            && interface.base_types_resolved
            && interface.declared_members_resolved
            && interface.declared_members == structured.members
            && valid_declared_member_table(self, symbol, interface.declared_members)
            && Self::valid_supported_property_object_tail(&interface.reference.object);
        let thisless = (flags == ObjectFlags::INTERFACE && cold || resolved)
            && record.flags() == TypeFlags::OBJECT
            && record.alias().is_none()
            && object_members::valid_thisless_interface_identity(interface)
            && cached_interface_type(self, symbol).ok().flatten() == Some(type_)
            && !self.declared_type_initialization_in_progress(symbol)
            && !matches!(
                object_members::validate_resolved_declared_property_type_graph(self, type_),
                object_members::DeclaredPropertyTypeGraphValidation::Malformed
            );
        if !thisless {
            return None;
        }
        self.lazy_default_library_interface_member_edges(
            symbol,
            array_targets,
            resolved.then_some(structured),
        )
    }

    /// Unqueried members add no type edges. Published members retain their source
    /// checks and contribute every type needed by the array capability scan.
    #[allow(clippy::too_many_lines)] // Check source ownership and both member tables together.
    fn lazy_default_library_interface_member_edges(
        &self,
        symbol: SemanticSymbolId,
        array_targets: Option<CanonicalArrayTargets>,
        resolved: Option<&StructuredTypeData>,
    ) -> Option<Vec<TypeId>> {
        let owner = self.symbol(symbol)?;
        let declarations = owner.declarations()?;
        let table = match owner.members() {
            Some(table) => Some(self.symbol_table(table)?),
            None => None,
        };
        let mut named_members = HashSet::new();
        let mut seen = HashSet::new();
        let mut resolved_members = Vec::new();
        let mut edges = Vec::new();
        for &declaration in declarations {
            if self.source_node_kind(declaration) != Some(SyntaxKind::InterfaceDeclaration) {
                continue;
            }
            for node in self.source_direct_children(declaration)? {
                match self.source_node_kind(node)? {
                    SyntaxKind::Identifier | SyntaxKind::DeclareKeyword => continue,
                    SyntaxKind::MethodSignature
                    | SyntaxKind::PropertyDeclaration
                    | SyntaxKind::PropertySignature
                    | SyntaxKind::GetAccessor
                    | SyntaxKind::SetAccessor
                    | SyntaxKind::IndexSignature
                    | SyntaxKind::CallSignature
                    | SyntaxKind::ConstructSignature => {}
                    _ => return None,
                }
                let member = self.source_declaration_symbol(node)?;
                let member_record = self.symbol(member)?;
                if self.get_parent_of_symbol(member) != Some(symbol)
                    || !self.source_merged_symbol_declarations_match(member)
                {
                    return None;
                }
                if member_record.name() != InternalSymbolName::Computed.as_ref() {
                    if table
                        .and_then(|table| table.get(member_record.name()))
                        .and_then(|raw| self.get_merged_symbol(raw))
                        != Some(member)
                    {
                        return None;
                    }
                    named_members.insert(member);
                } else if self
                    .source_child_with_kind(node, SyntaxKind::ComputedPropertyName)
                    .is_none()
                {
                    return None;
                }
                if seen.insert(member) {
                    if let Some(resolved) = resolved {
                        let published = self
                            .late_bound_links(member)
                            .and_then(|links| links.late_symbol)
                            .unwrap_or(member);
                        let name = self.symbol(published)?.name();
                        if self
                            .value_symbol_links(published)
                            .and_then(|links| links.resolved_type)
                            .is_none()
                            || self
                                .symbol_table(resolved.members?)?
                                .get(name)
                                .and_then(|symbol| self.get_merged_symbol(symbol))
                                != Some(published)
                        {
                            return None;
                        }
                        if !resolved_members.contains(&published) {
                            resolved_members.push(published);
                        }
                    }
                    edges.extend(self.lazy_default_library_member_edges(member, array_targets)?);
                }
            }
        }
        if table.is_some_and(|table| {
            table.len() != named_members.len()
                || table.iter().any(|(name, raw)| {
                    self.get_merged_symbol(raw).is_none_or(|member| {
                        !named_members.contains(&member)
                            || self
                                .symbol(member)
                                .is_none_or(|record| record.name() != name)
                    })
                })
        }) {
            return None;
        }
        if let Some(resolved) = resolved
            && (resolved.properties.as_deref()
                != (!resolved_members.is_empty()).then_some(resolved_members.as_slice())
                || resolved.members.is_some_and(|table| {
                    self.symbol_table(table)
                        .is_none_or(|table| table.len() != resolved_members.len())
                }))
        {
            return None;
        }
        Some(edges)
    }

    #[allow(clippy::too_many_lines)] // Validates one member and its published annotation caches.
    fn lazy_default_library_member_edges(
        &self,
        source: SemanticSymbolId,
        array_targets: Option<CanonicalArrayTargets>,
    ) -> Option<Vec<TypeId>> {
        let source_record = self.symbol(source)?;
        let member = self
            .late_bound_links(source)
            .and_then(|links| links.late_symbol)
            .unwrap_or(source);
        let record = self.symbol(member)?;
        if member != source
            && (!record.flags().contains(SymbolFlags::METHOD)
                || record.check_flags() != CheckFlags::LATE
                || self.get_parent_of_symbol(member) != self.get_parent_of_symbol(source)
                || self
                    .late_bound_method_sources(member)
                    .is_none_or(|sources| !sources.contains(&source))
                || self.authenticated_interface_method_owner(member).is_none()
                || self
                    .value_symbol_links(source)
                    .is_some_and(|links| links != &ValueSymbolLinks::default()))
        {
            return None;
        }
        if let Some(value) = self
            .value_symbol_links(member)
            .and_then(|links| links.resolved_type)
        {
            if record.flags().contains(SymbolFlags::METHOD) {
                let (callable, expected) =
                    object_members::declared_method_value_types(self, member)?;
                if expected != value
                    || !record.declarations()?.iter().all(|declaration| {
                        self.lazy_default_library_annotation_children_are_exact(
                            *declaration,
                            array_targets,
                            &mut HashSet::new(),
                        )
                    })
                {
                    return None;
                }
                let Some(StoredCallableSetValidation::Valid { edges, .. }) =
                    validate_stored_declared_method_callable_set(self, callable)
                else {
                    return None;
                };
                // Keep the dependencies from the provider that proved this publication.
                return Some(edges);
            }
            if record.flags().without(SymbolFlags::OPTIONAL) != SymbolFlags::PROPERTY
                || self.value_symbol_links(member)
                    != Some(&ValueSymbolLinks {
                        resolved_type: Some(value),
                        ..ValueSymbolLinks::default()
                    })
            {
                return None;
            }
            for &declaration in record.declarations()? {
                let annotation = self.source_direct_type_annotation(declaration)?;
                let annotation_type = self.lazy_default_library_annotation_type(
                    annotation,
                    array_targets,
                    &mut HashSet::new(),
                )?;
                // Nongeneric properties store the annotation. Reads add optionality.
                if value != annotation_type {
                    return None;
                }
            }
            return Some(vec![value]);
        }
        if member != source {
            return None;
        }
        let mut pending = source_record.declarations()?.to_vec();
        let mut edges = Vec::new();
        while let Some(node) = pending.pop() {
            if let Some(type_) = self
                .type_node_links(node)
                .and_then(|links| links.resolved_type)
            {
                let kind = self.source_node_kind(node)?;
                if !kind.is_keyword_type()
                    && !(SyntaxKind::FIRST_TYPE_NODE as u16..=SyntaxKind::LAST_TYPE_NODE as u16)
                        .contains(&(kind as u16))
                    || self.lazy_default_library_annotation_type(
                        node,
                        array_targets,
                        &mut HashSet::new(),
                    ) != Some(type_)
                {
                    return None;
                }
                edges.push(type_);
                if matches!(
                    self.source_node_kind(node),
                    Some(SyntaxKind::FunctionType | SyntaxKind::ConstructorType)
                ) && matches!(
                    validate_stored_callable_set(self, type_),
                    StoredCallableSetValidation::Valid { .. }
                ) {
                    continue;
                }
            } else if self
                .type_node_links(node)
                .is_some_and(|links| links != &TypeNodeLinks::default())
            {
                return None;
            }
            if self
                .signature_links(node)
                .is_some_and(|links| links != &SignatureLinks::default())
                || self.source_declaration_symbol(node).is_some_and(|member| {
                    !self.source_merged_symbol_declarations_match(member)
                        || self
                            .value_symbol_links(member)
                            .is_some_and(|links| links != &ValueSymbolLinks::default())
                        || self
                            .late_bound_links(member)
                            .is_some_and(|links| links != &LateBoundLinks::default())
                })
            {
                return None;
            }
            pending.extend(self.source_direct_children(node)?);
        }
        Some(edges)
    }

    /// Rebuilds the annotation identity from source before accepting a cached type.
    #[allow(clippy::too_many_lines)] // Each syntax case uses its canonical type validator.
    fn lazy_default_library_annotation_type(
        &self,
        node: NodeRef,
        array_targets: Option<CanonicalArrayTargets>,
        active: &mut HashSet<NodeRef>,
    ) -> Option<TypeId> {
        if !active.insert(node) {
            return None;
        }
        let result = (|| {
            let kind = self.source_node_kind(node)?;
            if kind == SyntaxKind::ParenthesizedType {
                let children = self.source_direct_children(node)?;
                let [child] = children.as_slice() else {
                    return None;
                };
                let expected =
                    self.lazy_default_library_annotation_type(*child, array_targets, active)?;
                return self
                    .type_node_links(node)
                    .is_none_or(|links| {
                        links == &TypeNodeLinks::default()
                            || links
                                == &TypeNodeLinks {
                                    resolved_type: Some(expected),
                                    ..TypeNodeLinks::default()
                                }
                    })
                    .then_some(expected);
            }
            let cached = validated_method_annotation_type(self, node)?;
            if kind != SyntaxKind::TypeReference
                && self.source_type_node_result_is_exact(node, cached, &[])
            {
                return Some(cached);
            }
            let children = self.source_direct_children(node)?;
            match kind {
                SyntaxKind::ArrayType => {
                    let [element] = children.as_slice() else {
                        return None;
                    };
                    let readonly = matches!(
                        self.source_node_parent(node),
                        Some(SourceNodeParent::Parent(parent))
                            if self.source_type_operator(parent) == Some(SyntaxKind::ReadonlyKeyword)
                    );
                    let name = if readonly { "ReadonlyArray" } else { "Array" };
                    let owner = self
                        .source_global_bindings()?
                        .get(ts_binder::EscapedNameRef::source(name))?
                        .symbol;
                    let target = self.declared_type_links(owner)?.declared_type?;
                    let targets = array_targets.unwrap_or_else(|| {
                        CanonicalArrayTargets::for_single_target_validation(target)
                    });
                    let expected_target = if readonly {
                        targets.readonly_array_type()
                    } else {
                        targets.array_type()
                    };
                    let TypeData::TypeReference(reference) = self.type_payload(cached)?.data()
                    else {
                        return None;
                    };
                    if target != expected_target || reference.object.target != Some(target) {
                        return None;
                    }
                    let array = self
                        .canonical_array_reference_with_targets(targets, cached)
                        .ok()??;
                    let expected_element =
                        self.lazy_default_library_annotation_type(*element, array_targets, active)?;
                    (array.base_type == cached && array.element_type == expected_element)
                        .then_some(cached)
                }
                SyntaxKind::TypeReference => {
                    let (name, arguments) = children.split_first()?;
                    let symbol = self.lazy_default_library_reference_symbol(*name)?;
                    if self
                        .symbol_node_links(node)
                        .and_then(|links| links.resolved_symbol)
                        != Some(symbol)
                        || !self.source_merged_symbol_declarations_match(symbol)
                    {
                        return None;
                    }
                    let owner = self.symbol(symbol)?;
                    if owner.flags() == SymbolFlags::TYPE_PARAMETER {
                        return (arguments.is_empty()
                            && cached_ordinary_type_parameter_owner(self, cached) == Some(symbol))
                        .then_some(cached);
                    }
                    if owner.flags() == SymbolFlags::TYPE_ALIAS {
                        let [declaration] = owner.declarations()? else {
                            return None;
                        };
                        let links = self.type_alias_links(symbol)?;
                        if !arguments.is_empty()
                            || links.type_parameters.is_some()
                            || links.instantiations.is_some()
                            || links.is_constructor_declared_property
                            || links.declared_type != Some(cached)
                        {
                            return None;
                        }
                        let body = self.source_direct_type_annotation(*declaration)?;
                        return (self.lazy_default_library_annotation_type(
                            body,
                            array_targets,
                            active,
                        )? == cached)
                            .then_some(cached);
                    }
                    let target = if owner.flags().contains(SymbolFlags::CLASS) {
                        cached_class_type(self, symbol).ok()??
                    } else if owner.flags().contains(SymbolFlags::INTERFACE) {
                        cached_interface_type(self, symbol).ok()??
                    } else {
                        return None;
                    };
                    if arguments.is_empty() {
                        return (super::declared::preflight_class_or_interface_reference(
                            self,
                            &super::DeclaredTypeHost::default(),
                            symbol,
                            owner.flags(),
                        )
                        .ok()?
                            == 0
                            && target == cached)
                            .then_some(cached);
                    }
                    let reference = validate_direct_generic_reference(self, cached).ok()?;
                    if reference.target != target
                        || reference.type_arguments.len() != arguments.len()
                    {
                        return None;
                    }
                    for (&argument, expected) in arguments.iter().zip(reference.type_arguments) {
                        if self.lazy_default_library_annotation_type(
                            argument,
                            array_targets,
                            active,
                        )? != expected
                        {
                            return None;
                        }
                    }
                    Some(cached)
                }
                SyntaxKind::UnionType => {
                    let types = children
                        .into_iter()
                        .map(|child| {
                            self.lazy_default_library_annotation_type(child, array_targets, active)
                        })
                        .collect::<Option<Vec<_>>>()?;
                    let mut parent = node;
                    let alias = loop {
                        let Some(SourceNodeParent::Parent(next)) = self.source_node_parent(parent)
                        else {
                            break None;
                        };
                        match self.source_node_kind(next)? {
                            SyntaxKind::ParenthesizedType => parent = next,
                            SyntaxKind::TypeAliasDeclaration => {
                                break self.source_declaration_symbol(next);
                            }
                            _ => break None,
                        }
                    };
                    (self
                        .cached_annotation_union_type(&types, alias.map(|owner| (owner, &[][..])))
                        .ok()??
                        == cached)
                        .then_some(cached)
                }
                SyntaxKind::TypeOperator
                    if self.source_type_operator(node) == Some(SyntaxKind::ReadonlyKeyword) =>
                {
                    let [child] = children.as_slice() else {
                        return None;
                    };
                    (self.lazy_default_library_annotation_type(*child, array_targets, active)?
                        == cached)
                        .then_some(cached)
                }
                SyntaxKind::LiteralType
                    if matches!(children.as_slice(), [child]
                    if self.source_node_kind(*child) == Some(SyntaxKind::NullKeyword)) =>
                {
                    (cached == self.intrinsic_bootstrap()?.null_type).then_some(cached)
                }
                SyntaxKind::FunctionType | SyntaxKind::ConstructorType => {
                    let StoredCallableSetValidation::Valid {
                        family: CallableFamily::FunctionType,
                        projection,
                        ..
                    } = validate_stored_callable_set(self, cached)
                    else {
                        return None;
                    };
                    let signatures = projection
                        .call_signatures
                        .iter()
                        .map(|callable| callable.signature)
                        .chain(projection.construct_signatures.iter().copied())
                        .collect::<Vec<_>>();
                    let [signature] = signatures.as_slice() else {
                        return None;
                    };
                    (self.signature(*signature)?.declaration() == Some(node)
                        && self.lazy_default_library_annotation_children_are_exact(
                            node,
                            array_targets,
                            active,
                        ))
                    .then_some(cached)
                }
                _ => None,
            }
        })();
        active.remove(&node);
        result
    }

    fn lazy_default_library_annotation_children_are_exact(
        &self,
        node: NodeRef,
        array_targets: Option<CanonicalArrayTargets>,
        active: &mut HashSet<NodeRef>,
    ) -> bool {
        let Some(mut pending) = self.source_direct_children(node) else {
            return false;
        };
        while let Some(child) = pending.pop() {
            if let Some(type_) = self
                .type_node_links(child)
                .and_then(|links| links.resolved_type)
                && self.source_node_kind(child).is_some_and(|kind| {
                    kind.is_keyword_type()
                        || (SyntaxKind::FIRST_TYPE_NODE as u16..=SyntaxKind::LAST_TYPE_NODE as u16)
                            .contains(&(kind as u16))
                })
                && self.lazy_default_library_annotation_type(child, array_targets, active)
                    != Some(type_)
            {
                return false;
            }
            let Some(children) = self.source_direct_children(child) else {
                return false;
            };
            pending.extend(children);
        }
        true
    }

    fn lazy_default_library_reference_symbol(&self, name: NodeRef) -> Option<SemanticSymbolId> {
        if self.source_node_kind(name) == Some(SyntaxKind::QualifiedName) {
            let children = self.source_direct_children(name)?;
            let [left, right] = children.as_slice() else {
                return None;
            };
            let parent = self.lazy_default_library_reference_symbol(*left)?;
            let name = self.source_identifier_text(*right)?;
            return self
                .symbol(parent)?
                .exports()
                .and_then(|table| self.symbol_table(table))?
                .get_source(name)
                .and_then(|symbol| self.get_merged_symbol(symbol));
        }
        let text = self.source_identifier_text(name)?;
        let mut scope = name;
        while let Some(SourceNodeParent::Parent(parent)) = self.source_node_parent(scope) {
            for child in self.source_direct_children(parent)? {
                if self.source_node_kind(child) == Some(SyntaxKind::TypeParameter)
                    && self
                        .source_child_with_kind(child, SyntaxKind::Identifier)
                        .and_then(|name| self.source_identifier_text(name))
                        == Some(text)
                {
                    return self.source_declaration_symbol(child);
                }
            }
            scope = parent;
        }
        let binding = self
            .source_global_bindings()?
            .get(ts_binder::EscapedNameRef::source(text))?;
        let globals = self.intrinsic_bootstrap()?.globals;
        (self.symbol_table(globals)?.get_source(text) == Some(binding.table_symbol)
            && self.get_merged_symbol(binding.table_symbol) == Some(binding.symbol))
        .then_some(binding.symbol)
    }

    /// Validates deferred operands without evaluating the indexed access.
    #[allow(clippy::too_many_arguments)]
    fn validate_supported_deferred_indexed_access(
        &self,
        type_: TypeId,
        record: &TypeRecord,
        indexed: &IndexedAccessTypeData,
        array_validation: UnionArrayValidation<'_>,
        visiting: &mut HashSet<TypeId>,
        array_visited: &mut HashSet<TypeId>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        let invalid = || LiteralTypeCacheError::InvalidCachedUnion(type_);
        let variable_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
        if record.flags() != TypeFlags::INDEXED_ACCESS
            || record.object_flags() != ObjectFlags::NONE && record.object_flags() != variable_flags
            || record.symbol().is_some()
            || record.alias().is_some()
            || indexed.constrained != ConstrainedTypeData::default()
            || indexed.access_flags & !AccessFlags::PERSISTENT != AccessFlags::NONE
            || cached_deferred_indexed_access_type(
                self,
                indexed.object_type,
                indexed.index_type,
                indexed.access_flags,
            ) != Ok(Some(type_))
        {
            return Err(invalid());
        }
        let index_owner = cached_ordinary_type_parameter_owner(self, indexed.index_type)
            .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
        if !self.source_symbol_declarations_match(index_owner) {
            return Err(invalid());
        }
        let object_owner = cached_ordinary_type_parameter_owner(self, indexed.object_type);
        if let Some(object_owner) = object_owner {
            if !self.source_symbol_declarations_match(object_owner) {
                return Err(invalid());
            }
        } else if !self.source_mapped_indexed_template_is_exact(type_) {
            return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
        }

        if !visiting.insert(type_) {
            return Err(invalid());
        }
        let result = object_owner
            .map(|_| indexed.object_type)
            .into_iter()
            .chain(std::iter::once(indexed.index_type))
            .try_for_each(|operand| {
                self.validate_union_constituent_worker(
                    operand,
                    array_validation,
                    visiting,
                    array_visited,
                    allowed_pending,
                )
            });
        visiting.remove(&type_);
        result
    }

    fn validate_supported_canonical_tuple(
        &self,
        type_: TypeId,
        array_validation: UnionArrayValidation<'_>,
        visiting: &mut HashSet<TypeId>,
        array_visited: &mut HashSet<TypeId>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        let tuple = self
            .canonical_tuple_shape(type_)
            .map_err(|_| LiteralTypeCacheError::InvalidCachedUnion(type_))?
            .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
        if !visiting.insert(type_) {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
        }
        // Declared members can refer back to this tuple. Direct containment
        // cycles still fail through the separate structural visiting set.
        array_visited.insert(type_);
        let result = tuple.element_types().iter().try_for_each(|element| {
            self.validate_union_constituent_worker(
                *element,
                array_validation,
                visiting,
                array_visited,
                allowed_pending,
            )
        });
        visiting.remove(&type_);
        result
    }

    /// Authenticates the shared parameter created by merging generic interfaces.
    fn valid_supported_merged_type_parameter(
        &self,
        type_: TypeId,
        symbol: SemanticSymbolId,
        parameter: &super::type_records::TypeParameterData,
    ) -> bool {
        let Some(record) = self.symbol(symbol) else {
            return false;
        };
        let Some(declarations) = record
            .declarations()
            .filter(|declarations| !declarations.is_empty())
        else {
            return false;
        };
        let Some(owner) = self.get_parent_of_symbol(symbol) else {
            return false;
        };
        let Some(owner_record) = self.symbol(owner) else {
            return false;
        };
        let Some(owner_declarations) = owner_record.declarations() else {
            return false;
        };
        let Some(members) = owner_record
            .members()
            .and_then(|members| self.symbol_table(members))
        else {
            return false;
        };
        let Some(owner_type) = self
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
        else {
            return false;
        };
        let Some(owner_type_record) = self.type_payload(owner_type) else {
            return false;
        };
        let TypeData::Interface(interface) = owner_type_record.data() else {
            return false;
        };
        let Some(arguments) = interface.reference.resolved_type_arguments.as_deref() else {
            return false;
        };
        let Some(all_parameters) = interface.all_type_parameters.as_deref() else {
            return false;
        };
        let Some(bootstrap) = self.intrinsic_bootstrap.as_ref() else {
            return false;
        };
        let ordinary = record.flags() == SymbolFlags::TYPE_PARAMETER;
        let merged = record.flags() == SymbolFlags::TYPE_PARAMETER | SymbolFlags::TRANSIENT;
        let allowed_owner_flags =
            SymbolFlags::INTERFACE | SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::TRANSIENT;
        if !ordinary && !merged
            || declarations.len() < 2
            || record.members().is_some()
            || owner_record.flags().without(allowed_owner_flags) != SymbolFlags::NONE
            || !owner_record.flags().contains(SymbolFlags::INTERFACE)
            || owner_record.flags().contains(SymbolFlags::TRANSIENT) != merged
            || owner_record.check_flags() != CheckFlags::NONE
            || owner_record.exports().is_some()
            || owner_record.export_symbol().is_some()
            || self.get_merged_symbol(owner) != Some(owner)
            || members
                .get(record.name())
                .and_then(|parameter| self.get_merged_symbol(parameter))
                != Some(symbol)
            || owner_type_record.flags() != TypeFlags::OBJECT
            || !owner_type_record
                .object_flags()
                .contains(ObjectFlags::INTERFACE | ObjectFlags::REFERENCE)
            || owner_type_record.symbol() != Some(owner)
            || owner_type_record.alias().is_some()
            || interface.outer_type_parameter_count != 0
            || interface.reference.object.target != Some(owner_type)
            || interface.reference.object.mapper.is_some()
            || interface.reference.node.is_some()
            || all_parameters.len() != arguments.len().saturating_add(1)
            || !all_parameters.starts_with(arguments)
            || all_parameters.last().copied() != interface.this_type
            || arguments
                .iter()
                .filter(|argument| **argument == type_)
                .count()
                != 1
            || parameter
                .resolved_default_type
                .is_some_and(|default| default != bootstrap.no_constraint_type)
        {
            return false;
        }

        let authoritative_owner = match self.get_parent_of_symbol(owner) {
            Some(parent) => self
                .symbol(parent)
                .filter(|parent| parent.flags().intersects(SymbolFlags::MODULE))
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| self.symbol_table(exports))
                .and_then(|exports| exports.get(owner_record.name()))
                .and_then(|owner| self.get_merged_symbol(owner)),
            None => self
                .symbol_table(bootstrap.globals)
                .and_then(|globals| globals.get(owner_record.name()))
                .and_then(|owner| self.get_merged_symbol(owner)),
        };
        if authoritative_owner != Some(owner) {
            return false;
        }

        let mut seen_owner_declarations = HashSet::with_capacity(owner_declarations.len());
        let mut value_declaration = None;
        for declaration in owner_declarations {
            if !seen_owner_declarations.insert(*declaration) {
                return false;
            }
            match self.source_node_kind(*declaration) {
                Some(SyntaxKind::InterfaceDeclaration) => {}
                Some(SyntaxKind::VariableDeclaration)
                    if value_declaration.replace(*declaration).is_none() => {}
                _ => return false,
            }
        }
        if owner_record.value_declaration() != value_declaration
            || owner_record
                .flags()
                .contains(SymbolFlags::FUNCTION_SCOPED_VARIABLE)
                != value_declaration.is_some()
        {
            return false;
        }

        let mut expected_declarations = owner_declarations.iter().copied().filter(|declaration| {
            self.source_node_kind(*declaration) == Some(SyntaxKind::InterfaceDeclaration)
        });
        let mut seen = HashSet::with_capacity(declarations.len());
        for declaration in declarations {
            let Some(expected_owner) = expected_declarations.next() else {
                return false;
            };
            if !seen.insert(*declaration)
                || self.source_node_kind(*declaration) != Some(SyntaxKind::TypeParameter)
                || self.source_node_parent(*declaration)
                    != Some(SourceNodeParent::Parent(expected_owner))
            {
                return false;
            }

            let annotation = self.source_direct_type_annotation(*declaration);
            let consistent_constraint = match (annotation, parameter.constraint) {
                (None, None) => true,
                (None, Some(constraint)) => constraint == bootstrap.no_constraint_type,
                (Some(annotation), Some(constraint)) => {
                    constraint != bootstrap.no_constraint_type
                        && self.source_direct_type_annotation_is_exact(annotation, constraint)
                }
                (Some(_), None) => false,
            };
            if !consistent_constraint {
                return false;
            }
        }
        if expected_declarations.next().is_some() {
            return false;
        }

        let expected_base = parameter.constraint.unwrap_or(bootstrap.no_constraint_type);
        parameter
            .constrained
            .resolved_base_constraint
            .is_none_or(|base| base == expected_base)
    }

    /// Authenticates a fresh method parameter against its source and receiver mapper.
    #[allow(clippy::too_many_lines)] // Source, receiver, and fresh mapper form one identity proof.
    fn instantiated_interface_method_type_parameter_owner(
        &self,
        type_: TypeId,
        record: &TypeRecord,
        parameter: &super::type_records::TypeParameterData,
    ) -> Option<SemanticSymbolId> {
        let source = parameter.target?;
        let mapper = parameter.mapper?;
        let symbol = cached_ordinary_type_parameter_owner(self, source)?;
        let source_record = self.type_payload(source)?;
        let symbol_record = self.symbol(symbol)?;
        let [declaration] = symbol_record.declarations()? else {
            return None;
        };
        let SourceNodeParent::Parent(method_declaration) = self.source_node_parent(*declaration)?
        else {
            return None;
        };
        let signature_id = self
            .signature_links(method_declaration)?
            .resolved_signature
            .signature()?;
        let signature = self.signature(signature_id)?;
        let callable = self.interface_method_linked_type(signature_id)?;
        let method = self.type_payload(callable)?.symbol()?;
        let (_, owner_type) = self.authenticated_interface_method_owner(method)?;
        let TypeData::Interface(interface) = self.type_payload(owner_type)?.data() else {
            return None;
        };
        let interface_parameters = interface.reference.resolved_type_arguments.as_deref()?;
        let this_type = interface.this_type?;
        let TypeMapperApplication::Composite {
            first: fresh_mapper,
            second: owner_mapper,
        } = self.mapper_application(mapper, source)?
        else {
            return None;
        };
        let receiver = self.map_type(owner_mapper, this_type)?;
        let receiver_reference = validate_direct_generic_reference(self, receiver).ok()?;
        let mapper_sources = interface_parameters
            .iter()
            .copied()
            .chain(std::iter::once(this_type))
            .collect::<Vec<_>>();
        let mapper_targets = receiver_reference
            .type_arguments
            .iter()
            .copied()
            .chain(std::iter::once(receiver))
            .collect::<Vec<_>>();
        let variable_flags = ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
            | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES;
        if record.flags() != TypeFlags::TYPE_PARAMETER
            || record.object_flags() != ObjectFlags::NONE && record.object_flags() != variable_flags
            || record.symbol() != Some(symbol)
            || record.alias().is_some()
            || parameter.is_this_type
            || source_record.symbol() != Some(symbol)
            || symbol_record.flags() != SymbolFlags::TYPE_PARAMETER
            || self.source_node_kind(*declaration) != Some(SyntaxKind::TypeParameter)
            || self.source_node_kind(method_declaration) != Some(SyntaxKind::MethodSignature)
            || signature.declaration() != Some(method_declaration)
            || !signature.type_parameters().contains(&source)
            || !super::callable_sets::valid_declared_method_type_parameters(
                self,
                signature,
                method_declaration,
            )
            || interface_parameters.is_empty()
            || receiver_reference.target != owner_type
            || receiver_reference.type_arguments.len() != interface_parameters.len()
            || interface
                .all_type_parameters
                .as_deref()
                .is_none_or(|parameters| {
                    parameters.len() != interface_parameters.len() + 1
                        || !parameters.starts_with(interface_parameters)
                        || parameters.last().copied() != Some(this_type)
                })
            || self.type_mapper_has_exact_endpoints(owner_mapper, &mapper_sources, &mapper_targets)
                != Some(true)
        {
            return None;
        }

        let mut fresh_parameters = Vec::with_capacity(signature.type_parameters().len());
        let mut seen = HashSet::with_capacity(signature.type_parameters().len());
        for original in signature.type_parameters() {
            let fresh = self.map_type(fresh_mapper, *original)?;
            let fresh_record = self.type_payload(fresh)?;
            let TypeData::TypeParameter(fresh_data) = fresh_record.data() else {
                return None;
            };
            if fresh == *original
                || !seen.insert(fresh)
                || fresh_record.flags() != TypeFlags::TYPE_PARAMETER
                || fresh_record.object_flags() != ObjectFlags::NONE
                    && fresh_record.object_flags() != variable_flags
                || fresh_record.symbol() != self.type_payload(*original)?.symbol()
                || fresh_record.alias().is_some()
                || fresh_data.is_this_type
                || fresh_data.target != Some(*original)
                || fresh_data.mapper != Some(mapper)
            {
                return None;
            }
            fresh_parameters.push(fresh);
        }
        (fresh_parameters.contains(&type_)
            && self.type_mapper_has_exact_endpoints(
                fresh_mapper,
                signature.type_parameters(),
                &fresh_parameters,
            ) == Some(true))
        .then_some(symbol)
    }

    #[allow(clippy::too_many_arguments)] // Structural cycles and member visits need separate sets.
    fn validate_supported_record_mapped_union_constituent(
        &self,
        type_: TypeId,
        record: &TypeRecord,
        mapped: &super::type_records::MappedTypeData,
        array_validation: UnionArrayValidation<'_>,
        visiting: &mut HashSet<TypeId>,
        array_visited: &mut HashSet<TypeId>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        let invalid = || LiteralTypeCacheError::InvalidCachedUnion(type_);
        let unsupported = || LiteralTypeCacheError::UnsupportedUnionConstituent(type_);
        if !record
            .object_flags()
            .contains(ObjectFlags::INSTANTIATED_MAPPED)
        {
            return Err(unsupported());
        }

        let identity = record
            .alias()
            .and_then(|identity| self.type_alias(identity))
            .ok_or_else(invalid)?;
        let alias = identity.symbol().ok_or_else(invalid)?;
        let alias_record = self.symbol(alias).ok_or_else(invalid)?;
        if alias_record.name().as_utf8() != Some("Record") {
            return Err(unsupported());
        }
        let Some([key, value]) = identity.type_arguments() else {
            return Err(invalid());
        };
        let bootstrap = self.intrinsic_bootstrap.as_ref().ok_or_else(invalid)?;
        if *key != bootstrap.string_type {
            return Err(unsupported());
        }

        let target = mapped.object.target.ok_or_else(invalid)?;
        let links = self.type_alias_links(alias).ok_or_else(invalid)?;
        let parameters = links.type_parameters.as_deref().ok_or_else(invalid)?;
        if links.declared_type != Some(target)
            || links.instantiations.as_ref().is_none_or(|instantiations| {
                !instantiations.values().any(|cached| *cached == type_)
            })
            || self
                .validate_record_mapped_alias_instantiation(
                    alias,
                    target,
                    parameters,
                    &[*key, *value],
                    type_,
                )
                .is_err()
        {
            return Err(invalid());
        }

        let (projection, edges) = match validate_stored_callable_set(self, *value) {
            StoredCallableSetValidation::Valid {
                family: CallableFamily::FunctionType | CallableFamily::DeclaredCallSignatures,
                projection,
                edges,
            } => (projection, edges),
            StoredCallableSetValidation::Pending {
                family: CallableFamily::FunctionType,
            } if allowed_pending.contains(value) => {
                if !visiting.insert(type_) {
                    return Err(invalid());
                }
                let result = self
                    .validate_union_constituent_worker(
                        *key,
                        array_validation,
                        visiting,
                        array_visited,
                        allowed_pending,
                    )
                    .and_then(|()| {
                        self.validate_union_constituent_worker(
                            *value,
                            array_validation,
                            visiting,
                            array_visited,
                            allowed_pending,
                        )
                    });
                visiting.remove(&type_);
                return result;
            }
            StoredCallableSetValidation::Valid { .. }
            | StoredCallableSetValidation::NotCallable => return Err(unsupported()),
            StoredCallableSetValidation::Malformed { .. }
            | StoredCallableSetValidation::Pending { .. } => return Err(invalid()),
        };
        let [callable] = projection.call_signatures.as_ref() else {
            return Err(invalid());
        };
        if !projection.construct_signatures.is_empty()
            || callable.parameters.as_slice() != [bootstrap.string_type]
            || callable.rest_parameter.is_some()
            || callable.min_argument_count != 1
            || callable
                .return_type
                .is_some_and(|return_type| return_type != bootstrap.void_type)
        {
            return Err(unsupported());
        }

        if !visiting.insert(type_) {
            return Err(invalid());
        }
        let result = std::iter::once(*key).chain(edges).try_for_each(|nested| {
            self.validate_union_constituent_worker(
                nested,
                array_validation,
                visiting,
                array_visited,
                allowed_pending,
            )
        });
        visiting.remove(&type_);
        result
    }

    fn validate_union_constituent_worker(
        &self,
        type_: TypeId,
        array_validation: UnionArrayValidation<'_>,
        visiting: &mut HashSet<TypeId>,
        array_visited: &mut HashSet<TypeId>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        let Some(record) = self.type_payload(type_) else {
            return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
        };
        if record.flags().intersects(TypeFlags::ENUM_LIKE) {
            return validate_enum_type_union_constituent(self, type_).ok_or_else(|| {
                if matches!(record.data(), TypeData::Literal(_)) {
                    LiteralTypeCacheError::InvalidCachedLiteral(type_)
                } else {
                    LiteralTypeCacheError::InvalidCachedUnion(type_)
                }
            });
        }
        self.validate_union_class_declarations(type_, record)?;
        match record.data() {
            TypeData::Intrinsic(data) => {
                self.validate_supported_intrinsic(type_, record, &data.intrinsic_name)
            }
            TypeData::Literal(data) => {
                let regular = data.regular_type;
                let Some(regular_record) = self.type_payload(regular) else {
                    return Err(LiteralTypeCacheError::InvalidCachedLiteral(type_));
                };
                let TypeData::Literal(regular_data) = regular_record.data() else {
                    return Err(LiteralTypeCacheError::InvalidCachedLiteral(type_));
                };
                let expected_flags = match &data.value {
                    LiteralValue::String(_) => Some(TypeFlags::STRING_LITERAL),
                    LiteralValue::Number(value) if !value.is_nan() => {
                        Some(TypeFlags::NUMBER_LITERAL)
                    }
                    LiteralValue::Boolean(_) => Some(TypeFlags::BOOLEAN_LITERAL),
                    LiteralValue::BigInt(value)
                        if !(value.base10_value.is_empty() && value.negative)
                            && (value.base10_value.is_empty()
                                || !value.base10_value.starts_with('0')
                                    && value
                                        .base10_value
                                        .bytes()
                                        .all(|digit| digit.is_ascii_digit())) =>
                    {
                        Some(TypeFlags::BIG_INT_LITERAL)
                    }
                    LiteralValue::Number(_)
                    | LiteralValue::BigInt(_)
                    | LiteralValue::ComputedEnum => None,
                };
                if expected_flags != Some(record.flags())
                    || record.object_flags() != ObjectFlags::NONE
                    || record.symbol().is_some()
                    || record.alias().is_some()
                    || regular_record.flags() != record.flags()
                    || regular_record.object_flags() != ObjectFlags::NONE
                    || regular_record.symbol().is_some()
                    || regular_record.alias().is_some()
                    || regular_data.value != data.value
                    || regular_data.regular_type != regular
                    || type_ != regular
                        && (data.fresh_type != Some(type_)
                            || regular_data.fresh_type != Some(type_))
                {
                    return Err(LiteralTypeCacheError::InvalidCachedLiteral(type_));
                }
                let fresh = regular_data.fresh_type;
                if let Some(fresh) = fresh {
                    if fresh == regular {
                        return Err(LiteralTypeCacheError::InvalidCachedLiteral(type_));
                    }
                    let Some(fresh_record) = self.type_payload(fresh) else {
                        return Err(LiteralTypeCacheError::InvalidCachedLiteral(type_));
                    };
                    let TypeData::Literal(fresh_data) = fresh_record.data() else {
                        return Err(LiteralTypeCacheError::InvalidCachedLiteral(type_));
                    };
                    if fresh_record.flags() != record.flags()
                        || fresh_record.object_flags() != ObjectFlags::NONE
                        || fresh_record.symbol().is_some()
                        || fresh_record.alias().is_some()
                        || fresh_data.value != data.value
                        || fresh_data.regular_type != regular
                        || fresh_data.fresh_type != Some(fresh)
                    {
                        return Err(LiteralTypeCacheError::InvalidCachedLiteral(type_));
                    }
                }
                self.validate_supported_literal_identity(type_, regular, fresh, &data.value)?;
                Ok(())
            }
            TypeData::TypeParameter(parameter) => {
                if parameter.is_this_type
                    && super::classes::source_class_this_type_owner(self, type_).is_some()
                {
                    return Ok(());
                }
                let Some(symbol) =
                    cached_ordinary_type_parameter_owner(self, type_).or_else(|| {
                        self.instantiated_interface_method_type_parameter_owner(
                            type_, record, parameter,
                        )
                    })
                else {
                    return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
                };
                let Some(symbol_record) = self.symbol(symbol) else {
                    return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
                };
                let valid_declarations = match symbol_record.flags() {
                    SymbolFlags::TYPE_PARAMETER => {
                        matches!(
                            symbol_record.declarations(),
                            Some([declaration])
                                if self.source_node_kind(*declaration)
                                    == Some(SyntaxKind::TypeParameter)
                        ) || self.valid_supported_merged_type_parameter(type_, symbol, parameter)
                    }
                    flags if flags == SymbolFlags::TYPE_PARAMETER | SymbolFlags::TRANSIENT => {
                        self.valid_supported_merged_type_parameter(type_, symbol, parameter)
                    }
                    _ => false,
                };
                if !valid_declarations
                    || symbol_record.check_flags() != CheckFlags::NONE
                    || symbol_record.value_declaration().is_some()
                    || symbol_record.exports().is_some()
                    || symbol_record.export_symbol().is_some()
                    || self.get_merged_symbol(symbol) != Some(symbol)
                {
                    return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
                }
                Ok(())
            }
            TypeData::Object(object) => {
                if record.symbol().is_some_and(|owner| {
                    self.symbol(owner)
                        .is_some_and(|owner| owner.flags().intersects(SymbolFlags::ENUM))
                }) {
                    return validate_enum_value_union_constituent(self, type_)
                        .ok_or(LiteralTypeCacheError::InvalidCachedUnion(type_));
                }
                if self.validate_supported_unknown_empty_object(type_, record, object) {
                    return Ok(());
                }
                match validate_stored_callable_set(self, type_) {
                    StoredCallableSetValidation::Valid { edges, .. } => {
                        if !visiting.insert(type_) {
                            return Ok(());
                        }
                        for edge in edges {
                            self.validate_cached_array_capability_worker(
                                edge,
                                array_validation,
                                array_visited,
                                allowed_pending,
                            )?;
                        }
                        return Ok(());
                    }
                    StoredCallableSetValidation::Pending {
                        family:
                            CallableFamily::FunctionType | CallableFamily::DeclaredCallSignatures,
                    } if allowed_pending.contains(&type_) => {
                        return Ok(());
                    }
                    StoredCallableSetValidation::Malformed { .. }
                    | StoredCallableSetValidation::Pending { .. } => {
                        return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
                    }
                    StoredCallableSetValidation::NotCallable
                        if object.structured.signatures.is_some()
                            || object.structured.call_signature_count != 0 =>
                    {
                        return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
                    }
                    StoredCallableSetValidation::NotCallable => {}
                }
                match object_members::validate_resolved_declared_property_object(self, type_) {
                    object_members::DeclaredPropertyObjectValidation::Valid(_) => self
                        .validate_cached_array_capability_worker(
                            type_,
                            array_validation,
                            array_visited,
                            allowed_pending,
                        ),
                    object_members::DeclaredPropertyObjectValidation::NotDeclared => {
                        match object_members::validate_resolved_declared_property_type_graph(
                            self, type_,
                        ) {
                            object_members::DeclaredPropertyTypeGraphValidation::Traversable(_) => {
                                self.validate_cached_array_capability_worker(
                                    type_,
                                    array_validation,
                                    array_visited,
                                    allowed_pending,
                                )
                            }
                            object_members::DeclaredPropertyTypeGraphValidation::Opaque => {
                                if self.validate_supported_derived_property_object(
                                    type_,
                                    record,
                                    object,
                                    array_validation,
                                    visiting,
                                    array_visited,
                                    allowed_pending,
                                )? {
                                    Ok(())
                                } else {
                                    self.validate_supported_fresh_property_object(
                                        type_,
                                        record,
                                        object,
                                        array_validation,
                                        visiting,
                                        array_visited,
                                        allowed_pending,
                                    )
                                }
                            }
                            object_members::DeclaredPropertyTypeGraphValidation::Malformed => {
                                Err(LiteralTypeCacheError::InvalidCachedUnion(type_))
                            }
                        }
                    }
                    object_members::DeclaredPropertyObjectValidation::Malformed => {
                        Err(LiteralTypeCacheError::InvalidCachedUnion(type_))
                    }
                }
            }
            TypeData::Interface(interface) => {
                if let Some(edges) = self.lazy_default_library_interface_union_edges(
                    type_,
                    record,
                    interface,
                    array_validation.targets(),
                ) {
                    if !visiting.insert(type_) {
                        return Ok(());
                    }
                    for edge in edges {
                        self.validate_cached_array_capability_worker(
                            edge,
                            array_validation,
                            array_visited,
                            allowed_pending,
                        )?;
                    }
                    return Ok(());
                }
                match validate_stored_callable_set(self, type_) {
                    StoredCallableSetValidation::Valid { edges, .. } => {
                        if !visiting.insert(type_) {
                            return Ok(());
                        }
                        for edge in edges {
                            self.validate_cached_array_capability_worker(
                                edge,
                                array_validation,
                                array_visited,
                                allowed_pending,
                            )?;
                        }
                        return Ok(());
                    }
                    StoredCallableSetValidation::Pending {
                        family:
                            CallableFamily::FunctionType | CallableFamily::DeclaredCallSignatures,
                    } if allowed_pending.contains(&type_) => {
                        return Ok(());
                    }
                    StoredCallableSetValidation::Malformed { .. }
                    | StoredCallableSetValidation::Pending { .. } => {
                        return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
                    }
                    StoredCallableSetValidation::NotCallable
                        if interface.reference.object.structured.signatures.is_some()
                            || interface.reference.object.structured.call_signature_count != 0 =>
                    {
                        return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
                    }
                    StoredCallableSetValidation::NotCallable => {}
                }
                match validate_class_heritage_members(self, type_) {
                    ClassHeritageMembersValidation::Valid => {
                        return self.validate_cached_array_capability_worker(
                            type_,
                            array_validation,
                            array_visited,
                            allowed_pending,
                        );
                    }
                    ClassHeritageMembersValidation::Malformed => {
                        return Err(
                            if self.is_cold_class_union_constituent(type_, record, interface) {
                                LiteralTypeCacheError::UnsupportedUnionConstituent(type_)
                            } else {
                                LiteralTypeCacheError::InvalidCachedUnion(type_)
                            },
                        );
                    }
                    ClassHeritageMembersValidation::NotClass => {}
                }
                if self.direct_interface_heritage_provenance(type_).is_some() {
                    if validate_interface_heritage_members_with_array_targets(
                        self,
                        type_,
                        array_validation.targets(),
                    ) != InterfaceHeritageMembersValidation::Valid
                    {
                        return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
                    }
                    return self.validate_cached_array_capability_worker(
                        type_,
                        array_validation,
                        array_visited,
                        allowed_pending,
                    );
                }
                match object_members::validate_resolved_declared_property_object(self, type_) {
                    object_members::DeclaredPropertyObjectValidation::Valid(_) => self
                        .validate_cached_array_capability_worker(
                            type_,
                            array_validation,
                            array_visited,
                            allowed_pending,
                        ),
                    object_members::DeclaredPropertyObjectValidation::NotDeclared => {
                        match object_members::validate_resolved_declared_property_type_graph(
                            self, type_,
                        ) {
                            object_members::DeclaredPropertyTypeGraphValidation::Traversable(_) => {
                                self.validate_cached_array_capability_worker(
                                    type_,
                                    array_validation,
                                    array_visited,
                                    allowed_pending,
                                )
                            }
                            object_members::DeclaredPropertyTypeGraphValidation::Opaque => {
                                Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))
                            }
                            object_members::DeclaredPropertyTypeGraphValidation::Malformed => {
                                Err(LiteralTypeCacheError::InvalidCachedUnion(type_))
                            }
                        }
                    }
                    object_members::DeclaredPropertyObjectValidation::Malformed => {
                        Err(LiteralTypeCacheError::InvalidCachedUnion(type_))
                    }
                }
            }
            TypeData::Tuple(_) => self.validate_supported_canonical_tuple(
                type_,
                array_validation,
                visiting,
                array_visited,
                allowed_pending,
            ),
            TypeData::TypeReference(reference) => {
                let target = reference.object.target;
                if target.is_some_and(|target| {
                    matches!(
                        self.type_payload(target).map(TypeRecord::data),
                        Some(TypeData::Tuple(_))
                    )
                }) {
                    self.validate_supported_canonical_tuple(
                        type_,
                        array_validation,
                        visiting,
                        array_visited,
                        allowed_pending,
                    )
                } else if target
                    .and_then(|target| self.type_payload(target))
                    .is_some_and(|target| {
                        matches!(target.data(), TypeData::Interface(_))
                            && target.object_flags().contains(ObjectFlags::INTERFACE)
                            && target.symbol().is_some_and(|symbol| {
                                !self.symbol_is_registered_global_array(symbol)
                            })
                    })
                {
                    self.validate_supported_generic_interface_reference(
                        type_,
                        array_validation,
                        visiting,
                        array_visited,
                        allowed_pending,
                    )
                } else {
                    self.validate_supported_canonical_array(
                        type_,
                        array_validation,
                        visiting,
                        array_visited,
                        allowed_pending,
                    )
                }
            }
            TypeData::Mapped(mapped) => self.validate_supported_record_mapped_union_constituent(
                type_,
                record,
                mapped,
                array_validation,
                visiting,
                array_visited,
                allowed_pending,
            ),
            TypeData::IndexedAccess(indexed) => self.validate_supported_deferred_indexed_access(
                type_,
                record,
                indexed,
                array_validation,
                visiting,
                array_visited,
                allowed_pending,
            ),
            TypeData::Union(data) => {
                if !visiting.insert(type_) {
                    return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
                }
                self.validate_union_structure(type_)?;
                for constituent in &data.union.types {
                    self.validate_union_constituent_worker(
                        *constituent,
                        array_validation,
                        visiting,
                        array_visited,
                        allowed_pending,
                    )?;
                }
                let expected_flags = TypeFlags::UNION
                    | if data.union.types.len() == 2
                        && data.union.types.iter().all(|constituent| {
                            self.type_payload(*constituent).is_some_and(|record| {
                                record.flags().intersects(TypeFlags::BOOLEAN_LITERAL)
                            })
                        })
                    {
                        TypeFlags::BOOLEAN
                    } else {
                        TypeFlags::NONE
                    };
                if record.flags() != expected_flags {
                    return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
                }
                if let Some(origin) = data.origin {
                    self.validate_supported_union_origin(
                        type_,
                        origin,
                        &data.union.types,
                        array_validation,
                        visiting,
                        array_visited,
                        allowed_pending,
                    )?;
                }
                self.validate_supported_union_cache_identity(
                    type_,
                    record,
                    data,
                    array_validation,
                    array_visited,
                    allowed_pending,
                )?;
                visiting.remove(&type_);
                Ok(())
            }
            _ => Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_)),
        }
    }

    fn is_cold_class_union_constituent(
        &self,
        type_: TypeId,
        record: &TypeRecord,
        interface: &InterfaceTypeData,
    ) -> bool {
        let Some(symbol) = record.symbol() else {
            return false;
        };
        // A declared instance can exist before either side has class members.
        // Published members must still pass the complete class graph check.
        record.object_flags() == (ObjectFlags::CLASS | ObjectFlags::REFERENCE)
            && cached_class_type(self, symbol) == Ok(Some(type_))
            && self.symbol(symbol).is_some_and(|owner| {
                owner.flags().contains(SymbolFlags::CLASS)
                    && owner.check_flags() == CheckFlags::NONE
                    && owner.value_declaration().is_some_and(|declaration| {
                        matches!(
                            self.source_node_kind(declaration),
                            Some(SyntaxKind::ClassDeclaration | SyntaxKind::ClassExpression)
                        ) && owner
                            .declarations()
                            .is_some_and(|declarations| declarations.contains(&declaration))
                    })
            })
            && self.get_merged_symbol(symbol) == Some(symbol)
            && self.direct_class_heritage_provenance(type_).is_none()
            && !interface.base_types_resolved
            && interface.resolved_base_constructor_type.is_none()
            && interface.resolved_base_types.is_none()
            && !interface.declared_members_resolved
            && interface.declared_members.is_none()
            && interface.declared_call_signatures.is_none()
            && interface.declared_construct_signatures.is_none()
            && interface.declared_index_infos.is_none()
            && interface.reference.object.structured == StructuredTypeData::default()
            && self
                .value_symbol_links(symbol)
                .is_none_or(|links| links == &ValueSymbolLinks::default())
    }

    #[allow(clippy::too_many_arguments)] // Structural cycles and member visits need separate sets.
    fn validate_supported_union_origin(
        &self,
        union: TypeId,
        origin: TypeId,
        normalized: &[TypeId],
        array_validation: UnionArrayValidation<'_>,
        visiting: &mut HashSet<TypeId>,
        array_visited: &mut HashSet<TypeId>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        self.validate_union_origin_structure(union, origin)?;
        let Some(record) = self.type_payload(origin) else {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        };
        let TypeData::Union(data) = record.data() else {
            return if self.valid_index_union_origin(origin) {
                Ok(())
            } else {
                Err(LiteralTypeCacheError::InvalidCachedUnion(union))
            };
        };
        for constituent in &data.union.types {
            self.validate_union_constituent_worker(
                *constituent,
                array_validation,
                visiting,
                array_visited,
                allowed_pending,
            )?;
        }

        let mut flattened = Vec::new();
        let mut leaf_count = 0usize;
        let mut flattening = HashSet::new();
        for constituent in &data.union.types {
            self.flatten_supported_union_type(
                *constituent,
                &mut flattened,
                &mut leaf_count,
                &mut flattening,
            )?;
        }
        if leaf_count != normalized.len() || flattened != normalized {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(union));
        }
        Ok(())
    }

    fn flatten_supported_union_type(
        &self,
        type_: TypeId,
        flattened: &mut Vec<TypeId>,
        leaf_count: &mut usize,
        visiting: &mut HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        let record = self
            .type_payload(type_)
            .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
        if let TypeData::Union(data) = record.data() {
            if !visiting.insert(type_) {
                return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
            }
            for constituent in &data.union.types {
                self.flatten_supported_union_type(*constituent, flattened, leaf_count, visiting)?;
            }
            visiting.remove(&type_);
        } else {
            *leaf_count = leaf_count
                .checked_add(1)
                .ok_or(LiteralTypeCacheError::Capacity)?;
            self.insert_union_type(flattened, type_)?;
        }
        Ok(())
    }

    fn type_name_for_union_order(
        &self,
        type_: TypeId,
    ) -> Result<Option<(SemanticSymbolId, Vec<TypeId>)>, LiteralTypeCacheError> {
        let record = self
            .type_payload(type_)
            .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
        if let Some(alias) = record.alias() {
            let alias = self
                .type_alias(alias)
                .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
            let symbol = alias
                .symbol()
                .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
            return Ok(Some((
                symbol,
                alias.type_arguments().unwrap_or_default().to_vec(),
            )));
        }
        if record
            .flags()
            .intersects(TypeFlags::TYPE_PARAMETER | TypeFlags::STRING_MAPPING)
            || record
                .object_flags()
                .intersects(ObjectFlags::CLASS_OR_INTERFACE | ObjectFlags::REFERENCE)
        {
            Ok(record.symbol().map(|symbol| (symbol, Vec::new())))
        } else {
            Ok(None)
        }
    }

    fn compare_union_object_symbols(
        &self,
        left: TypeId,
        right: TypeId,
    ) -> Result<Ordering, LiteralTypeCacheError> {
        let left_type = self
            .type_payload(left)
            .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(left))?;
        let right_type = self
            .type_payload(right)
            .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(right))?;
        self.validate_union_class_declarations(left, left_type)?;
        self.validate_union_class_declarations(right, right_type)?;
        let left_symbol = left_type.symbol();
        let right_symbol = right_type.symbol();
        let (left_symbol, right_symbol) = match (left_symbol, right_symbol) {
            (left, right) if left == right => return Ok(Ordering::Equal),
            (Some(left), Some(right)) => (left, right),
            (Some(_), None) => return Ok(Ordering::Less),
            (None, Some(_)) => return Ok(Ordering::Greater),
            (None, None) => return Ok(Ordering::Equal),
        };
        let left_record = self
            .symbol(left_symbol)
            .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(left))?;
        let right_record = self
            .symbol(right_symbol)
            .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(right))?;
        let declarations = match (
            left_record.declarations().and_then(|nodes| nodes.first()),
            right_record.declarations().and_then(|nodes| nodes.first()),
        ) {
            (Some(left_node), Some(right_node)) => {
                let left_start = self
                    .source_node_start(*left_node)
                    .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(left))?;
                let right_start = self
                    .source_node_start(*right_node)
                    .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(right))?;
                let left_rank = self
                    .source_file_rank(left_node.file)
                    .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(left))?;
                let right_rank = self
                    .source_file_rank(right_node.file)
                    .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(right))?;
                left_rank
                    .cmp(&right_rank)
                    .then_with(|| left_start.cmp(&right_start))
            }
            (Some(_), None) => Ordering::Less,
            (None, Some(_)) => Ordering::Greater,
            (None, None) => Ordering::Equal,
        };
        Ok(declarations
            .then_with(|| {
                left_record
                    .name()
                    .as_bytes()
                    .cmp(right_record.name().as_bytes())
            })
            .then_with(|| left_symbol.cmp(&right_symbol)))
    }

    fn validate_union_class_declarations(
        &self,
        type_: TypeId,
        record: &TypeRecord,
    ) -> Result<(), LiteralTypeCacheError> {
        if record.flags().contains(TypeFlags::OBJECT)
            && record.symbol().is_some_and(|symbol| {
                self.symbol(symbol)
                    .is_some_and(|owner| owner.flags().contains(SymbolFlags::CLASS))
                    && !self.source_symbol_declarations_match(symbol)
            })
        {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
        }
        Ok(())
    }

    fn compare_union_type_lists_worker(
        &self,
        left: &[TypeId],
        right: &[TypeId],
        comparing: &mut HashSet<(TypeId, TypeId)>,
    ) -> Result<Ordering, LiteralTypeCacheError> {
        let lengths = left.len().cmp(&right.len());
        if lengths != Ordering::Equal {
            return Ok(lengths);
        }
        for (left, right) in left.iter().zip(right) {
            let ordering = self.compare_union_types_worker(*left, *right, comparing)?;
            if ordering != Ordering::Equal {
                return Ok(ordering);
            }
        }
        Ok(Ordering::Equal)
    }

    fn compare_union_types(
        &self,
        left: TypeId,
        right: TypeId,
    ) -> Result<Ordering, LiteralTypeCacheError> {
        self.compare_union_types_worker(left, right, &mut HashSet::new())
    }

    #[allow(clippy::too_many_lines)] // Keep flags, names, source symbols, and payloads in upstream order.
    fn compare_union_types_worker(
        &self,
        left: TypeId,
        right: TypeId,
        comparing: &mut HashSet<(TypeId, TypeId)>,
    ) -> Result<Ordering, LiteralTypeCacheError> {
        if left == right {
            return Ok(Ordering::Equal);
        }
        if !comparing.insert((left, right)) {
            return Err(LiteralTypeCacheError::InvalidCachedUnion(left));
        }
        let result = (|| {
            let left_record = self
                .type_payload(left)
                .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(left))?;
            let right_record = self
                .type_payload(right)
                .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(right))?;
            let flags = left_record.flags().cmp(&right_record.flags());
            if flags != Ordering::Equal {
                return Ok(flags);
            }

            match (
                self.type_name_for_union_order(left)?,
                self.type_name_for_union_order(right)?,
            ) {
                (Some((left_symbol, left_arguments)), Some((right_symbol, right_arguments))) => {
                    if left_symbol == right_symbol {
                        let arguments = self.compare_union_type_lists_worker(
                            &left_arguments,
                            &right_arguments,
                            comparing,
                        )?;
                        if arguments != Ordering::Equal {
                            return Ok(arguments);
                        }
                    } else {
                        let left_name = self
                            .symbol(left_symbol)
                            .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(left))?
                            .name();
                        let right_name = self
                            .symbol(right_symbol)
                            .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(right))?
                            .name();
                        let names = left_name.as_bytes().cmp(right_name.as_bytes());
                        if names != Ordering::Equal {
                            return Ok(names);
                        }
                    }
                }
                (Some(_), None) => return Ok(Ordering::Less),
                (None, Some(_)) => return Ok(Ordering::Greater),
                (None, None) => {}
            }

            if left_record.flags().contains(TypeFlags::OBJECT) {
                let symbols = self.compare_union_object_symbols(left, right)?;
                if symbols != Ordering::Equal {
                    return Ok(symbols);
                }
            }

            match (left_record.data(), right_record.data()) {
                (TypeData::Literal(left_data), TypeData::Literal(right_data)) => {
                    let values = match (&left_data.value, &right_data.value) {
                        (LiteralValue::String(left), LiteralValue::String(right)) => {
                            left.cmp(right)
                        }
                        (LiteralValue::Number(left), LiteralValue::Number(right)) => left
                            .partial_cmp(right)
                            .ok_or(LiteralTypeCacheError::InvalidValue)?,
                        (LiteralValue::Boolean(left), LiteralValue::Boolean(right)) => {
                            left.cmp(right)
                        }
                        _ => Ordering::Equal,
                    };
                    if values != Ordering::Equal {
                        return Ok(values);
                    }
                }
                (TypeData::Union(left_data), TypeData::Union(right_data)) => {
                    let origins = match (left_data.origin, right_data.origin) {
                        (None, None) => self.compare_union_type_lists_worker(
                            &left_data.union.types,
                            &right_data.union.types,
                            comparing,
                        )?,
                        (None, Some(_)) => Ordering::Greater,
                        (Some(_), None) => Ordering::Less,
                        (Some(left), Some(right)) => {
                            self.compare_union_types_worker(left, right, comparing)?
                        }
                    };
                    if origins != Ordering::Equal {
                        return Ok(origins);
                    }
                }
                _ => {}
            }
            Ok(left.get().cmp(&right.get()))
        })();
        comparing.remove(&(left, right));
        result
    }

    fn insert_union_type(
        &self,
        types: &mut Vec<TypeId>,
        candidate: TypeId,
    ) -> Result<(), LiteralTypeCacheError> {
        for (index, current) in types.iter().copied().enumerate() {
            match self.compare_union_types(current, candidate)? {
                Ordering::Less => {}
                Ordering::Equal => return Ok(()),
                Ordering::Greater => {
                    types.insert(index, candidate);
                    return Ok(());
                }
            }
        }
        types.push(candidate);
        Ok(())
    }

    fn add_types_to_union(
        &self,
        type_set: &mut Vec<TypeId>,
        includes: &mut TypeFlags,
        types: &[TypeId],
    ) -> Result<(), LiteralTypeCacheError> {
        let bootstrap = self
            .intrinsic_bootstrap
            .as_ref()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        for type_ in types {
            let record = self
                .type_payload(*type_)
                .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(*type_))?;
            if let TypeData::Union(data) = record.data() {
                if record.alias().is_some() || data.origin.is_some() {
                    *includes |= TypeFlags::UNION;
                }
                self.add_types_to_union(type_set, includes, &data.union.types)?;
                continue;
            }
            let flags = record.flags();
            if flags.intersects(TypeFlags::NEVER) {
                continue;
            }
            *includes |= flags & TypeFlags::INCLUDES_MASK;
            if flags.intersects(TypeFlags::INSTANTIABLE) {
                *includes |= TypeFlags::INCLUDES_INSTANTIABLE;
            }
            if *type_ == bootstrap.wildcard_type {
                *includes |= TypeFlags::INCLUDES_WILDCARD;
            }
            if *type_ == bootstrap.error_type
                || flags.intersects(TypeFlags::ANY) && record.alias().is_some()
            {
                *includes |= TypeFlags::INCLUDES_ERROR;
            }
            if !bootstrap.options.strict_null_checks && flags.intersects(TypeFlags::NULLABLE) {
                if !record
                    .object_flags()
                    .contains(ObjectFlags::CONTAINS_WIDENING_TYPE)
                {
                    *includes |= TypeFlags::INCLUDES_NON_WIDENING_TYPE;
                }
            } else {
                self.insert_union_type(type_set, *type_)?;
            }
        }
        Ok(())
    }

    fn remove_redundant_literal_union_types(
        &self,
        types: &mut Vec<TypeId>,
        includes: TypeFlags,
        reduce_void_undefined: bool,
    ) -> Result<(), LiteralTypeCacheError> {
        let mut index = types.len();
        while index != 0 {
            index -= 1;
            let candidate = types[index];
            let record = self.type_payload(candidate).ok_or(
                LiteralTypeCacheError::UnsupportedUnionConstituent(candidate),
            )?;
            let flags = record.flags();
            let fresh_redundant = if let TypeData::Literal(data) = record.data() {
                data.fresh_type == Some(candidate)
                    && data.regular_type != candidate
                    && types.contains(&data.regular_type)
            } else {
                false
            };
            if flags.intersects(TypeFlags::STRING_LITERAL) && includes.intersects(TypeFlags::STRING)
                || flags.intersects(TypeFlags::NUMBER_LITERAL)
                    && includes.intersects(TypeFlags::NUMBER)
                || flags.intersects(TypeFlags::BIG_INT_LITERAL)
                    && includes.intersects(TypeFlags::BIG_INT)
                || reduce_void_undefined
                    && flags.intersects(TypeFlags::UNDEFINED)
                    && includes.intersects(TypeFlags::VOID)
                || fresh_redundant
            {
                types.remove(index);
            }
        }
        Ok(())
    }

    fn is_supported_empty_property_object(&self, type_: TypeId) -> bool {
        self.type_payload(type_).is_some_and(|record| {
            record.flags().intersects(TypeFlags::OBJECT)
                && matches!(
                    record.data(),
                    TypeData::Object(object) if object.structured.properties.is_none()
                )
        })
    }

    fn is_authenticated_symbol_owned_empty_anonymous_object(&self, type_: TypeId) -> bool {
        self.type_payload(type_).is_some_and(|record| {
            let Some(owner) = record.symbol() else {
                return false;
            };
            let Some(owner_record) = self.symbol(owner) else {
                return false;
            };
            let TypeData::Object(object) = record.data() else {
                return false;
            };
            record.flags() == TypeFlags::OBJECT
                && record
                    .object_flags()
                    .contains(ObjectFlags::ANONYMOUS | ObjectFlags::MEMBERS_RESOLVED)
                && self.get_merged_symbol(owner) == Some(owner)
                && owner_record
                    .flags()
                    .intersects(SymbolFlags::OBJECT_LITERAL | SymbolFlags::TYPE_LITERAL)
                && owner_record.check_flags() == CheckFlags::NONE
                && Self::valid_supported_property_object_tail(object)
                && object
                    .structured
                    .properties
                    .as_ref()
                    .is_none_or(Vec::is_empty)
                && object.structured.members.is_none_or(|members| {
                    self.symbol_table(members)
                        .is_some_and(ts_binder::semantic::SymbolTable::is_empty)
                })
        })
    }

    fn subtype_reduction_unit_property(
        &self,
        type_: TypeId,
        expected_name: Option<&EscapedName>,
        global_types: Option<&CanonicalGlobalTypes>,
    ) -> Result<Option<(EscapedName, TypeId)>, LiteralTypeCacheError> {
        let record = self
            .type_payload(type_)
            .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(type_))?;
        if !record.flags().intersects(TypeFlags::OBJECT) {
            return Ok(None);
        }
        if !record.object_flags().contains(ObjectFlags::OBJECT_LITERAL) {
            match object_members::validate_resolved_declared_property_object(self, type_) {
                object_members::DeclaredPropertyObjectValidation::Valid(_) => {}
                object_members::DeclaredPropertyObjectValidation::Malformed => {
                    return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
                }
                object_members::DeclaredPropertyObjectValidation::NotDeclared => {
                    let derived = match global_types {
                        Some(global_types) => self
                            .validate_derived_object_literal_with_global_types(type_, global_types),
                        None => self.validate_derived_object_literal_for_relation(type_),
                    };
                    match derived {
                        DerivedObjectLiteralValidation::Valid { .. } => {}
                        DerivedObjectLiteralValidation::Invalid => {
                            return Err(LiteralTypeCacheError::InvalidCachedUnion(type_));
                        }
                        DerivedObjectLiteralValidation::NotDerived => return Ok(None),
                    }
                }
            }
        }

        let properties = record
            .data()
            .structured()
            .ok_or(LiteralTypeCacheError::InvalidCachedUnion(type_))?
            .properties
            .as_deref()
            .unwrap_or_default();
        for property in properties {
            let symbol = self
                .symbol(*property)
                .ok_or(LiteralTypeCacheError::InvalidCachedUnion(type_))?;
            if expected_name.is_some_and(|name| symbol.name() != name.as_ref()) {
                continue;
            }
            let property_type = self
                .value_symbol_links(*property)
                .and_then(|links| links.resolved_type)
                .ok_or(LiteralTypeCacheError::InvalidCachedUnion(type_))?;
            let property_record = self
                .type_payload(property_type)
                .ok_or(LiteralTypeCacheError::InvalidCachedUnion(type_))?;
            if !property_record.flags().intersects(TypeFlags::UNIT) {
                if expected_name.is_some() {
                    return Ok(None);
                }
                continue;
            }

            self.validate_union_constituent(property_type)?;
            let regular = match property_record.data() {
                TypeData::Literal(literal) => literal.regular_type,
                _ => property_type,
            };
            return Ok(Some((symbol.name().to_owned(), regular)));
        }
        Ok(None)
    }

    fn remove_union_subtypes(
        &mut self,
        types: &mut Vec<TypeId>,
        has_object_types: bool,
        global_types: Option<&CanonicalGlobalTypes>,
    ) -> Result<(), LiteralTypeCacheError> {
        // This is the dependency-closed `removeSubtypes` prefix for expression
        // unions. The validator admits primitives, literals, recursively
        // canonical unions, and fresh property objects, so the upstream type
        // parameter and class-derivation branches are unreachable here. The
        // unit-property shortcut is limited to authenticated fresh, declared,
        // and derived property objects. Global-aware calls additionally admit
        // canonical arrays and preserve nested derived-array provenance. The
        // one mixed relation independent of generic Array members is Array ->
        // regularized empty object; every nonempty mixed surface remains typed
        // unavailable rather than becoming a negative answer.
        if types.len() < 2 {
            return Ok(());
        }
        if let Some(global_types) = global_types {
            self.preflight_expression_union_array_object_pairs(types, global_types)?;
        }
        let (empty_object_type, unknown_empty_object_type) = {
            let bootstrap = self
                .intrinsic_bootstrap
                .as_ref()
                .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
            (
                bootstrap.empty_object_type,
                bootstrap.unknown_empty_object_type,
            )
        };
        let has_empty_object = has_object_types
            && types
                .iter()
                .copied()
                .any(|type_| self.is_supported_empty_property_object(type_));
        let original_length = types.len();
        let mut index = original_length;
        let mut comparison_count = 0usize;
        while index != 0 {
            index -= 1;
            let source = types[index];
            let source_flags = self
                .type_payload(source)
                .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(source))?
                .flags();
            if !has_empty_object && !source_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
            {
                continue;
            }

            let discriminant = self.subtype_reduction_unit_property(source, None, global_types)?;
            let candidates = types.clone();
            for target in candidates {
                if source == target {
                    continue;
                }
                if comparison_count == 100_000 {
                    let processed = original_length - index;
                    let estimated_count = (comparison_count / processed) * original_length;
                    if estimated_count > 1_000_000 {
                        return Err(LiteralTypeCacheError::Capacity);
                    }
                }
                comparison_count = comparison_count
                    .checked_add(1)
                    .ok_or(LiteralTypeCacheError::Capacity)?;
                if let Some((name, source_type)) = &discriminant
                    && self
                        .subtype_reduction_unit_property(target, Some(name), global_types)?
                        .is_some_and(|(_, target_type)| *source_type != target_type)
                {
                    continue;
                }
                if (source == empty_object_type || source == unknown_empty_object_type)
                    && self.is_authenticated_symbol_owned_empty_anonymous_object(target)
                {
                    continue;
                }
                let related = match global_types {
                    Some(global_types) => self.is_type_strict_subtype_of_with_global_types(
                        source,
                        target,
                        global_types,
                    ),
                    None => self.is_type_strict_subtype_of(source, target),
                }
                .map_err(|_| LiteralTypeCacheError::UnsupportedUnionConstituent(source))?;
                if related {
                    types.remove(index);
                    break;
                }
            }
        }
        Ok(())
    }

    fn collect_named_unions(
        &self,
        types: &[TypeId],
        named: &mut Vec<TypeId>,
        visiting: &mut HashSet<TypeId>,
    ) -> Result<(), LiteralTypeCacheError> {
        for type_ in types {
            let record = self
                .type_payload(*type_)
                .ok_or(LiteralTypeCacheError::UnsupportedUnionConstituent(*type_))?;
            let TypeData::Union(data) = record.data() else {
                continue;
            };
            if !visiting.insert(*type_) {
                return Err(LiteralTypeCacheError::InvalidCachedUnion(*type_));
            }
            if record.alias().is_some()
                || data.origin.is_some_and(|origin| {
                    self.type_payload(origin)
                        .is_some_and(|origin| !origin.flags().intersects(TypeFlags::UNION))
                })
            {
                if !named.contains(type_) {
                    named.push(*type_);
                }
            } else if let Some(origin) = data.origin {
                let Some(TypeData::Union(origin)) = self.type_payload(origin).map(TypeRecord::data)
                else {
                    return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(*type_));
                };
                self.collect_named_unions(&origin.union.types, named, visiting)?;
            }
            visiting.remove(type_);
        }
        Ok(())
    }

    fn union_contains_type(&self, union: TypeId, type_: TypeId) -> bool {
        self.type_payload(union).is_some_and(|record| {
            matches!(record.data(), TypeData::Union(data) if data.union.types.contains(&type_))
        })
    }

    fn union_propagating_flags(&self, types: &[TypeId]) -> ObjectFlags {
        types.iter().fold(ObjectFlags::NONE, |flags, type_| {
            let Some(record) = self.type_payload(*type_) else {
                return flags;
            };
            if record.flags().intersects(TypeFlags::NULLABLE) {
                flags
            } else {
                flags | record.object_flags()
            }
        }) & ObjectFlags::PROPAGATING_FLAGS
    }

    /// Constructs an anonymous expression union using the requested pinned
    /// reduction mode. Empty inputs reduce to the canonical `never` identity.
    #[cfg(test)]
    pub(super) fn expression_union_type(
        &mut self,
        types: &[TypeId],
        reduction: UnionReduction,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        let mut prepared = self.prepare_type_query_types(&[], &[], &[], 1, 0)?;
        self.union_type_prepared(
            types,
            reduction,
            None,
            &mut prepared,
            UnionArrayValidation::None,
        )
    }

    /// Constructs an expression union with authoritative global-array
    /// identities available to constituent validation and subtype reduction.
    pub(super) fn expression_union_type_with_global_types(
        &mut self,
        global_types: &CanonicalGlobalTypes,
        types: &[TypeId],
        reduction: UnionReduction,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        let mut prepared =
            self.prepare_type_query_types_with_global_types(&[], &[], &[], 1, 0, global_types)?;
        self.union_type_prepared(
            types,
            reduction,
            None,
            &mut prepared,
            UnionArrayValidation::GlobalTypes(global_types),
        )
    }

    #[cfg(test)]
    pub(super) fn literal_union_type(
        &mut self,
        types: &[TypeId],
        alias_symbol: Option<SemanticSymbolId>,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        let mut prepared =
            self.prepare_type_query_types(&[], &[], &[], 1, usize::from(alias_symbol.is_some()))?;
        self.literal_union_type_prepared(types, alias_symbol, &mut prepared)
    }

    pub(super) fn literal_union_type_prepared(
        &mut self,
        types: &[TypeId],
        alias_symbol: Option<SemanticSymbolId>,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        self.literal_union_type_with_alias_prepared(
            types,
            alias_symbol.map(|symbol| (symbol, &[][..])),
            prepared,
            None,
        )
    }

    pub(super) fn preflight_prepared_union_constituent(
        &self,
        type_: TypeId,
        prepared: &PreparedTypeQueryTypes,
        globals: Option<&CanonicalGlobalTypes>,
    ) -> Result<(), LiteralTypeCacheError> {
        if prepared.store != self.id()
            || prepared.array_targets != globals.map(CanonicalArrayTargets::from_global_types)
        {
            return Err(LiteralTypeCacheError::InvalidPreparedQuery);
        }
        self.validate_union_constituent_worker(
            type_,
            UnionArrayValidation::from_global_types(globals),
            &mut HashSet::new(),
            &mut HashSet::new(),
            &prepared.pending_function_types,
        )
    }

    pub(super) fn literal_union_type_prepared_with_global_types(
        &mut self,
        global_types: &CanonicalGlobalTypes,
        types: &[TypeId],
        alias_symbol: Option<SemanticSymbolId>,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        self.literal_union_type_with_alias_prepared(
            types,
            alias_symbol.map(|symbol| (symbol, &[][..])),
            prepared,
            Some(global_types),
        )
    }

    /// Keeps the alias symbol and ordered arguments in the canonical union key.
    pub(super) fn literal_union_type_with_alias_prepared(
        &mut self,
        types: &[TypeId],
        alias: Option<(SemanticSymbolId, &[TypeId])>,
        prepared: &mut PreparedTypeQueryTypes,
        global_types: Option<&CanonicalGlobalTypes>,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        self.union_type_prepared(
            types,
            UnionReduction::Literal,
            alias.map(|(symbol, arguments)| UnionAliasCacheKey::new(symbol, arguments)),
            prepared,
            UnionArrayValidation::from_global_types(global_types),
        )
    }

    pub(super) fn literal_union_type_with_alias_and_array_targets(
        &mut self,
        types: &[TypeId],
        alias: Option<(SemanticSymbolId, &[TypeId])>,
        targets: Option<CanonicalArrayTargets>,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        let mut prepared = self.prepare_type_query_types_worker(
            &[],
            &[],
            &[],
            1,
            usize::from(alias.is_some()),
            targets.map_or(UnionArrayValidation::None, UnionArrayValidation::Targets),
            &[],
            0,
            0,
        )?;
        self.union_type_prepared(
            types,
            UnionReduction::Literal,
            alias.map(|(symbol, arguments)| UnionAliasCacheKey::new(symbol, arguments)),
            &mut prepared,
            targets.map_or(UnionArrayValidation::None, UnionArrayValidation::Targets),
        )
    }

    /// Looks up the result of literal union construction without publishing types or aliases.
    pub(super) fn cached_literal_union_type_with_alias(
        &self,
        types: &[TypeId],
        alias: Option<(SemanticSymbolId, &[TypeId])>,
        targets: Option<CanonicalArrayTargets>,
    ) -> Result<Option<TypeId>, LiteralTypeCacheError> {
        self.cached_literal_union_type_with_alias_worker(
            types,
            alias,
            Some(targets.map_or(UnionArrayValidation::None, UnionArrayValidation::Targets)),
        )
    }

    /// Reads an annotation union after its caller validates each source constituent.
    /// Reuses normal reduction and cache checks without traversing unused member types.
    pub(super) fn cached_annotation_union_type(
        &self,
        types: &[TypeId],
        alias: Option<(SemanticSymbolId, &[TypeId])>,
    ) -> Result<Option<TypeId>, LiteralTypeCacheError> {
        self.cached_literal_union_type_with_alias_worker(types, alias, None)
    }

    fn cached_literal_union_type_with_alias_worker(
        &self,
        types: &[TypeId],
        alias: Option<(SemanticSymbolId, &[TypeId])>,
        validation: Option<UnionArrayValidation<'_>>,
    ) -> Result<Option<TypeId>, LiteralTypeCacheError> {
        let alias = alias.map(|(symbol, arguments)| UnionAliasCacheKey::new(symbol, arguments));
        if !self.valid_union_alias_key(alias.as_ref()) {
            return Err(alias.map_or(LiteralTypeCacheError::InvalidValue, |alias| {
                LiteralTypeCacheError::InvalidUnionAlias(alias.symbol)
            }));
        }
        if let Some(validation) = validation {
            if let Some(alias) = alias.as_ref() {
                let mut visited = HashSet::new();
                for argument in &alias.type_arguments {
                    self.validate_cached_array_capability_worker(
                        *argument,
                        validation,
                        &mut visited,
                        &HashSet::new(),
                    )?;
                }
            }
            for type_ in types {
                self.validate_union_constituent_worker(
                    *type_,
                    validation,
                    &mut HashSet::new(),
                    &mut HashSet::new(),
                    &HashSet::new(),
                )?;
            }
        }
        if let [type_] = types {
            return Ok(Some(*type_));
        }
        let plan = match self.normalize_union_members(types, UnionReduction::Literal)? {
            UnionMembersPlan::Existing(existing) => UnionPlan::Existing(existing),
            UnionMembersPlan::Members {
                types: normalized,
                includes,
            } => self.finish_union_type_plan(
                types,
                normalized,
                includes,
                UnionReduction::Literal,
                alias,
                true,
            )?,
        };
        match plan {
            UnionPlan::Existing(existing) => Ok(Some(existing)),
            UnionPlan::Union {
                types,
                alias,
                origin,
                ..
            } => {
                let key = UnionTypeCacheKey {
                    types,
                    alias,
                    origin: origin.map(|origin| match origin {
                        UnionOriginPlan::DenormalizedUnion(types) => {
                            UnionOriginCacheKey::DenormalizedUnion(types)
                        }
                        UnionOriginPlan::ExistingIndex(index) => UnionOriginCacheKey::Index(index),
                    }),
                };
                let cached = self
                    .intrinsic_bootstrap
                    .as_ref()
                    .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?
                    .union_types
                    .get(&key)
                    .copied();
                if let Some(cached) = cached {
                    if let Some(validation) = validation {
                        self.validate_union_cache_entry(
                            &key,
                            cached,
                            validation,
                            &mut HashSet::new(),
                            &HashSet::new(),
                        )?;
                    } else {
                        self.validate_union_cache_entry_metadata(&key, cached)?;
                    }
                }
                Ok(cached)
            }
        }
    }

    /// Constructs the pinned `getLiteralTypeFromProperties` union shape for
    /// a previously allocated `newIndexType(target, IndexFlagsNone)` origin.
    ///
    /// The explicit origin deliberately bypasses the union-of-union fast path
    /// and named-union origin synthesis, matching `getUnionTypeEx(...,
    /// origin)` in the pinned checker. The caller must allocate the index
    /// shell only after the shared query preflight; one union operation
    /// reserves enough type capacity for that shell and the normalized union.
    pub(super) fn literal_union_type_prepared_with_index_origin(
        &mut self,
        types: &[TypeId],
        origin: TypeId,
        prepared: &mut PreparedTypeQueryTypes,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        prepared.consume_union(self.id(), false, None)?;
        if !prepared.pending_function_types.is_empty() {
            self.mark_union_cache_validation_dirty();
        }
        if !self.valid_index_union_origin(origin) {
            return Err(LiteralTypeCacheError::InvalidValue);
        }
        for type_ in types {
            self.validate_union_constituent_worker(
                *type_,
                UnionArrayValidation::None,
                &mut HashSet::new(),
                &mut HashSet::new(),
                &prepared.pending_function_types,
            )?;
        }
        if types.is_empty() {
            return self
                .intrinsic_bootstrap
                .as_ref()
                .map(|bootstrap| bootstrap.never_type)
                .ok_or(LiteralTypeCacheError::BootstrapUninitialized);
        }
        if types.len() == 1 {
            return Ok(types[0]);
        }
        match self.plan_union_type(types, UnionReduction::Literal, None, None, false)? {
            UnionPlan::Existing(existing) => Ok(existing),
            UnionPlan::Union {
                types,
                object_flags,
                alias: None,
                ..
            } => self.union_type_from_sorted_list(
                types,
                object_flags,
                None,
                Some(UnionOriginPlan::ExistingIndex(origin)),
                UnionArrayValidation::None,
                &prepared.pending_function_types,
            ),
            UnionPlan::Union { alias: Some(_), .. } => Err(LiteralTypeCacheError::InvalidValue),
        }
    }

    fn union_type_prepared(
        &mut self,
        types: &[TypeId],
        reduction: UnionReduction,
        alias: Option<UnionAliasCacheKey>,
        prepared: &mut PreparedTypeQueryTypes,
        array_validation: UnionArrayValidation<'_>,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        let array_targets = array_validation.targets();
        prepared.consume_union(self.id(), alias.is_some(), array_targets)?;
        if !prepared.pending_function_types.is_empty() {
            self.mark_union_cache_validation_dirty();
        }
        for type_ in types {
            self.validate_union_constituent_worker(
                *type_,
                array_validation,
                &mut HashSet::new(),
                &mut HashSet::new(),
                &prepared.pending_function_types,
            )?;
        }
        if !self.valid_union_alias_key(alias.as_ref()) {
            return Err(alias.map_or(LiteralTypeCacheError::InvalidValue, |alias| {
                LiteralTypeCacheError::InvalidUnionAlias(alias.symbol)
            }));
        }
        if let Some(alias) = alias.as_ref() {
            let mut visited = HashSet::new();
            for argument in &alias.type_arguments {
                self.validate_cached_array_capability_worker(
                    *argument,
                    array_validation,
                    &mut visited,
                    &prepared.pending_function_types,
                )?;
            }
        }
        if types.is_empty() {
            return self
                .intrinsic_bootstrap
                .as_ref()
                .map(|bootstrap| bootstrap.never_type)
                .ok_or(LiteralTypeCacheError::BootstrapUninitialized);
        }
        if types.len() == 1 {
            return Ok(types[0]);
        }

        let first_is_union = self
            .type_payload(types[0])
            .is_some_and(|record| record.flags().intersects(TypeFlags::UNION));
        let second_is_union = self
            .type_payload(types[1])
            .is_some_and(|record| record.flags().intersects(TypeFlags::UNION));
        let union_of_union_key =
            (types.len() == 2 && (first_is_union || second_is_union)).then(|| {
                let (first, second) = if types[0] < types[1] {
                    (types[0], types[1])
                } else {
                    (types[1], types[0])
                };
                UnionOfUnionCacheKey {
                    first,
                    second,
                    reduction,
                    alias: alias.clone(),
                }
            });
        if let Some(key) = union_of_union_key.as_ref()
            && let Some(cached) = self
                .intrinsic_bootstrap
                .as_ref()
                .and_then(|bootstrap| bootstrap.union_of_union_types.get(key))
                .copied()
        {
            self.validate_union_of_union_cache_entry(
                key.clone(),
                cached,
                array_validation,
                &prepared.pending_function_types,
            )?;
            return Ok(cached);
        }

        let result = self.union_type_worker(
            types,
            reduction,
            alias,
            array_validation,
            &prepared.pending_function_types,
        )?;
        if let Some(key) = union_of_union_key {
            let bootstrap = self
                .intrinsic_bootstrap
                .as_mut()
                .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
            bootstrap.union_of_union_types.insert(key, result);
        }
        Ok(result)
    }

    fn union_type_worker(
        &mut self,
        types: &[TypeId],
        reduction: UnionReduction,
        alias: Option<UnionAliasCacheKey>,
        array_validation: UnionArrayValidation<'_>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        match self.plan_union_type(
            types,
            reduction,
            alias,
            array_validation.global_types(),
            true,
        )? {
            UnionPlan::Existing(existing) => Ok(existing),
            UnionPlan::Union {
                types,
                object_flags,
                alias,
                origin,
            } => self.union_type_from_sorted_list(
                types,
                object_flags,
                alias,
                origin,
                array_validation,
                allowed_pending,
            ),
        }
    }

    fn plan_union_type(
        &mut self,
        types: &[TypeId],
        reduction: UnionReduction,
        alias: Option<UnionAliasCacheKey>,
        global_types: Option<&CanonicalGlobalTypes>,
        synthesize_origin: bool,
    ) -> Result<UnionPlan, LiteralTypeCacheError> {
        let (mut normalized, includes) = match self.normalize_union_members(types, reduction)? {
            UnionMembersPlan::Existing(existing) => return Ok(UnionPlan::Existing(existing)),
            UnionMembersPlan::Members { types, includes } => (types, includes),
        };
        if reduction == UnionReduction::Subtype {
            self.remove_union_subtypes(
                &mut normalized,
                includes.intersects(TypeFlags::OBJECT),
                global_types,
            )?;
        }
        self.finish_union_type_plan(
            types,
            normalized,
            includes,
            reduction,
            alias,
            synthesize_origin,
        )
    }

    fn normalize_union_members(
        &self,
        types: &[TypeId],
        reduction: UnionReduction,
    ) -> Result<UnionMembersPlan, LiteralTypeCacheError> {
        let mut type_set = Vec::with_capacity(types.len());
        let mut includes = TypeFlags::NONE;
        self.add_types_to_union(&mut type_set, &mut includes, types)?;
        let (wildcard_type, error_type, any_type, unknown_type, undefined_type, missing_type) = {
            let bootstrap = self
                .intrinsic_bootstrap
                .as_ref()
                .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
            (
                bootstrap.wildcard_type,
                bootstrap.error_type,
                bootstrap.any_type,
                bootstrap.unknown_type,
                bootstrap.undefined_type,
                bootstrap.missing_type,
            )
        };
        if reduction != UnionReduction::None {
            if includes.intersects(TypeFlags::ANY_OR_UNKNOWN) {
                if includes.intersects(TypeFlags::ANY) {
                    return Ok(UnionMembersPlan::Existing(
                        if includes.intersects(TypeFlags::INCLUDES_WILDCARD) {
                            wildcard_type
                        } else if includes.intersects(TypeFlags::INCLUDES_ERROR) {
                            error_type
                        } else {
                            any_type
                        },
                    ));
                }
                return Ok(UnionMembersPlan::Existing(unknown_type));
            }
            if includes.intersects(TypeFlags::UNDEFINED)
                && type_set.len() >= 2
                && type_set[0] == undefined_type
                && type_set[1] == missing_type
            {
                type_set.remove(1);
            }
            if includes.intersects(
                TypeFlags::ENUM
                    | TypeFlags::LITERAL
                    | TypeFlags::UNIQUE_ES_SYMBOL
                    | TypeFlags::TEMPLATE_LITERAL
                    | TypeFlags::STRING_MAPPING,
            ) || includes.intersects(TypeFlags::VOID)
                && includes.intersects(TypeFlags::UNDEFINED)
            {
                self.remove_redundant_literal_union_types(
                    &mut type_set,
                    includes,
                    reduction == UnionReduction::Subtype,
                )?;
            }
        }
        Ok(UnionMembersPlan::Members {
            types: type_set,
            includes,
        })
    }

    fn finish_union_type_plan(
        &self,
        types: &[TypeId],
        type_set: Vec<TypeId>,
        includes: TypeFlags,
        reduction: UnionReduction,
        alias: Option<UnionAliasCacheKey>,
        synthesize_origin: bool,
    ) -> Result<UnionPlan, LiteralTypeCacheError> {
        if type_set.is_empty() {
            let bootstrap = self
                .intrinsic_bootstrap
                .as_ref()
                .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
            return Ok(UnionPlan::Existing(if reduction == UnionReduction::None {
                bootstrap.never_type
            } else if includes.intersects(TypeFlags::NULL) {
                if includes.intersects(TypeFlags::INCLUDES_NON_WIDENING_TYPE) {
                    bootstrap.null_type
                } else {
                    bootstrap.null_widening_type
                }
            } else if includes.intersects(TypeFlags::UNDEFINED) {
                if includes.intersects(TypeFlags::INCLUDES_NON_WIDENING_TYPE) {
                    bootstrap.undefined_type
                } else {
                    bootstrap.undefined_widening_type
                }
            } else {
                bootstrap.never_type
            }));
        }

        let mut origin = None;
        if synthesize_origin && includes.intersects(TypeFlags::UNION) {
            let mut named = Vec::new();
            self.collect_named_unions(types, &mut named, &mut HashSet::new())?;
            let mut reduced = Vec::new();
            for type_ in &type_set {
                if !named
                    .iter()
                    .any(|union| self.union_contains_type(*union, *type_))
                {
                    reduced.push(*type_);
                }
            }
            if alias.is_none() && named.len() == 1 && reduced.is_empty() {
                return Ok(UnionPlan::Existing(named[0]));
            }
            let named_type_count = named.iter().try_fold(0usize, |count, union| {
                let Some(TypeData::Union(data)) = self.type_payload(*union).map(TypeRecord::data)
                else {
                    return Err(LiteralTypeCacheError::UnsupportedUnionConstituent(*union));
                };
                count
                    .checked_add(data.union.types.len())
                    .ok_or(LiteralTypeCacheError::Capacity)
            })?;
            if named_type_count
                .checked_add(reduced.len())
                .ok_or(LiteralTypeCacheError::Capacity)?
                == type_set.len()
            {
                for union in named {
                    self.insert_union_type(&mut reduced, union)?;
                }
                origin = Some(UnionOriginPlan::DenormalizedUnion(reduced));
            }
        }

        let mut object_flags = if includes.intersects(TypeFlags::NOT_PRIMITIVE_UNION) {
            ObjectFlags::NONE
        } else {
            ObjectFlags::PRIMITIVE_UNION
        };
        if includes.intersects(TypeFlags::INTERSECTION) {
            object_flags |= ObjectFlags::CONTAINS_INTERSECTIONS;
        }
        object_flags |= self.union_propagating_flags(&type_set);
        if type_set.len() == 1 {
            return Ok(UnionPlan::Existing(type_set[0]));
        }
        Ok(UnionPlan::Union {
            types: type_set,
            object_flags,
            alias,
            origin,
        })
    }

    fn union_type_from_sorted_list(
        &mut self,
        types: Vec<TypeId>,
        object_flags: ObjectFlags,
        alias: Option<UnionAliasCacheKey>,
        origin: Option<UnionOriginPlan>,
        array_validation: UnionArrayValidation<'_>,
        allowed_pending: &HashSet<TypeId>,
    ) -> Result<TypeId, LiteralTypeCacheError> {
        let bootstrap = self
            .intrinsic_bootstrap
            .as_ref()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        if types.is_empty() {
            return Ok(bootstrap.never_type);
        }
        if types.len() == 1 {
            return Ok(types[0]);
        }
        let key = UnionTypeCacheKey {
            types: types.clone(),
            origin: origin.as_ref().map(|origin| match origin {
                UnionOriginPlan::DenormalizedUnion(types) => {
                    UnionOriginCacheKey::DenormalizedUnion(types.clone())
                }
                UnionOriginPlan::ExistingIndex(index) => UnionOriginCacheKey::Index(*index),
            }),
            alias: alias.clone(),
        };
        if let Some(cached) = self
            .intrinsic_bootstrap
            .as_ref()
            .and_then(|bootstrap| bootstrap.union_types.get(&key))
            .copied()
        {
            self.validate_union_cache_entry(
                &key,
                cached,
                array_validation,
                &mut HashSet::new(),
                allowed_pending,
            )?;
            return Ok(cached);
        }

        let needs_creation_proof = alias.is_some() || origin.is_some();
        let owners = alias
            .as_ref()
            .map(|alias| self.union_alias_source_owners(alias))
            .transpose()?
            .unwrap_or_default();
        let cache_was_dirty = self.union_cache_needs_validation;
        let origin = match origin {
            Some(UnionOriginPlan::DenormalizedUnion(types)) => Some(
                self.alloc_union_type(ObjectFlags::NONE, types)
                    .expect("preflighted named-union origin is valid"),
            ),
            Some(UnionOriginPlan::ExistingIndex(index)) => Some(index),
            None => None,
        };
        let is_boolean = types.len() == 2
            && types.iter().all(|type_| {
                self.type_payload(*type_)
                    .is_some_and(|record| record.flags().intersects(TypeFlags::BOOLEAN_LITERAL))
            });
        let union = self
            .alloc_union_type(object_flags, types)
            .expect("preflighted sorted union constituents are valid");
        if is_boolean {
            assert!(self.add_type_flags(union, TypeFlags::BOOLEAN));
        }
        if let Some(origin) = origin {
            assert!(self.set_union_caches(
                union,
                None,
                None,
                Some(origin),
                EscapedName::default(),
                ConstituentMapState::Unallocated,
            ));
        }
        if let Some(alias) = alias {
            let identity = self
                .alloc_type_alias(Some(alias.symbol))
                .expect("preflighted union alias symbol belongs to this store");
            if !alias.type_arguments.is_empty() {
                assert!(self.set_type_alias_arguments(identity, Some(alias.type_arguments)));
            }
            assert!(self.set_type_alias(union, Some(identity)));
        }
        if needs_creation_proof {
            assert!(
                self.record_canonical_union_creation(CanonicalUnionCreationProof {
                    union,
                    key: key.clone(),
                    owners
                })
            );
        }
        let bootstrap = self
            .intrinsic_bootstrap
            .as_mut()
            .ok_or(LiteralTypeCacheError::BootstrapUninitialized)?;
        let previous = bootstrap.union_types.insert(key, union);
        self.union_cache_needs_validation = cache_was_dirty;
        debug_assert!(
            previous.is_none(),
            "union cache was checked before allocation"
        );
        Ok(previous.unwrap_or(union))
    }

    /// Initializes the exact dependency-closed intrinsic set once.
    ///
    /// A repeated request with identical options is idempotent. Different
    /// options or any prior checker-owned arena, sparse-link, or resolution
    /// write are rejected before this method changes semantic state. Prebound
    /// symbols/tables and registered AST scopes remain valid inputs.
    ///
    /// # Errors
    ///
    /// Returns [`IntrinsicBootstrapError::OptionsMismatch`] when a completed
    /// bootstrap used different options, or
    /// [`IntrinsicBootstrapError::NonPristineCheckerState`] when checker-owned
    /// state predates the first request.
    ///
    /// # Panics
    ///
    /// Panics if a canonical identity arena is exhausted or an internal pinned
    /// bootstrap shape is rejected by its canonical allocator.
    pub fn initialize_intrinsic_bootstrap(
        &mut self,
        options: IntrinsicBootstrapOptions,
    ) -> Result<&IntrinsicBootstrap, IntrinsicBootstrapError> {
        if let Some(initialized) = self
            .intrinsic_bootstrap
            .as_ref()
            .map(|bootstrap| bootstrap.options)
        {
            return if initialized == options {
                Ok(self
                    .intrinsic_bootstrap
                    .as_ref()
                    .expect("bootstrap presence was just observed"))
            } else {
                Err(IntrinsicBootstrapError::OptionsMismatch {
                    initialized,
                    requested: options,
                })
            };
        }

        let [
            node,
            symbol_node,
            type_node,
            enum_member,
            assertion,
            array_literal,
            switch_statement,
            jsx_element,
            signature,
            symbol_reference,
            value_symbol,
            mapped_symbol,
            deferred_symbol,
            alias_symbol,
            module_symbol,
            late_bound,
            export_type,
            members_and_exports,
            type_alias,
            declared_type,
            spread,
            variance,
            reverse_mapped_symbol,
            marked_assignment_symbol,
            containing_symbol,
            source_file,
        ] = self.checker_link_allocated_lengths();
        let (entries, resolution_start, boundaries, next_boundary_serial) =
            self.type_resolution_internal_state();
        let [
            source_callable_types,
            source_callable_declarations,
            source_callable_owners,
            source_callable_signatures,
            source_callable_type_parameters,
        ] = self.source_callable_provenance_lengths();
        let state = CheckerStateSnapshot {
            checker_symbols: self.symbol_store().checker_created_symbol_len(),
            merged_symbols: self.merged_symbol_len(),
            source_callable_types,
            source_callable_declarations,
            source_callable_owners,
            source_callable_signatures,
            source_callable_type_parameters,
            cached_signatures: self.cached_signature_len(),
            callable_signature_parameter_types: self.callable_signature_parameter_types_len(),
            semantic_arenas: SemanticArenaCounts {
                types: self.type_len(),
                mappers: self.mapper_len(),
                signatures: self.signature_len(),
                predicates: self.type_predicate_len(),
                index_infos: self.index_info_len(),
                type_aliases: self.type_alias_len(),
                conditional_roots: self.conditional_root_len(),
                entity_names: self.entity_name_len(),
            },
            links: CheckerLinkCounts {
                node,
                symbol_node,
                type_node,
                enum_member,
                assertion,
                array_literal,
                switch_statement,
                jsx_element,
                signature,
                symbol_reference,
                value_symbol,
                mapped_symbol,
                deferred_symbol,
                alias_symbol,
                module_symbol,
                late_bound,
                export_type,
                members_and_exports,
                type_alias,
                declared_type,
                spread,
                variance,
                reverse_mapped_symbol,
                marked_assignment_symbol,
                containing_symbol,
                source_file,
            },
            type_resolution: TypeResolutionStateSnapshot {
                entries,
                resolution_start,
                boundaries,
                next_boundary_serial,
            },
            relations: self.relation_state_snapshot(),
        };
        if !state.is_pristine() {
            return Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                state,
            )));
        }

        let bootstrap = IntrinsicBootstrap::build(self, options);
        self.intrinsic_bootstrap = Some(bootstrap);
        self.union_cache_needs_validation = false;
        Ok(self
            .intrinsic_bootstrap
            .as_ref()
            .expect("bootstrap was just installed"))
    }
}

impl IntrinsicBootstrap {
    /// Looks up the exact checker-owned string-literal cache.
    #[must_use]
    pub fn cached_string_literal_type(&self, value: &str) -> Option<TypeId> {
        self.string_literal_types.get(value).copied()
    }

    /// Looks up the exact checker-owned number-literal cache.
    ///
    /// NaN is absent because pinned `NewChecker` does not initialize `nanType`.
    #[must_use]
    pub fn cached_number_literal_type(&self, value: Number) -> Option<TypeId> {
        NumberLiteralCacheKey::from_number(value)
            .and_then(|key| self.number_literal_types.get(&key).copied())
    }

    /// Looks up the exact checker-owned bigint-literal cache.
    #[must_use]
    pub fn cached_bigint_literal_type(&self, value: &PseudoBigInt) -> Option<TypeId> {
        self.bigint_literal_types
            .iter()
            .find_map(|(cached, id)| (cached == value).then_some(*id))
    }

    /// Looks up an already-normalized, sorted canonical union key.
    ///
    /// Callers supply the post-flattening, post-reduction list; this read API
    /// performs no normalization of its own.
    #[must_use]
    pub fn cached_union_type(&self, normalized_types: &[TypeId]) -> Option<TypeId> {
        self.union_types
            .get(&UnionTypeCacheKey::anonymous(normalized_types.to_vec()))
            .copied()
    }

    /// Reads an existing optional-parameter identity without normalizing or allocating types.
    pub(super) fn cached_optional_parameter_type(&self, base: TypeId) -> Option<TypeId> {
        if [
            self.any_type,
            self.wildcard_type,
            self.error_type,
            self.unknown_type,
            self.undefined_type,
        ]
        .contains(&base)
        {
            return Some(base);
        }
        if base == self.never_type || base == self.missing_type {
            return Some(self.undefined_type);
        }
        let (first, second) = if base < self.undefined_type {
            (base, self.undefined_type)
        } else {
            (self.undefined_type, base)
        };
        self.union_of_union_types
            .get(&UnionOfUnionCacheKey {
                first,
                second,
                reduction: UnionReduction::Literal,
                alias: None,
            })
            .copied()
            .or_else(|| self.cached_union_type(&[first, second]))
            .or_else(|| {
                self.union_types.iter().find_map(|(key, value)| {
                    (*value == base && key.types.contains(&self.undefined_type)).then_some(base)
                })
            })
    }

    /// Looks up an already-normalized bootstrap template-literal key.
    #[must_use]
    pub fn cached_template_literal_type(
        &self,
        normalized_texts: &[String],
        normalized_types: &[TypeId],
    ) -> Option<TypeId> {
        self.template_literal_types.iter().find_map(|(key, id)| {
            (key.texts.as_slice() == normalized_texts && key.types.as_slice() == normalized_types)
                .then_some(*id)
        })
    }

    /// Number of checker-owned string-literal cache entries.
    #[must_use]
    pub fn string_literal_cache_len(&self) -> usize {
        self.string_literal_types.len()
    }

    /// Number of checker-owned number-literal cache entries.
    #[must_use]
    pub fn number_literal_cache_len(&self) -> usize {
        self.number_literal_types.len()
    }

    /// Number of checker-owned bigint-literal cache entries.
    #[must_use]
    pub fn bigint_literal_cache_len(&self) -> usize {
        self.bigint_literal_types.len()
    }

    /// Number of normalized union entries seeded by pinned bootstrap calls.
    #[must_use]
    pub fn union_cache_len(&self) -> usize {
        self.union_types.len()
    }

    /// Number of two-input union fast-path entries created after bootstrap.
    #[cfg(test)]
    #[must_use]
    pub(super) fn union_of_union_cache_len(&self) -> usize {
        self.union_of_union_types.len()
    }

    /// Number of template-literal entries seeded by pinned bootstrap calls.
    #[must_use]
    pub fn template_literal_cache_len(&self) -> usize {
        self.template_literal_types.len()
    }

    #[allow(clippy::too_many_lines)] // Preserves the observable pinned initialization order.
    fn build(
        store: &mut SemanticStore<TypeRecord, TypeMapper>,
        options: IntrinsicBootstrapOptions,
    ) -> Self {
        let mut string_literal_types = HashMap::new();
        let mut number_literal_types = HashMap::new();
        let mut bigint_literal_types = Vec::new();
        let mut union_types = HashMap::new();
        let union_of_union_types = HashMap::new();
        let mut template_literal_types = HashMap::new();

        let globals = store.alloc_symbol_table();
        let undefined_symbol = transient_symbol(store, SymbolFlags::PROPERTY, "undefined");
        let arguments_symbol = transient_symbol(store, SymbolFlags::PROPERTY, "arguments");
        let require_symbol = transient_symbol(store, SymbolFlags::PROPERTY, "require");
        let unknown_symbol = transient_symbol(store, SymbolFlags::PROPERTY, "unknown");
        let global_this_symbol = store.alloc_transient_symbol(
            SymbolFlags::MODULE,
            EscapedName::source("globalThis"),
            CheckFlags::READONLY,
        );
        assert!(store.set_symbol_relationships(
            global_this_symbol,
            None,
            Some(globals),
            None,
            None,
        ));
        assert_eq!(
            store.insert_symbol(
                globals,
                EscapedName::source("globalThis"),
                global_this_symbol,
            ),
            Some(None),
        );

        let any_type = intrinsic(store, TypeFlags::ANY, "any");
        let auto_type = intrinsic_ex(
            store,
            TypeFlags::ANY,
            "any",
            ObjectFlags::NON_INFERRABLE_TYPE,
        );
        let wildcard_type = intrinsic(store, TypeFlags::ANY, "any");
        let blocked_string_type = intrinsic(store, TypeFlags::ANY, "any");
        let error_type = intrinsic(store, TypeFlags::ANY, "error");
        let unresolved_type = intrinsic(store, TypeFlags::ANY, "unresolved");
        let non_inferrable_any_type = intrinsic_ex(
            store,
            TypeFlags::ANY,
            "any",
            ObjectFlags::CONTAINS_WIDENING_TYPE,
        );
        let intrinsic_marker_type = intrinsic(store, TypeFlags::ANY, "intrinsic");
        let unknown_type = intrinsic(store, TypeFlags::UNKNOWN, "unknown");
        let undefined_type = intrinsic(store, TypeFlags::UNDEFINED, "undefined");
        let undefined_widening_type = if options.strict_null_checks {
            undefined_type
        } else {
            intrinsic_ex(
                store,
                TypeFlags::UNDEFINED,
                "undefined",
                ObjectFlags::CONTAINS_WIDENING_TYPE,
            )
        };
        let missing_type = intrinsic(store, TypeFlags::UNDEFINED, "undefined");
        let undefined_or_missing_type = if options.exact_optional_property_types {
            missing_type
        } else {
            undefined_type
        };
        let optional_type = intrinsic(store, TypeFlags::UNDEFINED, "undefined");
        let null_type = intrinsic(store, TypeFlags::NULL, "null");
        let null_widening_type = if options.strict_null_checks {
            null_type
        } else {
            intrinsic_ex(
                store,
                TypeFlags::NULL,
                "null",
                ObjectFlags::CONTAINS_WIDENING_TYPE,
            )
        };
        let string_type = intrinsic(store, TypeFlags::STRING, "string");
        let number_type = intrinsic(store, TypeFlags::NUMBER, "number");
        let bigint_type = intrinsic(store, TypeFlags::BIG_INT, "bigint");

        let regular_false_type = literal(
            store,
            TypeFlags::BOOLEAN_LITERAL,
            LiteralValue::Boolean(false),
            RegularLiteralLink::SelfType,
        );
        let false_type = literal(
            store,
            TypeFlags::BOOLEAN_LITERAL,
            LiteralValue::Boolean(false),
            RegularLiteralLink::Type(regular_false_type),
        );
        assert!(store.set_literal_links(regular_false_type, Some(false_type), regular_false_type,));
        assert!(store.set_literal_links(false_type, Some(false_type), regular_false_type,));
        let regular_true_type = literal(
            store,
            TypeFlags::BOOLEAN_LITERAL,
            LiteralValue::Boolean(true),
            RegularLiteralLink::SelfType,
        );
        let true_type = literal(
            store,
            TypeFlags::BOOLEAN_LITERAL,
            LiteralValue::Boolean(true),
            RegularLiteralLink::Type(regular_true_type),
        );
        assert!(store.set_literal_links(regular_true_type, Some(true_type), regular_true_type,));
        assert!(store.set_literal_links(true_type, Some(true_type), regular_true_type,));
        let boolean_type = fixed_union(
            store,
            &mut union_types,
            vec![regular_false_type, regular_true_type],
            ObjectFlags::PRIMITIVE_UNION,
            true,
        );

        let es_symbol_type = intrinsic(store, TypeFlags::ES_SYMBOL, "symbol");
        let void_type = intrinsic(store, TypeFlags::VOID, "void");
        let never_type = intrinsic(store, TypeFlags::NEVER, "never");
        let silent_never_type = intrinsic_ex(
            store,
            TypeFlags::NEVER,
            "never",
            ObjectFlags::NON_INFERRABLE_TYPE,
        );
        let implicit_never_type = intrinsic(store, TypeFlags::NEVER, "never");
        let unreachable_never_type = intrinsic(store, TypeFlags::NEVER, "never");
        let non_primitive_type = intrinsic(store, TypeFlags::NON_PRIMITIVE, "object");
        let string_or_number_type = fixed_union(
            store,
            &mut union_types,
            vec![string_type, number_type],
            ObjectFlags::PRIMITIVE_UNION,
            false,
        );
        let string_number_symbol_type = fixed_union(
            store,
            &mut union_types,
            vec![string_type, number_type, es_symbol_type],
            ObjectFlags::PRIMITIVE_UNION,
            false,
        );
        let number_or_bigint_type = fixed_union(
            store,
            &mut union_types,
            vec![number_type, bigint_type],
            ObjectFlags::PRIMITIVE_UNION,
            false,
        );
        let numeric_string_type = cached_template_literal(
            store,
            &mut template_literal_types,
            vec![String::new(), String::new()],
            vec![number_type],
        );
        let template_constraint_types = if options.strict_null_checks {
            vec![
                undefined_type,
                null_type,
                string_type,
                number_type,
                bigint_type,
                regular_false_type,
                regular_true_type,
            ]
        } else {
            // Pinned addTypeToUnion records nullable includes but does not insert
            // nullable constituents when strict null checking is disabled.
            vec![
                string_type,
                number_type,
                bigint_type,
                regular_false_type,
                regular_true_type,
            ]
        };
        let template_constraint_type = fixed_union(
            store,
            &mut union_types,
            template_constraint_types,
            ObjectFlags::PRIMITIVE_UNION,
            false,
        );
        let unique_literal_type = intrinsic(store, TypeFlags::NEVER, "never");

        // Five callback-owned mapper allocations occur here upstream. They are
        // deliberately absent until canonical TypeMapper can own executable behavior.
        let empty_object_type = anonymous(store, None);
        let empty_jsx_object_type = anonymous(store, None);
        let empty_fresh_jsx_object_type = anonymous(store, None);
        let empty_type_literal_symbol = store.alloc_transient_symbol(
            SymbolFlags::TYPE_LITERAL,
            EscapedName::internal(InternalSymbolName::Type),
            CheckFlags::NONE,
        );
        let empty_type_literal_type = anonymous(store, Some(empty_type_literal_symbol));
        let unknown_empty_object_type = anonymous(store, None);
        let unknown_union_type = if options.strict_null_checks {
            fixed_union(
                store,
                &mut union_types,
                vec![undefined_type, null_type, unknown_empty_object_type],
                ObjectFlags::NONE,
                false,
            )
        } else {
            unknown_type
        };
        let empty_generic_type = anonymous(store, None);
        assert!(store.set_object_instantiations(
            empty_generic_type,
            TypeCacheState::Allocated(HashMap::new()),
        ));
        let any_function_type = anonymous(store, None);
        assert!(store.add_type_object_flags(any_function_type, ObjectFlags::NON_INFERRABLE_TYPE,));
        let no_constraint_type = anonymous(store, None);
        let circular_constraint_type = anonymous(store, None);
        let resolving_default_type = anonymous(store, None);
        let marker_super_type = type_parameter(store);
        let marker_sub_type = type_parameter(store);
        assert!(store.set_type_parameter_resolution(
            marker_sub_type,
            Some(marker_super_type),
            None,
            None,
            None,
        ));
        let marker_other_type = type_parameter(store);
        let marker_super_type_for_check = type_parameter(store);
        let marker_sub_type_for_check = type_parameter(store);
        assert!(store.set_type_parameter_resolution(
            marker_sub_type_for_check,
            Some(marker_super_type_for_check),
            None,
            None,
            None,
        ));

        let no_type_predicate = store
            .alloc_type_predicate(
                TypePredicateKind::Identifier,
                0,
                "<<unresolved>>",
                Some(any_type),
            )
            .expect("the pinned no-type predicate references this store");
        let any_signature = empty_signature(store, any_type);
        let unknown_signature = empty_signature(store, error_type);
        let resolving_signature = empty_signature(store, any_type);
        let silent_never_signature = empty_signature(store, silent_never_type);
        let enum_number_index_info = store
            .alloc_index_info(number_type, string_type, true, None, Vec::new())
            .expect("the pinned enum number index info references this store");
        let any_base_type_index_info = store
            .alloc_index_info(string_type, any_type, false, None, Vec::new())
            .expect("the pinned any-base index info references this store");

        let empty_string_type =
            cached_string_literal(store, &mut string_literal_types, String::new());
        let zero_type = cached_number_literal(store, &mut number_literal_types, Number::new(0.0));
        let zero_bigint_type =
            cached_bigint_literal(store, &mut bigint_literal_types, PseudoBigInt::default());
        let typeof_types = [
            "bigint",
            "boolean",
            "function",
            "number",
            "object",
            "string",
            "symbol",
            "undefined",
        ]
        .into_iter()
        .map(|value| cached_string_literal(store, &mut string_literal_types, value.to_owned()))
        .collect();
        let typeof_type = fixed_union(
            store,
            &mut union_types,
            typeof_types,
            ObjectFlags::PRIMITIVE_UNION,
            false,
        );

        Self {
            options,
            globals,
            undefined_symbol,
            arguments_symbol,
            require_symbol,
            unknown_symbol,
            global_this_symbol,
            any_type,
            auto_type,
            wildcard_type,
            blocked_string_type,
            error_type,
            unresolved_type,
            non_inferrable_any_type,
            intrinsic_marker_type,
            unknown_type,
            undefined_type,
            undefined_widening_type,
            missing_type,
            undefined_or_missing_type,
            optional_type,
            null_type,
            null_widening_type,
            string_type,
            number_type,
            bigint_type,
            regular_false_type,
            false_type,
            regular_true_type,
            true_type,
            boolean_type,
            es_symbol_type,
            void_type,
            never_type,
            silent_never_type,
            implicit_never_type,
            unreachable_never_type,
            non_primitive_type,
            string_or_number_type,
            string_number_symbol_type,
            number_or_bigint_type,
            numeric_string_type,
            template_constraint_type,
            unique_literal_type,
            empty_object_type,
            empty_jsx_object_type,
            empty_fresh_jsx_object_type,
            empty_type_literal_symbol,
            empty_type_literal_type,
            unknown_empty_object_type,
            unknown_union_type,
            empty_generic_type,
            any_function_type,
            no_constraint_type,
            circular_constraint_type,
            resolving_default_type,
            marker_super_type,
            marker_sub_type,
            marker_other_type,
            marker_super_type_for_check,
            marker_sub_type_for_check,
            no_type_predicate,
            any_signature,
            unknown_signature,
            resolving_signature,
            silent_never_signature,
            enum_number_index_info,
            any_base_type_index_info,
            empty_string_type,
            zero_type,
            zero_bigint_type,
            typeof_type,
            string_literal_types,
            number_literal_types,
            bigint_literal_types,
            union_types,
            union_of_union_types,
            template_literal_types,
        }
    }
}

fn transient_symbol(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    flags: SymbolFlags,
    name: &str,
) -> SemanticSymbolId {
    store.alloc_transient_symbol(flags, EscapedName::source(name), CheckFlags::NONE)
}

fn intrinsic(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    flags: TypeFlags,
    name: &str,
) -> TypeId {
    store
        .alloc_intrinsic_type(flags, name)
        .expect("the pinned intrinsic shape is valid")
}

fn intrinsic_ex(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    flags: TypeFlags,
    name: &str,
    object_flags: ObjectFlags,
) -> TypeId {
    store
        .alloc_intrinsic_type_ex(flags, name, object_flags)
        .expect("the pinned extended intrinsic shape is valid")
}

fn literal(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    flags: TypeFlags,
    value: LiteralValue,
    regular_type: RegularLiteralLink,
) -> TypeId {
    store
        .alloc_literal_type(flags, value, regular_type)
        .expect("the pinned literal shape and provenance are valid")
}

fn fixed_union(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    cache: &mut HashMap<UnionTypeCacheKey, TypeId>,
    types: Vec<TypeId>,
    object_flags: ObjectFlags,
    is_boolean: bool,
) -> TypeId {
    let key = UnionTypeCacheKey::anonymous(types.clone());
    if let Some(cached) = cache.get(&key) {
        return *cached;
    }
    let union = store
        .alloc_union_type(object_flags, types)
        .expect("the pinned sorted union constituents belong to this store");
    if is_boolean {
        assert!(store.add_type_flags(union, TypeFlags::BOOLEAN));
    }
    assert_eq!(cache.insert(key, union), None);
    union
}

fn cached_template_literal(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    cache: &mut HashMap<TemplateLiteralCacheKey, TypeId>,
    texts: Vec<String>,
    types: Vec<TypeId>,
) -> TypeId {
    let key = TemplateLiteralCacheKey {
        texts: texts.clone(),
        types: types.clone(),
    };
    if let Some(cached) = cache.get(&key) {
        return *cached;
    }
    let template = store
        .alloc_template_literal_type(texts, types)
        .expect("the pinned normalized template literal is valid");
    assert_eq!(cache.insert(key, template), None);
    template
}

fn cached_string_literal(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    cache: &mut HashMap<String, TypeId>,
    value: String,
) -> TypeId {
    if let Some(cached) = cache.get(&value) {
        return *cached;
    }
    let literal = literal(
        store,
        TypeFlags::STRING_LITERAL,
        LiteralValue::String(value.clone()),
        RegularLiteralLink::SelfType,
    );
    assert_eq!(cache.insert(value, literal), None);
    literal
}

fn cached_number_literal(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    cache: &mut HashMap<NumberLiteralCacheKey, TypeId>,
    value: Number,
) -> TypeId {
    let key = NumberLiteralCacheKey::from_number(value)
        .expect("NewChecker bootstrap never requests a NaN literal");
    if let Some(cached) = cache.get(&key) {
        return *cached;
    }
    let literal = literal(
        store,
        TypeFlags::NUMBER_LITERAL,
        LiteralValue::Number(value),
        RegularLiteralLink::SelfType,
    );
    assert_eq!(cache.insert(key, literal), None);
    literal
}

fn cached_bigint_literal(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    cache: &mut Vec<(PseudoBigInt, TypeId)>,
    value: PseudoBigInt,
) -> TypeId {
    if let Some((_, cached)) = cache.iter().find(|(cached, _)| cached == &value) {
        return *cached;
    }
    let literal = literal(
        store,
        TypeFlags::BIG_INT_LITERAL,
        LiteralValue::BigInt(value.clone()),
        RegularLiteralLink::SelfType,
    );
    cache.push((value, literal));
    literal
}

fn anonymous(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    symbol: Option<SemanticSymbolId>,
) -> TypeId {
    let object = store
        .alloc_plain_object_type(ObjectFlags::ANONYMOUS, symbol)
        .expect("the pinned anonymous type shape and symbol provenance are valid");
    assert!(store.set_structured_type_members(object, None, None, None, None, None));
    object
}

fn type_parameter(store: &mut SemanticStore<TypeRecord, TypeMapper>) -> TypeId {
    store
        .alloc_type_parameter(None)
        .expect("the pinned marker type parameter is valid")
}

fn empty_signature(
    store: &mut SemanticStore<TypeRecord, TypeMapper>,
    return_type: TypeId,
) -> SignatureId {
    store
        .alloc_signature(
            SignatureFlags::NONE,
            None,
            Vec::new(),
            None,
            Vec::new(),
            Some(return_type),
            None,
            0,
        )
        .expect("the pinned sentinel signature references this store")
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use ts_ast::{FileId, NodeData, NodeRef, SyntaxKind};
    use ts_binder::{
        AstScope, CanonicalBinder, CanonicalModuleState, CanonicalProgramBindings,
        CanonicalSourceFileFacts, CanonicalSourceLanguage, CheckFlags, EscapedName,
        InternalSymbolName, SymbolData, SymbolFlags, SymbolStore,
    };
    use ts_parser::{ParseResult, parse_source_file};

    use super::*;
    use crate::semantic::{
        AliasSymbolLinks, AliasTargetState, CanonicalCheckerContext, CanonicalCheckerOptions,
        DecoratorSignatureState, EffectsSignatureState, ResolvedSignatureState, SignatureLinks,
        declared::type_list_key,
        instantiate::canonical_anonymous_union,
        signatures::ElementFlags,
        tuple_types::CanonicalTupleTypeRequest,
        type_records::{LiteralTypeData, TypeData},
    };

    type TestStore = SemanticStore<TypeRecord, TypeMapper>;

    fn initialized(options: IntrinsicBootstrapOptions) -> TestStore {
        let mut store = TestStore::new();
        store.initialize_intrinsic_bootstrap(options).unwrap();
        store
    }

    fn completed_bindings(file: FileId, parsed: &ParseResult) -> CanonicalProgramBindings {
        let mut binder = CanonicalBinder::new();
        binder
            .bind_source_file_with_facts(
                &parsed.arena,
                parsed.source_file,
                file,
                CanonicalSourceFileFacts::new(
                    EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
                    CanonicalSourceLanguage::TypeScript,
                    false,
                    CanonicalModuleState::Script,
                ),
            )
            .unwrap();
        binder
            .bind_typescript_declaration_slice(&parsed.arena, file)
            .unwrap();
        binder.finish()
    }

    fn checker_context(file: FileId, parsed: &ParseResult) -> CanonicalCheckerContext<'_> {
        CanonicalCheckerContext::new(
            completed_bindings(file, parsed),
            [(file, &parsed.arena)].into_iter().collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap()
    }

    fn variable_initializer(parsed: &ParseResult, file: FileId, expected: &str) -> NodeRef {
        let initializer = parsed
            .arena
            .iter()
            .find_map(|(_, node)| {
                let NodeData::VariableDeclaration(variable) = &node.data else {
                    return None;
                };
                let name = parsed.arena.get(variable.name)?;
                let NodeData::Identifier(identifier) = &name.data else {
                    return None;
                };
                (identifier.text == expected)
                    .then_some(variable.initializer)
                    .flatten()
            })
            .unwrap_or_else(|| panic!("missing initializer for variable {expected}"));
        NodeRef::new(parsed.arena.id(), file, initializer)
    }

    fn checked_expression_type(
        context: &CanonicalCheckerContext<'_>,
        expression: NodeRef,
    ) -> TypeId {
        context
            .store()
            .type_node_links(expression)
            .and_then(|links| links.resolved_type)
            .expect("the expression was checked")
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Check raw caches, read projections, replay, and cache rejection.
    fn library_optional_properties_keep_raw_annotation_caches() {
        let library = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface LibraryShape { label?: string; items?: string[]; } ",
            "interface LibraryShapeConstructor { new(): LibraryShape; } ",
            "declare var LibraryShape: LibraryShapeConstructor;",
        ));
        let source = parse_source_file(concat!(
            "declare const sample: LibraryShape; ",
            "const labelRead = sample.label; const itemsRead = sample.items; ",
            "const inferred = () => sample;",
        ));
        let library_file = FileId::new(9_961);
        let file = FileId::new(9_962);
        for (strict, exact) in [(false, false), (true, false), (true, true)] {
            let mut binder = CanonicalBinder::new();
            for (parsed, file, default_library) in
                [(&library, library_file, true), (&source, file, false)]
            {
                assert!(parsed.diagnostics.is_empty());
                binder
                    .bind_source_file_with_facts(
                        &parsed.arena,
                        parsed.source_file,
                        file,
                        CanonicalSourceFileFacts::new_with_default_library(
                            EscapedName::source(format!("\"/optional-{}.ts\"", file.index())),
                            CanonicalSourceLanguage::TypeScript,
                            default_library,
                            default_library,
                            CanonicalModuleState::Script,
                        ),
                    )
                    .unwrap();
                binder
                    .bind_typescript_declaration_slice(&parsed.arena, file)
                    .unwrap();
            }
            let options = CanonicalCheckerOptions {
                intrinsic: IntrinsicBootstrapOptions {
                    strict_null_checks: strict,
                    exact_optional_property_types: exact,
                },
                ..CanonicalCheckerOptions::default()
            };
            let mut context = CanonicalCheckerContext::new(
                binder.finish(),
                vec![(library_file, &library.arena), (file, &source.arena)],
                options,
            )
            .unwrap();
            let globals = context.global_types().clone();
            let store = context.store();
            let owner = store
                .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                .and_then(|globals| globals.get_source("LibraryShape"))
                .and_then(|owner| store.get_merged_symbol(owner))
                .unwrap();
            let properties = ["label", "items"].map(|name| {
                store
                    .symbol(owner)
                    .and_then(ts_binder::semantic::Symbol::members)
                    .and_then(|members| store.symbol_table(members))
                    .and_then(|members| members.get_source(name))
                    .unwrap()
            });
            for property in properties {
                assert!(store.value_symbol_links(property).is_none());
            }
            let type_ = {
                let library_bound = context.file(library_file).unwrap().1.clone();
                let source_bound = context.file(file).unwrap().1.clone();
                let host = crate::semantic::DeclaredTypeHost::new_after_global_merge(
                    [
                        (&library.arena, &library_bound),
                        (&source.arena, &source_bound),
                    ],
                    crate::semantic::production::GlobalMergeCompletion::for_test(
                        options.name_resolution,
                    ),
                )
                .unwrap();
                context
                    .store_mut_for_test()
                    .get_declared_type_of_symbol(&host, owner)
                    .unwrap()
            };
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let constituents = [type_, number];
            let union = context
                .store_mut_for_test()
                .expression_union_type_with_global_types(
                    &globals,
                    &constituents,
                    UnionReduction::Literal,
                )
                .unwrap();
            assert_eq!(context.get_declared_type_of_symbol(owner), Ok(type_));
            let store = context.store();
            assert!(
                store
                    .type_payload(type_)
                    .unwrap()
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED)
            );
            let raw_types = properties.map(|property| {
                assert_eq!(
                    store.symbol(property).unwrap().flags(),
                    SymbolFlags::PROPERTY | SymbolFlags::OPTIONAL,
                );
                store
                    .value_symbol_links(property)
                    .unwrap()
                    .resolved_type
                    .unwrap()
            });
            let string = store.intrinsic_bootstrap().unwrap().string_type;
            assert_eq!(raw_types[0], string);
            let array = store
                .canonical_array_reference(&globals, raw_types[1])
                .unwrap()
                .unwrap();
            assert_eq!(array.element_type, string);
            assert_eq!(array.base_type, raw_types[1]);
            assert_eq!(
                store.validate_cached_array_capability_with_array_targets(
                    CanonicalArrayTargets::from_global_types(&globals),
                    type_,
                ),
                Ok(()),
            );
            assert_eq!(
                store.validate_cached_array_capability(type_),
                Err(LiteralTypeCacheError::UnsupportedUnionConstituent(
                    raw_types[1]
                )),
            );
            context.check_source_file(file).unwrap();
            assert!(context.diagnostics().is_empty());
            let reads = ["labelRead", "itemsRead"].map(|name| {
                let node = variable_initializer(&source, file, name);
                (node, checked_expression_type(&context, node))
            });
            let store = context.store_mut_for_test();
            for (property, (raw, (_, read))) in
                properties.into_iter().zip(raw_types.into_iter().zip(reads))
            {
                assert_eq!(
                    store.value_symbol_links(property),
                    Some(&ValueSymbolLinks {
                        resolved_type: Some(raw),
                        ..ValueSymbolLinks::default()
                    }),
                );
                if strict {
                    let mut expected = [
                        raw,
                        store
                            .intrinsic_bootstrap()
                            .unwrap()
                            .undefined_or_missing_type,
                    ];
                    expected.sort_unstable();
                    assert_ne!(raw, read);
                    assert_eq!(
                        store.validate_canonical_union_metadata(read, &expected),
                        Ok(())
                    );
                } else {
                    assert_eq!(read, raw);
                }
            }
            assert_eq!(
                store.expression_union_type_with_global_types(
                    &globals,
                    &constituents,
                    UnionReduction::Literal
                ),
                Ok(union),
            );
            let snapshot = |store: &TestStore| {
                (
                    store.type_len(),
                    store.symbol_len(),
                    store.signature_len(),
                    store.mapper_len(),
                    store.index_info_len(),
                    store.symbol_store().symbol_table_len(),
                    store.checker_link_allocated_lengths(),
                )
            };
            let warm = snapshot(store);
            for _ in 0..2 {
                context.recheck_source_file(file).unwrap();
                assert_eq!(context.get_declared_type_of_symbol(owner), Ok(type_));
                for (node, read) in reads {
                    assert_eq!(context.get_type_at_location(node), Ok(read));
                }
                let store = context.store_mut_for_test();
                assert_eq!(
                    store.expression_union_type_with_global_types(
                        &globals,
                        &constituents,
                        UnionReduction::Literal
                    ),
                    Ok(union),
                );
                assert_eq!(snapshot(store), warm);
            }
            if !strict {
                continue;
            }
            let store = context.store_mut_for_test();
            for (property, (_, read)) in properties.into_iter().zip(reads) {
                let original = store.value_symbol_links(property).cloned().unwrap();
                assert!(store.set_value_symbol_links(
                    property,
                    ValueSymbolLinks {
                        resolved_type: Some(read),
                        ..ValueSymbolLinks::default()
                    }
                ));
                let rejected = Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_));
                for _ in 0..2 {
                    assert_eq!(
                        store.validate_cached_array_capability_with_array_targets(
                            CanonicalArrayTargets::from_global_types(&globals),
                            type_,
                        ),
                        rejected,
                    );
                    assert_eq!(
                        store.expression_union_type_with_global_types(
                            &globals,
                            &constituents,
                            UnionReduction::Literal
                        ),
                        Err(LiteralTypeCacheError::UnsupportedUnionConstituent(type_)),
                    );
                    assert_eq!(snapshot(store), warm);
                }
                assert!(store.set_value_symbol_links(property, original));
                assert_eq!(
                    store.expression_union_type_with_global_types(
                        &globals,
                        &constituents,
                        UnionReduction::Literal
                    ),
                    Ok(union),
                );
                assert_eq!(snapshot(store), warm);
            }
        }
    }

    fn inherited_graph_property(store: &TestStore) -> (TypeId, TypeId, SemanticSymbolId) {
        let owner = store
            .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
            .and_then(|globals| globals.get_source("Derived"))
            .and_then(|owner| store.get_merged_symbol(owner))
            .unwrap();
        let derived = store
            .declared_type_links(owner)
            .unwrap()
            .declared_type
            .unwrap();
        let TypeData::Interface(data) = store.type_payload(derived).unwrap().data() else {
            panic!("Derived must retain its interface identity")
        };
        let base = data.resolved_base_types.as_ref().unwrap()[0];
        let value = store
            .symbol_table(data.reference.object.structured.members.unwrap())
            .and_then(|members| members.get_source("value"))
            .unwrap();
        (derived, base, value)
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Both bodies must preserve cold array targets through source replay.
    fn inherited_index_callables_preserve_cold_array_targets() {
        let declarations = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Base<T> { value: T; [index: number]: Array<number>; }",
        ));
        assert!(
            declarations.diagnostics.is_empty(),
            "{:?}",
            declarations.diagnostics
        );
        for (body, reads_inherited) in [("return 1;", false), ("return value.value;", true)] {
            let parsed = parse_source_file(&format!(
                "interface Derived extends Base<number> {{}} \
                 function read(value: Derived): number {{ {body} }}",
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(198);
            let library_file = FileId::new(199);
            let mut binder = CanonicalBinder::new();
            for (file, source, is_declaration) in
                [(library_file, &declarations, true), (file, &parsed, false)]
            {
                binder
                    .bind_source_file_with_facts(
                        &source.arena,
                        source.source_file,
                        file,
                        CanonicalSourceFileFacts::new(
                            EscapedName::source(if is_declaration {
                                "\"/project/cold-index-base.d.ts\""
                            } else {
                                "\"/project/cold-index-callable.ts\""
                            }),
                            CanonicalSourceLanguage::TypeScript,
                            is_declaration,
                            CanonicalModuleState::Script,
                        ),
                    )
                    .unwrap();
                binder
                    .bind_typescript_declaration_slice(&source.arena, file)
                    .unwrap();
            }
            let mut context = CanonicalCheckerContext::new(
                binder.finish(),
                [(library_file, &declarations.arena), (file, &parsed.arena)]
                    .into_iter()
                    .collect(),
                CanonicalCheckerOptions::default(),
            )
            .unwrap();
            let targets = CanonicalArrayTargets::from_global_types(context.global_types());
            let assert_cold_arrays = |store: &TestStore| {
                for target in [targets.array_type(), targets.readonly_array_type()] {
                    assert!(matches!(
                        store.type_payload(target).map(TypeRecord::data),
                        Some(TypeData::Interface(interface)) if !interface.declared_members_resolved
                    ));
                }
            };
            assert_cold_arrays(context.store());
            context
                .check_source_file(file)
                .unwrap_or_else(|error| panic!("{body}: {error:?}"));
            assert!(context.diagnostics().is_empty());
            assert_cold_arrays(context.store());
            let store = context.store();
            let (derived, _, value) = inherited_graph_property(store);
            let number = store.intrinsic_bootstrap().unwrap().number_type;
            let index = store
                .type_payload(derived)
                .unwrap()
                .data()
                .structured()
                .unwrap()
                .index_infos
                .as_ref()
                .unwrap()[0];
            let array = store.index_info(index).unwrap().value_type();
            assert_eq!(
                store
                    .canonical_array_reference_with_targets(targets, array)
                    .unwrap()
                    .unwrap()
                    .element_type,
                number,
            );
            assert_eq!(
                store.value_symbol_links(value).unwrap().resolved_type,
                reads_inherited.then_some(number),
            );
            let snapshot = |store: &TestStore| {
                (
                    store.type_len(),
                    store.symbol_len(),
                    store.mapper_len(),
                    store.signature_len(),
                    store.index_info_len(),
                    store.symbol_store().symbol_table_len(),
                    store.checker_link_allocated_lengths(),
                    store.relation_state_snapshot(),
                )
            };
            let warm = snapshot(store);
            assert_eq!(
                store.validate_cached_array_capability_with_array_targets(targets, derived),
                Ok(()),
            );
            assert_eq!(snapshot(store), warm);
            assert_cold_arrays(store);
            for _ in 0..2 {
                context
                    .recheck_source_file(file)
                    .unwrap_or_else(|error| panic!("warm {body}: {error:?}"));
                let store = context.store();
                assert_eq!(snapshot(store), warm);
                assert_cold_arrays(store);
                assert!(context.diagnostics().is_empty());
                assert_eq!(store.index_info(index).unwrap().value_type(), array);
                assert_eq!(
                    store.value_symbol_links(value).unwrap().resolved_type,
                    reads_inherited.then_some(number),
                );
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Source-backed index identity and cold/warm proxy state share one fixture.
    fn inherited_callable_graph_checks_array_edges_in_base_index_values() {
        let declarations =
            parse_source_file("interface Base<T> { value: T; [index: number]: Array<number>; }");
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Derived extends Base<number> {}",
        ));
        assert!(
            declarations.diagnostics.is_empty(),
            "{:?}",
            declarations.diagnostics
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(196);
        let library_file = FileId::new(197);
        let mut binder = CanonicalBinder::new();
        for (file, source, is_declaration) in
            [(library_file, &declarations, true), (file, &parsed, false)]
        {
            binder
                .bind_source_file_with_facts(
                    &source.arena,
                    source.source_file,
                    file,
                    CanonicalSourceFileFacts::new(
                        EscapedName::source(if is_declaration {
                            "\"/project/index-base.d.ts\""
                        } else {
                            "\"/project/index-derived.ts\""
                        }),
                        CanonicalSourceLanguage::TypeScript,
                        is_declaration,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&source.arena, file)
                .unwrap();
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            [(library_file, &declarations.arena), (file, &parsed.arena)]
                .into_iter()
                .collect(),
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        let targets = CanonicalArrayTargets::from_global_types(context.global_types());
        let store = context.store_mut_for_test();
        let (derived, base, value) = inherited_graph_property(store);
        let index = store
            .type_payload(derived)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .index_infos
            .as_ref()
            .unwrap()[0];
        let array = store.index_info(index).unwrap().value_type();
        for warm in [false, true] {
            if warm {
                let mut session = super::super::instantiate::InstantiationSession::new(
                    super::super::instantiate::InstantiationLimits::default(),
                );
                super::super::instantiated_members::demand_instantiated_property_type(
                    store,
                    base,
                    value,
                    Some(targets),
                    &mut session,
                )
                .unwrap();
            }
            assert_eq!(
                store
                    .value_symbol_links(value)
                    .unwrap()
                    .resolved_type
                    .is_some(),
                warm
            );
            let before = (
                store.type_len(),
                store.symbol_len(),
                store.mapper_len(),
                store.signature_len(),
                store.index_info_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            );
            assert_eq!(
                store.validate_cached_array_capability_with_array_targets(targets, derived),
                Ok(()),
            );
            assert_eq!(
                store.validate_cached_array_capability(derived),
                Err(LiteralTypeCacheError::UnsupportedUnionConstituent(array)),
                "warm={warm}",
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.symbol_len(),
                    store.mapper_len(),
                    store.signature_len(),
                    store.index_info_len(),
                    store.symbol_store().symbol_table_len(),
                    store.checker_link_allocated_lengths(),
                    store.relation_state_snapshot(),
                ),
                before,
            );
        }
    }

    #[test]
    fn inherited_callable_graph_keeps_proxies_lazy_and_validates_warm_values() {
        let parsed = parse_source_file(concat!(
            "interface Base<T> { value: T; next(): T; } ",
            "interface Derived extends Base<number> { own: number; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(FileId::new(192), &parsed);
        context.check_source_file(FileId::new(192)).unwrap();
        let store = context.store_mut_for_test();
        let (derived, base, value) = inherited_graph_property(store);
        let next = store
            .type_payload(derived)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .members
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source("next"))
            .unwrap();
        let target = store.value_symbol_links(value).unwrap().target.unwrap();
        let template = store.value_symbol_links(target).unwrap().clone();
        let snapshot = |store: &TestStore| {
            (
                store.type_len(),
                store.symbol_len(),
                store.mapper_len(),
                store.signature_len(),
                store.index_info_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            )
        };
        for warm in [false, true] {
            if warm {
                for name in ["value", "next"] {
                    store
                        .resolve_generic_interface_property(base, name, None)
                        .unwrap()
                        .unwrap();
                }
            }
            assert_eq!(
                store
                    .value_symbol_links(value)
                    .unwrap()
                    .resolved_type
                    .is_some(),
                warm
            );
            assert_eq!(
                store
                    .value_symbol_links(next)
                    .unwrap()
                    .resolved_type
                    .is_some(),
                warm
            );
            let before = snapshot(store);
            for _ in 0..2 {
                assert_eq!(store.validate_cached_array_capability(derived), Ok(()));
                assert_eq!(store.validate_union_constituent(derived), Ok(()));
                assert_eq!(snapshot(store), before);
                assert_eq!(store.value_symbol_links(target), Some(&template));
                assert_eq!(
                    store
                        .value_symbol_links(value)
                        .unwrap()
                        .resolved_type
                        .is_some(),
                    warm
                );
                assert_eq!(
                    store
                        .value_symbol_links(next)
                        .unwrap()
                        .resolved_type
                        .is_some(),
                    warm
                );
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Each mutation must fail before the graph reader changes any cache.
    fn inherited_callable_graph_rejects_corrupt_proxy_and_template_caches() {
        #[derive(Clone, Copy, Debug)]
        enum Poison {
            Target,
            Mapper,
            Flags,
            Declaration,
            MissingTemplate,
            TemplateType,
            CachedValue,
            ExtraLink,
            MissingMember,
        }
        for warm in [false, true] {
            for poison in [
                Poison::Target,
                Poison::Mapper,
                Poison::Flags,
                Poison::Declaration,
                Poison::MissingTemplate,
                Poison::TemplateType,
                Poison::CachedValue,
                Poison::ExtraLink,
                Poison::MissingMember,
            ] {
                let parsed = parse_source_file(concat!(
                    "interface Base<T> { value: T; } ",
                    "interface Derived extends Base<number> { own: number; }",
                ));
                let mut context = checker_context(FileId::new(193), &parsed);
                context.check_source_file(FileId::new(193)).unwrap();
                let store = context.store_mut_for_test();
                let (derived, base, value) = inherited_graph_property(store);
                if warm {
                    store
                        .resolve_generic_interface_property(base, "value", None)
                        .unwrap()
                        .unwrap();
                }
                assert_eq!(store.validate_cached_array_capability(derived), Ok(()));
                let mut links = store.value_symbol_links(value).unwrap().clone();
                let target = links.target.unwrap();
                let string = store.intrinsic_bootstrap().unwrap().string_type;
                let owner = store.type_payload(derived).unwrap().symbol().unwrap();
                match poison {
                    Poison::Target => {
                        links.target = Some(owner);
                        assert!(store.set_value_symbol_links(value, links));
                    }
                    Poison::Mapper => {
                        let template = store
                            .value_symbol_links(target)
                            .unwrap()
                            .resolved_type
                            .unwrap();
                        links.mapper =
                            Some(store.new_type_mapper(vec![template], vec![string]).unwrap());
                        assert!(store.set_value_symbol_links(value, links));
                    }
                    Poison::Flags => {
                        let flags = store.symbol(value).unwrap().flags();
                        assert!(store.set_symbol_flags(value, flags, CheckFlags::NONE));
                    }
                    Poison::Declaration => {
                        let declaration = store.symbol(owner).unwrap().declarations().unwrap()[0];
                        assert!(store.set_symbol_declarations(
                            value,
                            Some(vec![declaration]),
                            Some(declaration)
                        ));
                    }
                    Poison::MissingTemplate | Poison::TemplateType => {
                        let mut links = store.value_symbol_links(target).unwrap().clone();
                        links.resolved_type =
                            matches!(poison, Poison::TemplateType).then_some(string);
                        assert!(store.set_value_symbol_links(target, links));
                    }
                    Poison::CachedValue => {
                        links.resolved_type = Some(string);
                        assert!(store.set_value_symbol_links(value, links));
                    }
                    Poison::ExtraLink => {
                        links.write_type = Some(string);
                        assert!(store.set_value_symbol_links(value, links));
                    }
                    Poison::MissingMember => {
                        assert!(
                            store.set_structured_type_members(base, None, None, None, None, None)
                        );
                    }
                }
                let snapshot = |store: &TestStore| {
                    (
                        store.type_len(),
                        store.symbol_len(),
                        store.mapper_len(),
                        store.signature_len(),
                        store.index_info_len(),
                        store.symbol_store().symbol_table_len(),
                        store.checker_link_allocated_lengths(),
                        store.relation_state_snapshot(),
                    )
                };
                let before = snapshot(store);
                for _ in 0..2 {
                    assert_eq!(
                        store.validate_cached_array_capability(derived),
                        Err(LiteralTypeCacheError::InvalidCachedUnion(derived)),
                        "warm={warm}, {poison:?}",
                    );
                    assert_eq!(
                        store.validate_union_constituent(derived),
                        Err(LiteralTypeCacheError::InvalidCachedUnion(derived)),
                        "warm={warm}, {poison:?}",
                    );
                    assert_eq!(snapshot(store), before, "warm={warm}, {poison:?}");
                }
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Array arguments and prepared-query ownership use the same lazy proxy.
    fn inherited_callable_graph_preserves_array_and_prepared_query_capabilities() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Base<T> { value: T; next(): T; } ",
            "interface Derived extends Base<Array<number>> { own: number; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(FileId::new(194), &parsed);
        context.check_source_file(FileId::new(194)).unwrap();
        let globals = context.global_types().clone();
        let targets = CanonicalArrayTargets::from_global_types(&globals);
        let store = context.store_mut_for_test();
        let (derived, base, value) = inherited_graph_property(store);
        let array = validate_direct_generic_reference(store, base)
            .unwrap()
            .type_arguments[0];
        let prepared = store
            .prepare_type_query_types_with_global_types(&[], &[], &[], 0, 0, &globals)
            .unwrap();
        let no_targets = store.prepare_type_query_types(&[], &[], &[], 0, 0).unwrap();
        let mut foreign = initialized(IntrinsicBootstrapOptions::default());
        let foreign_prepared = foreign
            .prepare_type_query_types(&[], &[], &[], 0, 0)
            .unwrap();
        let snapshot = |store: &TestStore| {
            (
                store.type_len(),
                store.symbol_len(),
                store.mapper_len(),
                store.signature_len(),
                store.index_info_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            )
        };
        for warm in [false, true] {
            if warm {
                let mut session = super::super::instantiate::InstantiationSession::new(
                    super::super::instantiate::InstantiationLimits::default(),
                );
                assert_eq!(
                    super::super::instantiated_members::demand_instantiated_property_type(
                        store,
                        base,
                        value,
                        Some(targets),
                        &mut session,
                    )
                    .unwrap(),
                    array,
                );
            }
            assert_eq!(
                store
                    .value_symbol_links(value)
                    .unwrap()
                    .resolved_type
                    .is_some(),
                warm
            );
            let before = snapshot(store);
            assert_eq!(
                store.validate_cached_array_capability(derived),
                Err(LiteralTypeCacheError::UnsupportedUnionConstituent(array)),
            );
            assert_eq!(
                store.validate_cached_array_capability_with_array_targets(targets, derived),
                Ok(()),
            );
            assert_eq!(
                store.validate_cached_array_capability_prepared(derived, Some(&globals), &prepared),
                Ok(()),
            );
            for (globals, prepared) in [
                (None, &prepared),
                (Some(&globals), &no_targets),
                (None, &foreign_prepared),
            ] {
                assert_eq!(
                    store.validate_cached_array_capability_prepared(derived, globals, prepared),
                    Err(LiteralTypeCacheError::InvalidPreparedQuery),
                );
            }
            assert_eq!(snapshot(store), before);
        }
    }

    #[test]
    fn inherited_callable_graph_checks_array_edges_in_lazy_method_templates() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Base<T> { value(input: T): Array<number>; } ",
            "interface Derived extends Base<number> { own: number; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(FileId::new(195), &parsed);
        context.check_source_file(FileId::new(195)).unwrap();
        let targets = CanonicalArrayTargets::from_global_types(context.global_types());
        let store = context.store_mut_for_test();
        let (derived, base, value) = inherited_graph_property(store);
        let target = store.value_symbol_links(value).unwrap().target.unwrap();
        let template = store
            .value_symbol_links(target)
            .unwrap()
            .resolved_type
            .unwrap();
        let signature = store
            .type_payload(template)
            .unwrap()
            .data()
            .structured()
            .unwrap()
            .signatures
            .as_ref()
            .unwrap()[0];
        let array = store
            .signature(signature)
            .unwrap()
            .resolved_return_type()
            .unwrap();
        let snapshot = |store: &TestStore| {
            (
                store.type_len(),
                store.symbol_len(),
                store.mapper_len(),
                store.signature_len(),
                store.index_info_len(),
                store.symbol_store().symbol_table_len(),
                store.checker_link_allocated_lengths(),
                store.relation_state_snapshot(),
            )
        };
        for warm in [false, true] {
            if warm {
                let mut session = super::super::instantiate::InstantiationSession::new(
                    super::super::instantiate::InstantiationLimits::default(),
                );
                super::super::instantiated_members::demand_instantiated_property_type(
                    store,
                    base,
                    value,
                    Some(targets),
                    &mut session,
                )
                .unwrap();
            }
            assert_eq!(
                store
                    .value_symbol_links(value)
                    .unwrap()
                    .resolved_type
                    .is_some(),
                warm
            );
            let before = snapshot(store);
            assert_eq!(
                store.validate_cached_array_capability(derived),
                Err(LiteralTypeCacheError::UnsupportedUnionConstituent(array)),
            );
            assert_eq!(
                store.validate_cached_array_capability_with_array_targets(targets, derived),
                Ok(()),
            );
            assert_eq!(snapshot(store), before);
            assert_eq!(
                store
                    .value_symbol_links(value)
                    .unwrap()
                    .resolved_type
                    .is_some(),
                warm
            );
        }
    }

    #[test]
    fn sparse_links_canonicalize_bootstrap_sentinel_id_encodings() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (resolving_signature, unknown_signature, any_signature, unknown_symbol) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.resolving_signature,
                bootstrap.unknown_signature,
                bootstrap.any_signature,
                bootstrap.unknown_symbol,
            )
        };
        let parsed = parse_source_file("factory();");
        let file = FileId::new(91);
        assert!(
            store
                .register_source_file(&parsed.arena, parsed.source_file, file)
                .is_some()
        );
        let call = parsed
            .arena
            .iter()
            .find_map(|(id, node)| (node.kind == SyntaxKind::CallExpression).then_some(id))
            .unwrap();
        let call = NodeRef::new(parsed.arena.id(), file, call);

        assert!(store.set_signature_links(
            call,
            SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolved(resolving_signature),
                effects_signature: EffectsSignatureState::Resolved(unknown_signature),
                decorator_signature: DecoratorSignatureState::Resolved(any_signature),
            }
        ));
        assert_eq!(
            store.signature_links(call),
            Some(&SignatureLinks {
                resolved_signature: ResolvedSignatureState::Resolving,
                effects_signature: EffectsSignatureState::NoEffects,
                decorator_signature: DecoratorSignatureState::NotApplicable,
            })
        );

        let alias = store
            .alloc_symbol(SymbolData::new(
                SymbolFlags::ALIAS,
                EscapedName::source("alias"),
            ))
            .unwrap();
        assert!(store.set_alias_symbol_links(
            alias,
            AliasSymbolLinks {
                alias_target: AliasTargetState::Resolved(unknown_symbol),
                ..AliasSymbolLinks::default()
            }
        ));
        assert_eq!(
            store.alias_symbol_links(alias).unwrap().alias_target,
            AliasTargetState::Unknown
        );
    }

    fn record(store: &TestStore, id: TypeId) -> &TypeRecord {
        store.type_payload(id).unwrap()
    }

    fn literal_data(store: &TestStore, id: TypeId) -> &LiteralTypeData {
        let TypeData::Literal(data) = record(store, id).data() else {
            panic!("expected literal payload")
        };
        data
    }

    fn union_types(store: &TestStore, id: TypeId) -> &[TypeId] {
        let TypeData::Union(data) = record(store, id).data() else {
            panic!("expected union payload")
        };
        &data.union.types
    }

    fn assert_intrinsic(
        store: &TestStore,
        id: TypeId,
        flags: TypeFlags,
        name: &str,
        object_flags: ObjectFlags,
    ) {
        let type_record = record(store, id);
        assert_eq!(type_record.flags(), flags);
        assert_eq!(type_record.object_flags(), object_flags);
        assert_eq!(type_record.symbol(), None);
        assert_eq!(type_record.alias(), None);
        let TypeData::Intrinsic(data) = type_record.data() else {
            panic!("expected intrinsic payload")
        };
        assert_eq!(data.intrinsic_name, name);
    }

    fn assert_union(
        store: &TestStore,
        id: TypeId,
        flags: TypeFlags,
        object_flags: ObjectFlags,
        types: &[TypeId],
    ) {
        assert_eq!(record(store, id).flags(), flags);
        assert_eq!(record(store, id).object_flags(), object_flags);
        assert_eq!(union_types(store, id), types);
    }

    fn semantic_counts(store: &TestStore) -> SemanticArenaCounts {
        SemanticArenaCounts {
            types: store.type_len(),
            mappers: store.mapper_len(),
            signatures: store.signature_len(),
            predicates: store.type_predicate_len(),
            index_infos: store.index_info_len(),
            type_aliases: store.type_alias_len(),
            conditional_roots: store.conditional_root_len(),
            entity_names: store.entity_name_len(),
        }
    }

    fn checker_state(store: &TestStore) -> CheckerStateSnapshot {
        let [
            node,
            symbol_node,
            type_node,
            enum_member,
            assertion,
            array_literal,
            switch_statement,
            jsx_element,
            signature,
            symbol_reference,
            value_symbol,
            mapped_symbol,
            deferred_symbol,
            alias_symbol,
            module_symbol,
            late_bound,
            export_type,
            members_and_exports,
            type_alias,
            declared_type,
            spread,
            variance,
            reverse_mapped_symbol,
            marked_assignment_symbol,
            containing_symbol,
            source_file,
        ] = store.checker_link_allocated_lengths();
        let (entries, resolution_start, boundaries, next_boundary_serial) =
            store.type_resolution_internal_state();
        let [
            source_callable_types,
            source_callable_declarations,
            source_callable_owners,
            source_callable_signatures,
            source_callable_type_parameters,
        ] = store.source_callable_provenance_lengths();
        CheckerStateSnapshot {
            checker_symbols: store.symbol_store().checker_created_symbol_len(),
            merged_symbols: store.merged_symbol_len(),
            source_callable_types,
            source_callable_declarations,
            source_callable_owners,
            source_callable_signatures,
            source_callable_type_parameters,
            cached_signatures: store.cached_signature_len(),
            callable_signature_parameter_types: store.callable_signature_parameter_types_len(),
            semantic_arenas: semantic_counts(store),
            links: CheckerLinkCounts {
                node,
                symbol_node,
                type_node,
                enum_member,
                assertion,
                array_literal,
                switch_statement,
                jsx_element,
                signature,
                symbol_reference,
                value_symbol,
                mapped_symbol,
                deferred_symbol,
                alias_symbol,
                module_symbol,
                late_bound,
                export_type,
                members_and_exports,
                type_alias,
                declared_type,
                spread,
                variance,
                reverse_mapped_symbol,
                marked_assignment_symbol,
                containing_symbol,
                source_file,
            },
            type_resolution: TypeResolutionStateSnapshot {
                entries,
                resolution_start,
                boundaries,
                next_boundary_serial,
            },
            relations: store.relation_state_snapshot(),
        }
    }

    fn assert_all_distinct(ids: &[TypeId]) {
        assert_eq!(ids.iter().copied().collect::<HashSet<_>>().len(), ids.len());
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One table pins the full upstream allocation sequence.
    fn strict_bootstrap_preserves_pinned_symbols_intrinsics_and_allocation_order() {
        let options = IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: true,
        };
        let store = initialized(options);
        let bootstrap = store.intrinsic_bootstrap().unwrap();

        assert_eq!(bootstrap.globals.get(), 1);
        assert_eq!(bootstrap.undefined_symbol.get(), 1);
        assert_eq!(bootstrap.arguments_symbol.get(), 2);
        assert_eq!(bootstrap.require_symbol.get(), 3);
        assert_eq!(bootstrap.unknown_symbol.get(), 4);
        assert_eq!(bootstrap.global_this_symbol.get(), 5);
        assert_eq!(bootstrap.empty_type_literal_symbol.get(), 6);
        for (id, name) in [
            (bootstrap.undefined_symbol, "undefined"),
            (bootstrap.arguments_symbol, "arguments"),
            (bootstrap.require_symbol, "require"),
            (bootstrap.unknown_symbol, "unknown"),
        ] {
            let symbol = store.symbol(id).unwrap();
            assert_eq!(
                symbol.flags(),
                SymbolFlags::PROPERTY | SymbolFlags::TRANSIENT
            );
            assert_eq!(symbol.check_flags(), CheckFlags::NONE);
            assert_eq!(symbol.name().as_utf8(), Some(name));
        }
        let global_this = store.symbol(bootstrap.global_this_symbol).unwrap();
        assert_eq!(
            global_this.flags(),
            SymbolFlags::MODULE | SymbolFlags::TRANSIENT,
        );
        assert_eq!(global_this.check_flags(), CheckFlags::READONLY);
        assert_eq!(global_this.exports(), Some(bootstrap.globals));
        assert_eq!(
            store
                .symbol_table(bootstrap.globals)
                .unwrap()
                .get_source("globalThis"),
            Some(bootstrap.global_this_symbol),
        );
        let type_literal = store.symbol(bootstrap.empty_type_literal_symbol).unwrap();
        assert_eq!(
            type_literal.flags(),
            SymbolFlags::TYPE_LITERAL | SymbolFlags::TRANSIENT,
        );
        assert_eq!(
            type_literal.name().as_bytes(),
            InternalSymbolName::Type.as_bytes(),
        );

        let allocated_in_order = [
            bootstrap.any_type,
            bootstrap.auto_type,
            bootstrap.wildcard_type,
            bootstrap.blocked_string_type,
            bootstrap.error_type,
            bootstrap.unresolved_type,
            bootstrap.non_inferrable_any_type,
            bootstrap.intrinsic_marker_type,
            bootstrap.unknown_type,
            bootstrap.undefined_type,
            bootstrap.missing_type,
            bootstrap.optional_type,
            bootstrap.null_type,
            bootstrap.string_type,
            bootstrap.number_type,
            bootstrap.bigint_type,
            bootstrap.regular_false_type,
            bootstrap.false_type,
            bootstrap.regular_true_type,
            bootstrap.true_type,
            bootstrap.boolean_type,
            bootstrap.es_symbol_type,
            bootstrap.void_type,
            bootstrap.never_type,
            bootstrap.silent_never_type,
            bootstrap.implicit_never_type,
            bootstrap.unreachable_never_type,
            bootstrap.non_primitive_type,
            bootstrap.string_or_number_type,
            bootstrap.string_number_symbol_type,
            bootstrap.number_or_bigint_type,
            bootstrap.numeric_string_type,
            bootstrap.template_constraint_type,
            bootstrap.unique_literal_type,
            bootstrap.empty_object_type,
            bootstrap.empty_jsx_object_type,
            bootstrap.empty_fresh_jsx_object_type,
            bootstrap.empty_type_literal_type,
            bootstrap.unknown_empty_object_type,
            bootstrap.unknown_union_type,
            bootstrap.empty_generic_type,
            bootstrap.any_function_type,
            bootstrap.no_constraint_type,
            bootstrap.circular_constraint_type,
            bootstrap.resolving_default_type,
            bootstrap.marker_super_type,
            bootstrap.marker_sub_type,
            bootstrap.marker_other_type,
            bootstrap.marker_super_type_for_check,
            bootstrap.marker_sub_type_for_check,
            bootstrap.empty_string_type,
            bootstrap.zero_type,
            bootstrap.zero_bigint_type,
        ];
        assert_eq!(
            allocated_in_order.map(TypeId::get),
            std::array::from_fn(|index| u32::try_from(index + 1).unwrap()),
        );
        assert_eq!(bootstrap.undefined_widening_type, bootstrap.undefined_type);
        assert_eq!(bootstrap.null_widening_type, bootstrap.null_type);
        assert_eq!(bootstrap.undefined_or_missing_type, bootstrap.missing_type);
        assert_eq!(bootstrap.typeof_type.get(), 62);
        assert_eq!(store.type_len(), 62);

        for (id, flags, name, object_flags) in [
            (bootstrap.any_type, TypeFlags::ANY, "any", ObjectFlags::NONE),
            (
                bootstrap.auto_type,
                TypeFlags::ANY,
                "any",
                ObjectFlags::NON_INFERRABLE_TYPE,
            ),
            (
                bootstrap.wildcard_type,
                TypeFlags::ANY,
                "any",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.blocked_string_type,
                TypeFlags::ANY,
                "any",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.error_type,
                TypeFlags::ANY,
                "error",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.unresolved_type,
                TypeFlags::ANY,
                "unresolved",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.non_inferrable_any_type,
                TypeFlags::ANY,
                "any",
                ObjectFlags::CONTAINS_WIDENING_TYPE,
            ),
            (
                bootstrap.intrinsic_marker_type,
                TypeFlags::ANY,
                "intrinsic",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.unknown_type,
                TypeFlags::UNKNOWN,
                "unknown",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.undefined_type,
                TypeFlags::UNDEFINED,
                "undefined",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.missing_type,
                TypeFlags::UNDEFINED,
                "undefined",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.optional_type,
                TypeFlags::UNDEFINED,
                "undefined",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.null_type,
                TypeFlags::NULL,
                "null",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.string_type,
                TypeFlags::STRING,
                "string",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.number_type,
                TypeFlags::NUMBER,
                "number",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.bigint_type,
                TypeFlags::BIG_INT,
                "bigint",
                ObjectFlags::NONE,
            ),
            (
                bootstrap.silent_never_type,
                TypeFlags::NEVER,
                "never",
                ObjectFlags::NON_INFERRABLE_TYPE,
            ),
            (
                bootstrap.non_primitive_type,
                TypeFlags::NON_PRIMITIVE,
                "object",
                ObjectFlags::NONE,
            ),
        ] {
            assert_intrinsic(&store, id, flags, name, object_flags);
        }
        assert_ne!(bootstrap.any_type, bootstrap.wildcard_type);
        assert_ne!(bootstrap.wildcard_type, bootstrap.blocked_string_type);
        assert_ne!(bootstrap.never_type, bootstrap.implicit_never_type);
        assert_ne!(
            bootstrap.implicit_never_type,
            bootstrap.unreachable_never_type
        );
        assert_ne!(bootstrap.unique_literal_type, bootstrap.never_type);
        assert_all_distinct(&[
            bootstrap.any_type,
            bootstrap.wildcard_type,
            bootstrap.blocked_string_type,
        ]);
        assert_all_distinct(&[
            bootstrap.undefined_type,
            bootstrap.missing_type,
            bootstrap.optional_type,
        ]);
        assert_all_distinct(&[
            bootstrap.never_type,
            bootstrap.implicit_never_type,
            bootstrap.unreachable_never_type,
            bootstrap.unique_literal_type,
        ]);
        assert_all_distinct(&[
            bootstrap.empty_object_type,
            bootstrap.empty_jsx_object_type,
            bootstrap.empty_fresh_jsx_object_type,
            bootstrap.unknown_empty_object_type,
            bootstrap.empty_generic_type,
            bootstrap.any_function_type,
            bootstrap.no_constraint_type,
            bootstrap.circular_constraint_type,
            bootstrap.resolving_default_type,
        ]);
        assert_all_distinct(&[
            bootstrap.marker_super_type,
            bootstrap.marker_sub_type,
            bootstrap.marker_other_type,
            bootstrap.marker_super_type_for_check,
            bootstrap.marker_sub_type_for_check,
        ]);
        assert_ne!(bootstrap.any_signature, bootstrap.resolving_signature);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Keeps interdependent identity assertions together.
    fn bootstrap_preserves_literal_union_object_and_sentinel_records() {
        let store = initialized(IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        });
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        assert_eq!(
            bootstrap.undefined_or_missing_type,
            bootstrap.undefined_type,
        );

        for (regular, fresh, value) in [
            (bootstrap.regular_false_type, bootstrap.false_type, false),
            (bootstrap.regular_true_type, bootstrap.true_type, true),
        ] {
            let regular_data = literal_data(&store, regular);
            assert_eq!(regular_data.value, LiteralValue::Boolean(value));
            assert_eq!(regular_data.regular_type, regular);
            assert_eq!(regular_data.fresh_type, Some(fresh));
            let fresh_data = literal_data(&store, fresh);
            assert_eq!(fresh_data.value, LiteralValue::Boolean(value));
            assert_eq!(fresh_data.regular_type, regular);
            assert_eq!(fresh_data.fresh_type, Some(fresh));
        }
        assert_eq!(
            record(&store, bootstrap.boolean_type).flags(),
            TypeFlags::UNION | TypeFlags::BOOLEAN,
        );
        assert_eq!(
            record(&store, bootstrap.boolean_type).object_flags(),
            ObjectFlags::PRIMITIVE_UNION,
        );
        assert_eq!(
            union_types(&store, bootstrap.boolean_type),
            [bootstrap.regular_false_type, bootstrap.regular_true_type],
        );
        assert_eq!(
            union_types(&store, bootstrap.string_or_number_type),
            [bootstrap.string_type, bootstrap.number_type],
        );
        assert_eq!(
            union_types(&store, bootstrap.string_number_symbol_type),
            [
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.es_symbol_type,
            ],
        );
        assert_eq!(
            union_types(&store, bootstrap.number_or_bigint_type),
            [bootstrap.number_type, bootstrap.bigint_type],
        );
        assert_eq!(
            union_types(&store, bootstrap.template_constraint_type),
            [
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
                bootstrap.regular_false_type,
                bootstrap.regular_true_type,
            ],
        );
        assert_eq!(
            union_types(&store, bootstrap.unknown_union_type),
            [
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.unknown_empty_object_type,
            ],
        );
        assert_eq!(
            record(&store, bootstrap.unknown_union_type).object_flags(),
            ObjectFlags::NONE,
        );
        assert_union(
            &store,
            bootstrap.boolean_type,
            TypeFlags::UNION | TypeFlags::BOOLEAN,
            ObjectFlags::PRIMITIVE_UNION,
            &[bootstrap.regular_false_type, bootstrap.regular_true_type],
        );
        for (id, types) in [
            (
                bootstrap.string_or_number_type,
                vec![bootstrap.string_type, bootstrap.number_type],
            ),
            (
                bootstrap.string_number_symbol_type,
                vec![
                    bootstrap.string_type,
                    bootstrap.number_type,
                    bootstrap.es_symbol_type,
                ],
            ),
            (
                bootstrap.number_or_bigint_type,
                vec![bootstrap.number_type, bootstrap.bigint_type],
            ),
            (
                bootstrap.template_constraint_type,
                vec![
                    bootstrap.undefined_type,
                    bootstrap.null_type,
                    bootstrap.string_type,
                    bootstrap.number_type,
                    bootstrap.bigint_type,
                    bootstrap.regular_false_type,
                    bootstrap.regular_true_type,
                ],
            ),
        ] {
            assert_union(
                &store,
                id,
                TypeFlags::UNION,
                ObjectFlags::PRIMITIVE_UNION,
                &types,
            );
        }
        assert_union(
            &store,
            bootstrap.unknown_union_type,
            TypeFlags::UNION,
            ObjectFlags::NONE,
            &[
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.unknown_empty_object_type,
            ],
        );
        let TypeData::TemplateLiteral(numeric_string) =
            record(&store, bootstrap.numeric_string_type).data()
        else {
            panic!("expected template literal payload")
        };
        assert_eq!(numeric_string.texts, ["", ""]);
        assert_eq!(numeric_string.types, [bootstrap.number_type]);

        for id in [
            bootstrap.empty_object_type,
            bootstrap.empty_jsx_object_type,
            bootstrap.empty_fresh_jsx_object_type,
            bootstrap.empty_type_literal_type,
            bootstrap.unknown_empty_object_type,
            bootstrap.empty_generic_type,
            bootstrap.any_function_type,
            bootstrap.no_constraint_type,
            bootstrap.circular_constraint_type,
            bootstrap.resolving_default_type,
        ] {
            let type_record = record(&store, id);
            assert!(type_record.object_flags().contains(ObjectFlags::ANONYMOUS));
            assert!(
                type_record
                    .object_flags()
                    .contains(ObjectFlags::MEMBERS_RESOLVED),
            );
            let TypeData::Object(data) = type_record.data() else {
                panic!("expected plain object payload")
            };
            assert_eq!(data.structured.members, None);
            assert_eq!(data.structured.properties, None);
            assert_eq!(data.structured.signatures, None);
            assert_eq!(data.structured.call_signature_count, 0);
            assert_eq!(data.structured.index_infos, None);
        }
        assert_eq!(
            record(&store, bootstrap.empty_type_literal_type).symbol(),
            Some(bootstrap.empty_type_literal_symbol),
        );
        let TypeData::Object(empty_generic) = record(&store, bootstrap.empty_generic_type).data()
        else {
            panic!("expected empty generic object")
        };
        assert!(matches!(
            &empty_generic.instantiations,
            TypeCacheState::Allocated(cache) if cache.is_empty()
        ));
        assert!(
            record(&store, bootstrap.any_function_type)
                .object_flags()
                .contains(ObjectFlags::NON_INFERRABLE_TYPE),
        );

        let TypeData::TypeParameter(marker_sub) = record(&store, bootstrap.marker_sub_type).data()
        else {
            panic!("expected marker type parameter")
        };
        assert_eq!(marker_sub.constraint, Some(bootstrap.marker_super_type));
        let TypeData::TypeParameter(marker_sub_for_check) =
            record(&store, bootstrap.marker_sub_type_for_check).data()
        else {
            panic!("expected check marker type parameter")
        };
        assert_eq!(
            marker_sub_for_check.constraint,
            Some(bootstrap.marker_super_type_for_check),
        );
        for id in [
            bootstrap.marker_super_type,
            bootstrap.marker_other_type,
            bootstrap.marker_super_type_for_check,
        ] {
            let TypeData::TypeParameter(data) = record(&store, id).data() else {
                panic!("expected marker type parameter")
            };
            assert_eq!(data.constraint, None);
            assert_eq!(data.target, None);
            assert_eq!(data.mapper, None);
            assert_eq!(data.resolved_default_type, None);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Pins every default in the sentinel record cluster.
    fn bootstrap_preserves_predicate_signature_index_and_literal_tail_defaults() {
        let store = initialized(IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        });
        let bootstrap = store.intrinsic_bootstrap().unwrap();

        let predicate = store.type_predicate(bootstrap.no_type_predicate).unwrap();
        assert_eq!(predicate.kind(), TypePredicateKind::Identifier);
        assert_eq!(predicate.parameter_index(), 0);
        assert_eq!(predicate.parameter_name(), "<<unresolved>>");
        assert_eq!(predicate.type_id(), Some(bootstrap.any_type));
        for (id, return_type) in [
            (bootstrap.any_signature, bootstrap.any_type),
            (bootstrap.unknown_signature, bootstrap.error_type),
            (bootstrap.resolving_signature, bootstrap.any_type),
            (
                bootstrap.silent_never_signature,
                bootstrap.silent_never_type,
            ),
        ] {
            let signature = store.signature(id).unwrap();
            assert_eq!(signature.flags(), SignatureFlags::NONE);
            assert_eq!(signature.min_argument_count(), 0);
            assert_eq!(signature.resolved_min_argument_count(), -1);
            assert_eq!(signature.declaration(), None);
            assert!(signature.type_parameters().is_empty());
            assert!(signature.parameters().is_empty());
            assert_eq!(signature.this_parameter(), None);
            assert_eq!(signature.resolved_return_type(), Some(return_type));
            assert_eq!(signature.resolved_type_predicate(), None);
            assert_eq!(signature.target(), None);
            assert_eq!(signature.mapper(), None);
            assert_eq!(signature.isolated_signature_type(), None);
            assert_eq!(signature.composite(), None);
        }
        let enum_index = store.index_info(bootstrap.enum_number_index_info).unwrap();
        assert_eq!(enum_index.key_type(), bootstrap.number_type);
        assert_eq!(enum_index.value_type(), bootstrap.string_type);
        assert!(enum_index.is_readonly());
        assert_eq!(enum_index.declaration(), None);
        assert_eq!(enum_index.index_symbol(), None);
        assert!(enum_index.components().is_empty());
        let any_base_index = store
            .index_info(bootstrap.any_base_type_index_info)
            .unwrap();
        assert_eq!(any_base_index.key_type(), bootstrap.string_type);
        assert_eq!(any_base_index.value_type(), bootstrap.any_type);
        assert!(!any_base_index.is_readonly());

        assert_eq!(
            literal_data(&store, bootstrap.empty_string_type).value,
            LiteralValue::String(String::new()),
        );
        assert_eq!(
            literal_data(&store, bootstrap.zero_type).value,
            LiteralValue::Number(Number::new(0.0)),
        );
        assert_eq!(
            literal_data(&store, bootstrap.zero_bigint_type).value,
            LiteralValue::BigInt(PseudoBigInt::default()),
        );
        for id in [
            bootstrap.empty_string_type,
            bootstrap.zero_type,
            bootstrap.zero_bigint_type,
        ] {
            let data = literal_data(&store, id);
            assert_eq!(data.regular_type, id);
            assert_eq!(data.fresh_type, None);
        }
        let typeof_values = union_types(&store, bootstrap.typeof_type)
            .iter()
            .map(|id| match &literal_data(&store, *id).value {
                LiteralValue::String(value) => value.as_str(),
                _ => panic!("typeof witness must be a string literal"),
            })
            .collect::<Vec<_>>();
        assert_eq!(
            typeof_values,
            [
                "bigint",
                "boolean",
                "function",
                "number",
                "object",
                "string",
                "symbol",
                "undefined",
            ],
        );
        assert_eq!(
            record(&store, bootstrap.typeof_type).object_flags(),
            ObjectFlags::PRIMITIVE_UNION,
        );
        assert_eq!(bootstrap.string_literal_cache_len(), 9);
        assert_eq!(bootstrap.number_literal_cache_len(), 1);
        assert_eq!(bootstrap.bigint_literal_cache_len(), 1);
        assert_eq!(bootstrap.union_cache_len(), 7);
        assert_eq!(bootstrap.template_literal_cache_len(), 1);
        assert_eq!(
            bootstrap.cached_string_literal_type(""),
            Some(bootstrap.empty_string_type),
        );
        assert_eq!(
            bootstrap.cached_number_literal_type(Number::new(0.0)),
            Some(bootstrap.zero_type),
        );
        assert_eq!(
            bootstrap.cached_number_literal_type(Number::new(-0.0)),
            Some(bootstrap.zero_type),
        );
        assert_eq!(bootstrap.cached_number_literal_type(Number::nan()), None);
        assert_eq!(
            bootstrap.cached_bigint_literal_type(&PseudoBigInt::default()),
            Some(bootstrap.zero_bigint_type),
        );
        for id in union_types(&store, bootstrap.typeof_type) {
            let LiteralValue::String(value) = &literal_data(&store, *id).value else {
                panic!("typeof witness must be a string literal")
            };
            assert_eq!(bootstrap.cached_string_literal_type(value), Some(*id));
        }
        for id in [
            bootstrap.boolean_type,
            bootstrap.string_or_number_type,
            bootstrap.string_number_symbol_type,
            bootstrap.number_or_bigint_type,
            bootstrap.template_constraint_type,
            bootstrap.unknown_union_type,
            bootstrap.typeof_type,
        ] {
            assert_eq!(
                bootstrap.cached_union_type(union_types(&store, id)),
                Some(id),
            );
        }
        assert_eq!(
            bootstrap.cached_template_literal_type(
                &[String::new(), String::new()],
                &[bootstrap.number_type],
            ),
            Some(bootstrap.numeric_string_type),
        );
    }

    #[test]
    fn non_strict_bootstrap_preserves_widening_and_nullable_reduction_identity() {
        let store = initialized(IntrinsicBootstrapOptions::default());
        let bootstrap = store.intrinsic_bootstrap().unwrap();

        assert_ne!(bootstrap.undefined_widening_type, bootstrap.undefined_type);
        assert_ne!(bootstrap.null_widening_type, bootstrap.null_type);
        assert_intrinsic(
            &store,
            bootstrap.undefined_widening_type,
            TypeFlags::UNDEFINED,
            "undefined",
            ObjectFlags::CONTAINS_WIDENING_TYPE,
        );
        assert_intrinsic(
            &store,
            bootstrap.null_widening_type,
            TypeFlags::NULL,
            "null",
            ObjectFlags::CONTAINS_WIDENING_TYPE,
        );
        assert_eq!(
            bootstrap.undefined_or_missing_type,
            bootstrap.undefined_type,
        );
        assert_eq!(bootstrap.unknown_union_type, bootstrap.unknown_type);
        assert_eq!(
            union_types(&store, bootstrap.template_constraint_type),
            [
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.bigint_type,
                bootstrap.regular_false_type,
                bootstrap.regular_true_type,
            ],
        );
        assert_eq!(bootstrap.undefined_widening_type.get(), 11);
        assert_eq!(bootstrap.null_widening_type.get(), 15);
        assert_eq!(bootstrap.empty_generic_type.get(), 42);
        assert_eq!(bootstrap.typeof_type.get(), 63);
        assert_eq!(store.type_len(), 63);
        assert_eq!(bootstrap.union_cache_len(), 6);
        assert_eq!(
            bootstrap.cached_union_type(union_types(&store, bootstrap.template_constraint_type,)),
            Some(bootstrap.template_constraint_type),
        );
        assert_eq!(
            bootstrap.cached_union_type(&[
                bootstrap.undefined_type,
                bootstrap.null_type,
                bootstrap.unknown_empty_object_type,
            ]),
            None,
        );
    }

    #[test]
    fn union_validation_admits_only_the_canonical_loose_nullish_widening_pair() {
        let store = initialized(IntrinsicBootstrapOptions::default());
        let bootstrap = store.intrinsic_bootstrap().unwrap();

        assert_eq!(
            store.validate_union_constituent(bootstrap.null_widening_type),
            Ok(()),
        );
        assert_eq!(
            store.validate_union_constituent(bootstrap.undefined_widening_type),
            Ok(()),
        );
        assert_eq!(
            store.validate_union_constituent(bootstrap.missing_type),
            Ok(())
        );
        assert_eq!(
            store.validate_union_constituent(bootstrap.optional_type),
            Err(LiteralTypeCacheError::UnsupportedUnionConstituent(
                bootstrap.optional_type
            )),
        );
    }

    #[test]
    fn indexed_access_missing_type_retains_its_identity_in_each_optional_mode() {
        for (strict_null_checks, exact_optional_property_types) in
            [(false, false), (false, true), (true, false), (true, true)]
        {
            let mut store = initialized(IntrinsicBootstrapOptions {
                strict_null_checks,
                exact_optional_property_types,
            });
            let (missing, optional, string) = {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                (
                    bootstrap.missing_type,
                    bootstrap.optional_type,
                    bootstrap.string_type,
                )
            };

            assert_eq!(
                store.validate_union_constituent(optional),
                Err(LiteralTypeCacheError::UnsupportedUnionConstituent(optional)),
            );
            assert_eq!(store.validate_union_constituent(missing), Ok(()));
            let union = store.literal_union_type(&[string, missing], None).unwrap();
            if strict_null_checks {
                assert_eq!(union_types(&store, union), &[missing, string]);
            } else {
                assert_eq!(union, string);
            }
            let warm = (
                store.type_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            );
            assert_eq!(
                store.literal_union_type(&[string, missing], None),
                Ok(union)
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.intrinsic_bootstrap().unwrap().union_cache_len()
                ),
                warm
            );
        }
    }

    #[test]
    fn initialization_is_idempotent_and_rejections_are_atomic() {
        let mut store = TestStore::new();
        let options = IntrinsicBootstrapOptions::default();
        let first = store.initialize_intrinsic_bootstrap(options).unwrap() as *const _;
        let state = checker_state(&store);
        let symbol_count = store.symbol_len();
        let table_count = store.symbol_store().symbol_table_len();
        let second = store.initialize_intrinsic_bootstrap(options).unwrap() as *const _;
        assert_eq!(first, second);
        assert_eq!(checker_state(&store), state);
        assert_eq!(store.symbol_len(), symbol_count);
        assert_eq!(store.symbol_store().symbol_table_len(), table_count);

        let requested = IntrinsicBootstrapOptions {
            strict_null_checks: true,
            exact_optional_property_types: false,
        };
        assert_eq!(
            store.initialize_intrinsic_bootstrap(requested),
            Err(IntrinsicBootstrapError::OptionsMismatch {
                initialized: options,
                requested,
            }),
        );
        assert_eq!(checker_state(&store), state);
        assert_eq!(store.symbol_len(), symbol_count);
        assert_eq!(store.symbol_store().symbol_table_len(), table_count);

        let mut occupied = TestStore::new();
        let preexisting = occupied
            .alloc_intrinsic_type(TypeFlags::ANY, "preexisting")
            .unwrap();
        let before = checker_state(&occupied);
        assert_eq!(
            occupied.initialize_intrinsic_bootstrap(options),
            Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                before,
            ))),
        );
        assert_eq!(checker_state(&occupied), before);
        assert_eq!(occupied.symbol_len(), 0);
        assert_eq!(occupied.symbol_store().symbol_table_len(), 0);
        assert_eq!(
            record(&occupied, preexisting).data(),
            &TypeData::Intrinsic(super::super::type_records::IntrinsicTypeData {
                intrinsic_name: "preexisting".to_owned(),
            }),
        );
        assert!(occupied.intrinsic_bootstrap().is_none());

        let mut mapper_occupied = TestStore::new();
        mapper_occupied
            .new_type_mapper(Vec::new(), Vec::new())
            .unwrap();
        let mut signature_occupied = TestStore::new();
        signature_occupied
            .alloc_signature(
                SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                None,
                None,
                0,
            )
            .unwrap();
        let mut predicate_occupied = TestStore::new();
        predicate_occupied
            .alloc_type_predicate(TypePredicateKind::Identifier, 0, "occupied", None)
            .unwrap();
        let mut alias_occupied = TestStore::new();
        alias_occupied.alloc_type_alias(None).unwrap();
        let mut index_occupied = TestStore::new();
        let index_type = index_occupied
            .alloc_intrinsic_type(TypeFlags::STRING, "string")
            .unwrap();
        index_occupied
            .alloc_index_info(index_type, index_type, false, None, Vec::new())
            .unwrap();
        let mut occupied_stores = Vec::with_capacity(5);
        occupied_stores.push(mapper_occupied);
        occupied_stores.push(signature_occupied);
        occupied_stores.push(predicate_occupied);
        occupied_stores.push(alias_occupied);
        occupied_stores.push(index_occupied);
        for mut occupied in occupied_stores {
            let before = checker_state(&occupied);
            let symbol_count = occupied.symbol_len();
            let table_count = occupied.symbol_store().symbol_table_len();
            assert!(!before.is_pristine());
            assert_eq!(
                occupied.initialize_intrinsic_bootstrap(options),
                Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                    before,
                ))),
            );
            assert_eq!(checker_state(&occupied), before);
            assert_eq!(occupied.symbol_len(), symbol_count);
            assert_eq!(occupied.symbol_store().symbol_table_len(), table_count);
            assert!(occupied.intrinsic_bootstrap().is_none());
        }
    }

    #[test]
    fn prebound_binder_symbols_and_tables_are_allowed_and_preserved() {
        let mut symbols = SymbolStore::new();
        let bound_symbol = symbols
            .alloc_symbol(SymbolData::new(
                SymbolFlags::CLASS,
                EscapedName::source("bound"),
            ))
            .unwrap();
        let private_name = symbols
            .private_identifier_name(bound_symbol, "#field")
            .unwrap();
        assert!(private_name.as_ref().is_private_identifier());
        let bound_global_id = symbols.global_symbol_id(bound_symbol).unwrap();
        let bound_table = symbols.alloc_symbol_table();
        assert_eq!(
            symbols.insert_symbol(bound_table, EscapedName::source("bound"), bound_symbol,),
            Some(None),
        );
        let mut store = TestStore::from_symbol_store(symbols);
        let parsed = parse_source_file("const prebound = 1;");
        assert!(store.register_ast_scope(AstScope::new(FileId::new(0), &parsed.arena,)));

        store
            .initialize_intrinsic_bootstrap(IntrinsicBootstrapOptions::default())
            .unwrap();
        assert_eq!(store.global_symbol_id(bound_symbol), Some(bound_global_id));
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        assert_eq!(bootstrap.undefined_symbol.get(), bound_symbol.get() + 1);
        assert_eq!(bootstrap.globals.get(), bound_table.get() + 1);
        assert_eq!(
            store.symbol(bound_symbol).unwrap().name().as_utf8(),
            Some("bound"),
        );
        assert_eq!(
            store.symbol_table(bound_table).unwrap().get_source("bound"),
            Some(bound_symbol),
        );
        assert_eq!(
            store
                .symbol_table(bootstrap.globals)
                .unwrap()
                .get_source("globalThis"),
            Some(bootstrap.global_this_symbol),
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Exercises every disjoint checker-owned side store.
    fn sparse_links_and_resolution_state_reject_bootstrap_atomically() {
        let options = IntrinsicBootstrapOptions::default();
        let parsed = parse_source_file(
            "enum E { A } const asserted = value as string; const array = [...items]; \
             switch (value) { case 0: break; } factory();",
        );
        let file = FileId::new(0);
        let mut symbols = SymbolStore::new();
        let linked_symbol = symbols
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::source("linked"),
            ))
            .unwrap();
        let mut linked = TestStore::from_symbol_store(symbols);
        let source_file = linked
            .register_source_file(&parsed.arena, parsed.source_file, file)
            .unwrap();
        let node = source_file.node_ref();
        let node_of_kind = |kind| {
            let node = parsed
                .arena
                .iter()
                .find_map(|(id, node)| (node.kind == kind).then_some(id))
                .unwrap_or_else(|| panic!("parsed source must contain {kind:?}"));
            NodeRef::new(parsed.arena.id(), file, node)
        };
        assert!(linked.register_entity_name_text("factory").is_some());
        assert!(linked.ensure_node_links(node));
        assert!(linked.ensure_symbol_node_links(node));
        assert!(linked.ensure_type_node_links(node));
        assert!(linked.ensure_enum_member_links(node_of_kind(SyntaxKind::EnumMember)));
        assert!(linked.ensure_assertion_links(node_of_kind(SyntaxKind::AsExpression)));
        assert!(
            linked.ensure_array_literal_links(node_of_kind(SyntaxKind::ArrayLiteralExpression))
        );
        assert!(linked.ensure_switch_statement_links(node_of_kind(SyntaxKind::SwitchStatement)));
        assert!(linked.ensure_jsx_element_links(node));
        assert!(linked.ensure_signature_links(node_of_kind(SyntaxKind::CallExpression)));
        assert!(linked.ensure_symbol_reference_links(linked_symbol));
        assert!(linked.ensure_value_symbol_links(linked_symbol));
        assert!(linked.ensure_mapped_symbol_links(linked_symbol));
        assert!(linked.ensure_deferred_symbol_links(linked_symbol));
        assert!(linked.ensure_alias_symbol_links(linked_symbol));
        assert!(linked.ensure_module_symbol_links(linked_symbol));
        assert!(linked.ensure_late_bound_links(linked_symbol));
        assert!(linked.ensure_export_type_links(linked_symbol));
        assert!(linked.ensure_members_and_exports_links(linked_symbol));
        assert!(linked.ensure_type_alias_links(linked_symbol));
        assert!(linked.ensure_declared_type_links(linked_symbol));
        assert!(linked.ensure_spread_links(linked_symbol));
        assert!(linked.ensure_variance_links(linked_symbol));
        assert!(linked.ensure_reverse_mapped_symbol_links(linked_symbol));
        assert!(linked.ensure_marked_assignment_symbol_links(linked_symbol));
        assert!(linked.ensure_containing_symbol_links(linked_symbol));
        assert!(linked.ensure_source_file_links(source_file));
        let before = checker_state(&linked);
        assert_eq!(before.semantic_arenas.entity_names, 1);
        assert_eq!(
            before.links,
            CheckerLinkCounts {
                node: 1,
                symbol_node: 1,
                type_node: 1,
                enum_member: 1,
                assertion: 1,
                array_literal: 1,
                switch_statement: 1,
                jsx_element: 1,
                signature: 1,
                symbol_reference: 1,
                value_symbol: 1,
                mapped_symbol: 1,
                deferred_symbol: 1,
                alias_symbol: 1,
                module_symbol: 1,
                late_bound: 1,
                export_type: 1,
                members_and_exports: 1,
                type_alias: 1,
                declared_type: 1,
                spread: 1,
                variance: 1,
                reverse_mapped_symbol: 1,
                marked_assignment_symbol: 1,
                containing_symbol: 1,
                source_file: 1,
            },
        );
        assert_eq!(
            linked.initialize_intrinsic_bootstrap(options),
            Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                before,
            ))),
        );
        assert_eq!(checker_state(&linked), before);
        assert!(linked.node_links(node).is_some());
        assert_eq!(linked.symbol_len(), 1);
        assert_eq!(linked.symbol_store().symbol_table_len(), 0);

        let mut symbols = SymbolStore::new();
        let symbol = symbols
            .alloc_symbol(SymbolData::new(
                SymbolFlags::PROPERTY,
                EscapedName::source("resolving"),
            ))
            .unwrap();
        let mut resolving = TestStore::from_symbol_store(symbols);
        assert_eq!(
            resolving.push_type_resolution(
                crate::semantic::TypeResolutionTarget::Symbol(symbol),
                crate::semantic::TypeSystemPropertyName::Type,
            ),
            Ok(true),
        );
        let before = checker_state(&resolving);
        assert_eq!(before.type_resolution.entries, 1);
        assert_eq!(
            resolving.initialize_intrinsic_bootstrap(options),
            Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                before,
            ))),
        );
        assert_eq!(checker_state(&resolving), before);
        assert_eq!(resolving.pop_type_resolution(), Some(true));

        let mut bounded = TestStore::new();
        let boundary = bounded.reset_type_resolution_start();
        let before = checker_state(&bounded);
        assert_eq!(before.type_resolution.boundaries, 1);
        assert_eq!(before.type_resolution.next_boundary_serial, 1);
        assert_eq!(
            bounded.initialize_intrinsic_bootstrap(options),
            Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                before,
            ))),
        );
        assert_eq!(checker_state(&bounded), before);
        assert!(bounded.restore_type_resolution_start(boundary).is_ok());

        let mut boundary_history = TestStore::new();
        let boundary = boundary_history.reset_type_resolution_start();
        assert!(
            boundary_history
                .restore_type_resolution_start(boundary)
                .is_ok(),
        );
        let before = checker_state(&boundary_history);
        assert_eq!(before.type_resolution.boundaries, 0);
        assert_eq!(before.type_resolution.next_boundary_serial, 1);
        assert_eq!(
            boundary_history.initialize_intrinsic_bootstrap(options),
            Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                before,
            ))),
        );
        assert_eq!(checker_state(&boundary_history), before);

        let mut symbols = SymbolStore::new();
        let enum_source = symbols
            .alloc_symbol(SymbolData::new(
                SymbolFlags::REGULAR_ENUM,
                EscapedName::source("Source"),
            ))
            .unwrap();
        let enum_target = symbols
            .alloc_symbol(SymbolData::new(
                SymbolFlags::REGULAR_ENUM,
                EscapedName::source("Target"),
            ))
            .unwrap();
        let mut related = TestStore::from_symbol_store(symbols);
        let relation_key = crate::semantic::CacheHashKey::from_halves(1, 2);
        for relation in crate::semantic::RelationKind::ALL {
            related.relation_cache_set(
                relation,
                relation_key,
                crate::semantic::RelationComparisonResult::SUCCEEDED,
            );
        }
        assert!(related.enum_relation_cache_set(
            enum_source,
            enum_target,
            crate::semantic::RelationComparisonResult::FAILED,
        ));
        let before = checker_state(&related);
        assert_eq!(before.relations.subtype.entries, 1);
        assert_eq!(before.relations.strict_subtype.entries, 1);
        assert_eq!(before.relations.assignable.entries, 1);
        assert_eq!(before.relations.comparable.entries, 1);
        assert_eq!(before.relations.identity.entries, 1);
        assert_eq!(before.relations.enum_relation_entries, 1);
        assert_eq!(
            related.initialize_intrinsic_bootstrap(options),
            Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                before,
            ))),
        );
        assert_eq!(checker_state(&related), before);
        for relation in crate::semantic::RelationKind::ALL {
            assert_eq!(
                related.relation_cache_get(relation, relation_key),
                crate::semantic::RelationComparisonResult::SUCCEEDED
            );
        }
        assert_eq!(
            related.enum_relation_cache_get(enum_source, enum_target),
            Some(crate::semantic::RelationComparisonResult::FAILED)
        );

        let mut symbols = SymbolStore::new();
        let _ = symbols.alloc_transient_symbol(
            SymbolFlags::PROPERTY,
            EscapedName::source("premature"),
            CheckFlags::NONE,
        );
        let mut transient = TestStore::from_symbol_store(symbols);
        let before = checker_state(&transient);
        assert_eq!(before.checker_symbols, 1);
        assert_eq!(
            transient.initialize_intrinsic_bootstrap(options),
            Err(IntrinsicBootstrapError::NonPristineCheckerState(Box::new(
                before,
            ))),
        );
        assert_eq!(checker_state(&transient), before);
    }

    #[test]
    fn every_bootstrap_handle_is_store_branded() {
        let first = initialized(IntrinsicBootstrapOptions::default());
        let first_bootstrap = first.intrinsic_bootstrap().unwrap();
        let any_type = first_bootstrap.any_type;
        let global_this_symbol = first_bootstrap.global_this_symbol;
        let globals = first_bootstrap.globals;
        let predicate = first_bootstrap.no_type_predicate;
        let signature = first_bootstrap.any_signature;
        let index_info = first_bootstrap.enum_number_index_info;
        let boolean_constituents = union_types(&first, first_bootstrap.boolean_type).to_vec();
        let number_type = first_bootstrap.number_type;

        let second = initialized(IntrinsicBootstrapOptions::default());
        let second_bootstrap = second.intrinsic_bootstrap().unwrap();
        assert_eq!(any_type.get(), second_bootstrap.any_type.get());
        assert_ne!(any_type, second_bootstrap.any_type);
        assert!(second.type_payload(any_type).is_none());
        assert!(second.symbol(global_this_symbol).is_none());
        assert!(second.symbol_table(globals).is_none());
        assert!(second.type_predicate(predicate).is_none());
        assert!(second.signature(signature).is_none());
        assert!(second.index_info(index_info).is_none());
        assert_eq!(
            second_bootstrap.cached_union_type(&boolean_constituents),
            None,
        );
        assert_eq!(
            second_bootstrap
                .cached_template_literal_type(&[String::new(), String::new()], &[number_type],),
            None,
        );
    }

    #[test]
    fn union_cache_rejects_wrong_generator_flags_atomically_and_accepts_repair() {
        for corruption in 0..4 {
            let mut store = initialized(IntrinsicBootstrapOptions::default());
            let (string_type, number_type) = {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                (bootstrap.string_type, bootstrap.number_type)
            };
            let types = vec![string_type, number_type];
            let malformed = store
                .alloc_union_type(
                    if corruption == 0 {
                        ObjectFlags::NONE
                    } else {
                        ObjectFlags::PRIMITIVE_UNION
                    },
                    types.clone(),
                )
                .unwrap();
            match corruption {
                0 => {}
                1 => assert!(store.add_type_flags(malformed, TypeFlags::ENUM_LITERAL)),
                2 => assert!(
                    store.add_type_object_flags(malformed, ObjectFlags::NON_INFERRABLE_TYPE,)
                ),
                3 => assert!(
                    store.add_type_object_flags(malformed, ObjectFlags::CONTAINS_INTERSECTIONS,)
                ),
                _ => unreachable!(),
            }
            let key = UnionTypeCacheKey::anonymous(types.clone());
            store
                .intrinsic_bootstrap
                .as_mut()
                .unwrap()
                .union_types
                .insert(key.clone(), malformed);
            store.mark_union_cache_validation_dirty();
            let before = (
                store.type_len(),
                store.type_alias_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            );
            assert_eq!(
                store.prepare_type_query_types(&[], &[], &[], 1, 0),
                Err(LiteralTypeCacheError::InvalidCachedUnion(malformed)),
            );
            assert_eq!(
                (
                    store.type_len(),
                    store.type_alias_len(),
                    store.intrinsic_bootstrap().unwrap().union_cache_len(),
                ),
                before,
            );

            let repaired = store
                .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, types)
                .unwrap();
            store
                .intrinsic_bootstrap
                .as_mut()
                .unwrap()
                .union_types
                .insert(key, repaired);
            assert!(store.prepare_type_query_types(&[], &[], &[], 1, 0).is_ok());
        }
    }

    #[test]
    fn index_origin_unions_use_exact_origin_identity_and_validate_warm_hits() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (string_type, number_type) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let target = store
            .alloc_interface_type(ObjectFlags::INTERFACE, None)
            .unwrap();
        let types = [string_type, number_type];

        let mut first_query = store.prepare_type_query_types(&[], &[], &[], 1, 0).unwrap();
        let first_origin = store.alloc_index_type(target, IndexFlags::NONE).unwrap();
        let first = store
            .literal_union_type_prepared_with_index_origin(&types, first_origin, &mut first_query)
            .unwrap();
        let TypeData::Union(first_data) = store.type_payload(first).unwrap().data() else {
            panic!("two primitive keys must remain a union");
        };
        assert_eq!(first_data.origin, Some(first_origin));

        let mut warm_query = store.prepare_type_query_types(&[], &[], &[], 1, 0).unwrap();
        assert_eq!(
            store
                .literal_union_type_prepared_with_index_origin(
                    &types,
                    first_origin,
                    &mut warm_query,
                )
                .unwrap(),
            first,
        );

        let mut second_query = store.prepare_type_query_types(&[], &[], &[], 1, 0).unwrap();
        let second_origin = store.alloc_index_type(target, IndexFlags::NONE).unwrap();
        let second = store
            .literal_union_type_prepared_with_index_origin(&types, second_origin, &mut second_query)
            .unwrap();
        assert_ne!(second, first);
        let TypeData::Union(second_data) = store.type_payload(second).unwrap().data() else {
            panic!("two primitive keys must remain a union");
        };
        assert_eq!(second_data.origin, Some(second_origin));
    }

    #[test]
    fn cyclic_union_origins_fail_typed_cache_validation_without_recursing_forever() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (string_type, number_type) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let leaves = vec![string_type, number_type];
        let left = store
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, leaves.clone())
            .unwrap();
        let right = store
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, leaves)
            .unwrap();
        assert!(store.set_union_caches(
            left,
            None,
            None,
            Some(right),
            EscapedName::default(),
            ConstituentMapState::Unallocated,
        ));
        assert!(store.set_union_caches(
            right,
            None,
            None,
            Some(left),
            EscapedName::default(),
            ConstituentMapState::Unallocated,
        ));
        let types = vec![left, right];
        let cached = store
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, types.clone())
            .unwrap();
        store
            .intrinsic_bootstrap
            .as_mut()
            .unwrap()
            .union_types
            .insert(UnionTypeCacheKey::anonymous(types), cached);
        store.mark_union_cache_validation_dirty();
        let before = store.type_len();
        assert_eq!(
            store.prepare_type_query_types(&[], &[], &[], 1, 0),
            Err(LiteralTypeCacheError::InvalidCachedUnion(cached)),
        );
        assert_eq!(store.type_len(), before);
    }

    #[test]
    fn union_cache_rejects_noncanonical_alias_owners_and_accepts_canonical_repair() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (string_type, number_type) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let canonical = store.alloc_transient_symbol(
            SymbolFlags::TYPE_ALIAS,
            EscapedName::source("Canonical"),
            CheckFlags::NONE,
        );
        let raw = store.alloc_transient_symbol(
            SymbolFlags::TYPE_ALIAS,
            EscapedName::source("Raw"),
            CheckFlags::NONE,
        );
        store.record_merged_symbol(canonical, raw).unwrap();
        let types = vec![string_type, number_type];
        let malformed = store
            .alloc_union_type(ObjectFlags::PRIMITIVE_UNION, types.clone())
            .unwrap();
        let malformed_alias = store.alloc_type_alias(Some(raw)).unwrap();
        assert!(store.set_type_alias(malformed, Some(malformed_alias)));
        let malformed_key = UnionTypeCacheKey {
            types: types.clone(),
            origin: None,
            alias: Some(UnionAliasCacheKey::new(raw, &[])),
        };
        store
            .intrinsic_bootstrap
            .as_mut()
            .unwrap()
            .union_types
            .insert(malformed_key.clone(), malformed);
        store.mark_union_cache_validation_dirty();
        let before = store.type_len();
        assert_eq!(
            store.prepare_type_query_types(&[], &[], &[], 1, 1),
            Err(LiteralTypeCacheError::InvalidCachedUnion(malformed)),
        );
        assert_eq!(store.type_len(), before);

        let cache = &mut store.intrinsic_bootstrap.as_mut().unwrap().union_types;
        cache.remove(&malformed_key);
        store.literal_union_type(&types, Some(canonical)).unwrap();
        assert!(store.prepare_type_query_types(&[], &[], &[], 1, 1).is_ok());
    }

    #[test]
    fn union_alias_keys_keep_ordered_arguments_in_both_union_caches() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (string, number, boolean, string_or_number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_type,
                bootstrap.number_type,
                bootstrap.boolean_type,
                bootstrap.string_or_number_type,
            )
        };
        let symbol = store.alloc_transient_symbol(
            SymbolFlags::TYPE_ALIAS,
            EscapedName::source("Choice"),
            CheckFlags::NONE,
        );
        for types in [vec![string, number], vec![string_or_number, boolean]] {
            let forward = store
                .literal_union_type_with_alias_and_array_targets(
                    &types,
                    Some((symbol, &[string, number])),
                    None,
                )
                .unwrap();
            let reverse = store
                .literal_union_type_with_alias_and_array_targets(
                    &types,
                    Some((symbol, &[number, string])),
                    None,
                )
                .unwrap();
            assert_ne!(forward, reverse);
            assert_eq!(union_types(&store, forward), union_types(&store, reverse));
            assert_eq!(
                store.validate_union_alias_identity(forward, symbol, &[string, number]),
                Ok(())
            );
            assert_eq!(
                store.validate_union_alias_identity(reverse, symbol, &[number, string]),
                Ok(())
            );
            let before = (store.type_len(), store.type_alias_len());
            for (arguments, expected) in [([string, number], forward), ([number, string], reverse)]
            {
                assert_eq!(
                    store.literal_union_type_with_alias_and_array_targets(
                        &types,
                        Some((symbol, &arguments)),
                        None,
                    ),
                    Ok(expected),
                );
            }
            assert_eq!((store.type_len(), store.type_alias_len()), before);
        }
    }

    #[test]
    fn union_alias_argument_and_owner_forgery_fail_before_query_writes() {
        for corruption in 0..3 {
            let mut store = initialized(IntrinsicBootstrapOptions::default());
            let (string, number) = {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                (bootstrap.string_type, bootstrap.number_type)
            };
            let symbol = store.alloc_transient_symbol(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source("Choice"),
                CheckFlags::NONE,
            );
            let other = store.alloc_transient_symbol(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source("Other"),
                CheckFlags::NONE,
            );
            let union = store
                .literal_union_type_with_alias_and_array_targets(
                    &[string, number],
                    Some((symbol, &[string, number])),
                    None,
                )
                .unwrap();
            let alias = store.type_payload(union).unwrap().alias().unwrap();
            match corruption {
                0 => assert!(store.set_type_alias_arguments(alias, Some(vec![number, string]))),
                1 => assert!(store.set_type_alias_arguments(alias, None)),
                2 => {
                    let forged = store.alloc_type_alias(Some(other)).unwrap();
                    assert!(store.set_type_alias_arguments(forged, Some(vec![string, number])));
                    assert!(store.set_type_alias(union, Some(forged)));
                }
                _ => unreachable!(),
            }
            let before = (store.type_len(), store.type_alias_len());
            assert_eq!(
                store.literal_union_type_with_alias_and_array_targets(
                    &[string, number],
                    Some((symbol, &[string, number])),
                    None,
                ),
                Err(LiteralTypeCacheError::InvalidCachedUnion(union)),
            );
            assert_eq!((store.type_len(), store.type_alias_len()), before);
            assert!(store.set_type_alias_arguments(alias, Some(vec![string, number])));
            assert!(store.set_type_alias(union, Some(alias)));
            assert_eq!(
                store.literal_union_type_with_alias_and_array_targets(
                    &[string, number],
                    Some((symbol, &[string, number])),
                    None,
                ),
                Ok(union),
            );
        }
    }

    #[test]
    fn anonymous_union_origin_creation_rejects_origin_and_cache_key_forgery() {
        let parsed = parse_source_file(concat!(
            "type Named<T> = T | string; ",
            "interface Holder<T> { value: Named<T> | boolean }",
        ));
        let file = FileId::new(157);
        let mut context = checker_context(file, &parsed);
        let property_type = parsed
            .arena
            .iter()
            .find_map(|(_, record)| {
                let NodeData::PropertyDeclaration(property) = &record.data else {
                    return None;
                };
                property
                    .type_
                    .map(|type_| NodeRef::new(parsed.arena.id(), file, type_))
            })
            .unwrap();
        let union = context.get_type_from_type_node(property_type).unwrap();
        let targets = CanonicalArrayTargets::from_global_types(context.global_types());
        let store = context.store_mut_for_test();
        let record = store.type_payload(union).unwrap();
        let TypeData::Union(data) = record.data() else {
            panic!("the property must retain its union")
        };
        assert!(record.alias().is_none());
        let origin = data
            .origin
            .expect("the named constituent must retain its origin");
        let parameter = data
            .union
            .types
            .iter()
            .copied()
            .find(|type_| {
                matches!(
                    store.type_payload(*type_).map(TypeRecord::data),
                    Some(TypeData::TypeParameter(_))
                )
            })
            .unwrap();
        let mapper = store.new_simple_type_mapper(parameter, parameter).unwrap();
        assert_eq!(
            crate::semantic::instantiate::instantiated_member_type_matches(
                store,
                union,
                union,
                mapper,
                Some(targets)
            ),
            Ok(true)
        );
        let original_key = store
            .intrinsic_bootstrap
            .as_ref()
            .unwrap()
            .union_types
            .iter()
            .find_map(|(key, type_)| (*type_ == union).then(|| key.clone()))
            .unwrap();
        assert!(original_key.alias.is_none());
        assert!(original_key.origin.is_some());
        let mut forged_key = original_key.clone();
        forged_key.origin = None;
        assert!(store.set_union_caches(
            union,
            None,
            None,
            None,
            EscapedName::default(),
            ConstituentMapState::Unallocated
        ));
        let cache = &mut store.intrinsic_bootstrap.as_mut().unwrap().union_types;
        cache.remove(&original_key);
        cache.insert(forged_key.clone(), union);
        store.mark_union_cache_validation_dirty();
        let before = (
            store.type_len(),
            store.type_alias_len(),
            store.mapper_len(),
            store.checker_link_allocated_lengths(),
        );
        assert_eq!(
            store.validate_cached_union_result_with_array_targets(targets, union, None),
            Err(LiteralTypeCacheError::InvalidCachedUnion(union))
        );
        assert!(
            crate::semantic::instantiate::instantiated_member_type_matches(
                store,
                union,
                union,
                mapper,
                Some(targets)
            )
            .is_err()
        );
        let mut session = crate::semantic::instantiate::InstantiationSession::new(
            crate::semantic::instantiate::InstantiationLimits::default(),
        );
        assert!(
            crate::semantic::instantiate::instantiate_type_with_session(
                store,
                union,
                mapper,
                Some(targets),
                &mut session
            )
            .is_err()
        );
        assert_eq!(session.query_count(), 0);
        assert_eq!(session.total_count(), 0);
        assert_eq!(
            (
                store.type_len(),
                store.type_alias_len(),
                store.mapper_len(),
                store.checker_link_allocated_lengths()
            ),
            before
        );
        assert!(context.get_type_from_type_node(property_type).is_err());
        let store = context.store_mut_for_test();
        assert_eq!(
            (
                store.type_len(),
                store.type_alias_len(),
                store.mapper_len(),
                store.checker_link_allocated_lengths()
            ),
            before
        );
        assert!(store.set_union_caches(
            union,
            None,
            None,
            Some(origin),
            EscapedName::default(),
            ConstituentMapState::Unallocated
        ));
        let cache = &mut store.intrinsic_bootstrap.as_mut().unwrap().union_types;
        cache.remove(&forged_key);
        cache.insert(original_key, union);
        assert_eq!(context.get_type_from_type_node(property_type), Ok(union));
    }

    #[test]
    fn union_alias_creation_rejects_alias_and_cache_key_forgery_together() {
        for corruption in 0..4 {
            let mut store = initialized(IntrinsicBootstrapOptions::default());
            let (string, number, boolean) = {
                let bootstrap = store.intrinsic_bootstrap().unwrap();
                (
                    bootstrap.string_type,
                    bootstrap.number_type,
                    bootstrap.boolean_type,
                )
            };
            let named_symbol = store.alloc_transient_symbol(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source("Named"),
                CheckFlags::NONE,
            );
            let owner = store.alloc_transient_symbol(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source("Choice"),
                CheckFlags::NONE,
            );
            let other = store.alloc_transient_symbol(
                SymbolFlags::TYPE_ALIAS,
                EscapedName::source("Other"),
                CheckFlags::NONE,
            );
            let named = store
                .literal_union_type(&[string, number], Some(named_symbol))
                .unwrap();
            let union = store
                .literal_union_type_with_alias_and_array_targets(
                    &[named, boolean],
                    Some((owner, &[string, number])),
                    None,
                )
                .unwrap();
            let original_key = store
                .intrinsic_bootstrap
                .as_ref()
                .unwrap()
                .union_types
                .iter()
                .find_map(|(key, value)| (*value == union).then(|| key.clone()))
                .unwrap();
            let identity = store.type_payload(union).unwrap().alias().unwrap();
            let mut forged_key = original_key.clone();
            match corruption {
                0 => {
                    assert!(store.set_type_alias_arguments(identity, Some(vec![number, string])));
                    forged_key.alias = Some(UnionAliasCacheKey::new(owner, &[number, string]));
                }
                1 => {
                    let forged_identity = store.alloc_type_alias(Some(other)).unwrap();
                    assert!(
                        store.set_type_alias_arguments(forged_identity, Some(vec![string, number]))
                    );
                    assert!(store.set_type_alias(union, Some(forged_identity)));
                    forged_key.alias = Some(UnionAliasCacheKey::new(other, &[string, number]));
                }
                2 => {
                    assert!(store.set_union_caches(
                        union,
                        None,
                        None,
                        None,
                        EscapedName::default(),
                        ConstituentMapState::Unallocated
                    ));
                    forged_key.origin = None;
                }
                3 => {
                    assert!(store.set_type_alias(union, None));
                    forged_key.alias = None;
                }
                _ => unreachable!(),
            }
            let cache = &mut store.intrinsic_bootstrap.as_mut().unwrap().union_types;
            cache.remove(&original_key);
            cache.insert(forged_key, union);
            store.mark_union_cache_validation_dirty();
            let before = (store.type_len(), store.type_alias_len(), store.mapper_len());
            assert_eq!(
                store.validate_cached_union_result(union, None),
                Err(LiteralTypeCacheError::InvalidCachedUnion(union))
            );
            assert!(store.prepare_type_query_types(&[], &[], &[], 1, 1).is_err());
            assert_eq!(
                (store.type_len(), store.type_alias_len(), store.mapper_len()),
                before
            );
        }
    }

    #[test]
    fn union_alias_foreign_arguments_are_rejected_without_publication() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let foreign = initialized(IntrinsicBootstrapOptions::default());
        let foreign_type = foreign.intrinsic_bootstrap().unwrap().string_type;
        let (string, number) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.string_type, bootstrap.number_type)
        };
        let symbol = store.alloc_transient_symbol(
            SymbolFlags::TYPE_ALIAS,
            EscapedName::source("Choice"),
            CheckFlags::NONE,
        );
        let before = (store.type_len(), store.type_alias_len());
        assert_eq!(
            store.literal_union_type_with_alias_and_array_targets(
                &[string, number],
                Some((symbol, &[foreign_type])),
                None,
            ),
            Err(LiteralTypeCacheError::InvalidUnionAlias(symbol)),
        );
        assert_eq!((store.type_len(), store.type_alias_len()), before);
    }

    #[test]
    fn lazy_union_memo_and_member_flags_do_not_rescan_a_growing_union_cache() {
        let mut store = initialized(IntrinsicBootstrapOptions {
            strict_null_checks: true,
            ..IntrinsicBootstrapOptions::default()
        });
        let number_type = store.intrinsic_bootstrap().unwrap().number_type;
        let baseline_scans = store.union_cache_validation_scan_count();
        let baseline_unions = store.intrinsic_bootstrap().unwrap().union_cache_len();

        for index in 0..32 {
            let literal = store
                .regular_string_literal_type(format!("memo-{index}"))
                .unwrap();
            let union = store
                .literal_union_type(&[literal, number_type], None)
                .unwrap();
            let flags = store.type_payload(union).unwrap().object_flags();

            assert!(
                !store.set_type_object_flags(union, flags | ObjectFlags::IS_UNKNOWN_LIKE_UNION,)
            );
            let _ = store.is_type_assignable_to(number_type, union);
            assert!(
                store
                    .type_payload(union)
                    .unwrap()
                    .object_flags()
                    .intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED)
            );
            assert_eq!(
                store.literal_union_type(&[literal, number_type], None),
                Ok(union),
            );
            assert!(store.set_structured_type_members(union, None, None, None, None, None));
            assert_eq!(
                store.literal_union_type(&[literal, number_type], None),
                Ok(union),
            );
            assert!(!store.union_cache_needs_validation);
        }

        assert_eq!(store.union_cache_validation_scan_count(), baseline_scans);
        assert_eq!(
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
            baseline_unions + 32,
        );
        assert!(store.prepare_type_query_types(&[], &[], &[], 1, 0).is_ok());
        assert_eq!(store.union_cache_validation_scan_count(), baseline_scans);
    }

    #[test]
    fn typeof_union_accepts_pinned_cached_literals_without_fresh_peers() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (typeof_type, bigint_type, zero_type, typeof_literals) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let TypeData::Union(data) = store.type_payload(bootstrap.typeof_type).unwrap().data()
            else {
                panic!("typeofType must be a union")
            };
            (
                bootstrap.typeof_type,
                bootstrap.bigint_type,
                bootstrap.zero_type,
                data.union.types.clone(),
            )
        };
        assert!(typeof_literals.iter().all(|literal| {
            matches!(
                store.type_payload(*literal).map(TypeRecord::data),
                Some(TypeData::Literal(LiteralTypeData {
                    fresh_type: None,
                    ..
                }))
            )
        }));
        assert_eq!(
            store.validate_cached_union_result(typeof_type, None),
            Ok(())
        );
        assert_eq!(store.validate_union_constituent(zero_type), Ok(()));

        let combined = store
            .literal_union_type(&[typeof_type, bigint_type], None)
            .unwrap();
        assert!(matches!(
            store.type_payload(combined).map(TypeRecord::data),
            Some(TypeData::Union(_))
        ));
        assert!(typeof_literals.iter().all(|literal| {
            matches!(
                store.type_payload(*literal).map(TypeRecord::data),
                Some(TypeData::Literal(LiteralTypeData {
                    fresh_type: None,
                    ..
                }))
            )
        }));
    }

    #[test]
    fn union_of_union_cache_rejects_a_valid_but_unrelated_result_without_writes() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let (first, second, forged) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.string_or_number_type,
                bootstrap.bigint_type,
                bootstrap.boolean_type,
            )
        };
        let (first, second) = if first < second {
            (first, second)
        } else {
            (second, first)
        };
        let key = UnionOfUnionCacheKey {
            first,
            second,
            reduction: UnionReduction::Literal,
            alias: None,
        };
        store
            .intrinsic_bootstrap
            .as_mut()
            .unwrap()
            .union_of_union_types
            .insert(key, forged);
        store.mark_union_cache_validation_dirty();
        let before = (
            store.type_len(),
            store.type_alias_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
            store
                .intrinsic_bootstrap()
                .unwrap()
                .union_of_union_cache_len(),
        );

        assert_eq!(
            store.literal_union_type(&[first, second], None),
            Err(LiteralTypeCacheError::InvalidCachedUnion(forged))
        );
        assert_eq!(
            (
                store.type_len(),
                store.type_alias_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
                store
                    .intrinsic_bootstrap()
                    .unwrap()
                    .union_of_union_cache_len(),
            ),
            before
        );
    }

    #[test]
    fn structured_expression_unions_flatten_sort_and_reuse_normalized_identity() {
        let parsed = parse_source_file(concat!(
            "const first: any = { id: 1 };",
            "const second: any = { id: 2, name: 'ok' };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(141);
        let mut context = checker_context(file, &parsed);
        context.check_source_file(file).unwrap();
        let first = checked_expression_type(&context, variable_initializer(&parsed, file, "first"));
        let second =
            checked_expression_type(&context, variable_initializer(&parsed, file, "second"));
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let store = context.store_mut_for_test();

        let nested = store
            .expression_union_type(&[second, number], UnionReduction::None)
            .unwrap();
        assert_eq!(union_types(store, nested), &[number, second]);
        let flattened = store
            .expression_union_type(&[first, nested, first], UnionReduction::None)
            .unwrap();
        assert_eq!(union_types(store, flattened), &[number, first, second]);
        let flags = record(store, flattened).object_flags();
        assert!(flags.contains(ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL));
        assert!(!flags.intersects(ObjectFlags::PRIMITIVE_UNION));

        let warm = (
            store.type_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
            store
                .intrinsic_bootstrap()
                .unwrap()
                .union_of_union_cache_len(),
        );
        assert_eq!(
            store
                .expression_union_type(&[nested, second, first], UnionReduction::None)
                .unwrap(),
            flattened
        );
        assert_eq!(
            (
                store.type_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
                store
                    .intrinsic_bootstrap()
                    .unwrap()
                    .union_of_union_cache_len(),
            ),
            warm
        );
    }

    #[test]
    fn derived_object_union_constituents_require_valid_cache_provenance() {
        let parsed = parse_source_file("const value: any = { missing: undefined };");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(145);
        let mut context = checker_context(file, &parsed);
        context.check_source_file(file).unwrap();
        let fresh = checked_expression_type(&context, variable_initializer(&parsed, file, "value"));
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let store = context.store_mut_for_test();
        let regular = store.get_regular_type_of_object_literal(fresh).unwrap();
        let widened = store.get_widened_type(regular).unwrap();
        assert_ne!(fresh, regular);
        assert_ne!(regular, widened);

        assert_eq!(store.validate_union_constituent(regular), Ok(()));
        assert_eq!(store.validate_union_constituent(widened), Ok(()));
        let regular_union = store
            .expression_union_type(&[number, regular], UnionReduction::None)
            .unwrap();
        let widened_union = store
            .expression_union_type(&[number, widened], UnionReduction::None)
            .unwrap();
        assert_eq!(union_types(store, regular_union), &[number, regular]);
        assert_eq!(union_types(store, widened_union), &[number, widened]);

        let warm = (
            store.type_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        );
        assert_eq!(
            store.expression_union_type(&[widened, number], UnionReduction::None),
            Ok(widened_union),
        );
        assert_eq!(
            (
                store.type_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ),
            warm,
        );

        let property = record(store, widened)
            .data()
            .structured()
            .and_then(|structured| structured.properties.as_deref())
            .and_then(|properties| properties.first())
            .copied()
            .unwrap();
        let original_links = store.value_symbol_links(property).unwrap().clone();
        let mut poisoned_links = original_links.clone();
        poisoned_links.resolved_type = Some(number);
        assert!(store.set_value_symbol_links(property, poisoned_links));
        assert_eq!(
            store.validate_union_constituent(widened),
            Err(LiteralTypeCacheError::InvalidCachedUnion(widened)),
        );
        assert!(store.set_value_symbol_links(property, original_links));
        assert_eq!(store.validate_union_constituent(widened), Ok(()));

        let (owner, members, properties) = {
            let regular_record = record(store, regular);
            let TypeData::Object(object) = regular_record.data() else {
                panic!("a regular object literal must retain its object payload")
            };
            (
                regular_record.symbol().unwrap(),
                object.structured.members,
                object.structured.properties.clone(),
            )
        };
        let forged = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(owner))
            .unwrap();
        assert!(store.set_structured_type_members(forged, members, properties, None, None, None,));
        assert_eq!(
            store.validate_union_constituent(forged),
            Err(LiteralTypeCacheError::UnsupportedUnionConstituent(forged)),
        );
    }

    #[test]
    fn record_callback_union_constituents_validate_pending_and_warm_caches() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {}\n",
            "type Record<K extends keyof any, T> = { [P in K]: T };\n",
            "declare function accept(value: ",
            "Record<string, (value: string) => void> | ",
            "Array<(value: number) => void>): void;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(146);
        let mut context = checker_context(file, &parsed);
        context.check_source_file(file).unwrap();

        let union_node = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                (record.kind == SyntaxKind::UnionType).then_some(NodeRef::new(
                    parsed.arena.id(),
                    file,
                    node,
                ))
            })
            .expect("the callable parameter has one union annotation");
        let union = context
            .store()
            .type_node_links(union_node)
            .and_then(|links| links.resolved_type)
            .expect("the callable parameter union was checked");
        let mapped = union_types(context.store(), union)
            .iter()
            .copied()
            .find(|type_| {
                matches!(
                    context.store().type_payload(*type_).map(TypeRecord::data),
                    Some(TypeData::Mapped(_))
                )
            })
            .expect("the union retains its Record constituent");
        let targets = CanonicalArrayTargets::from_global_types(context.global_types());
        assert_eq!(
            context
                .store()
                .validate_union_constituent_with_array_targets(targets, union),
            Ok(()),
        );

        let warm = (
            context.store().type_len(),
            context.store().mapper_len(),
            context.store().signature_len(),
            context
                .store()
                .intrinsic_bootstrap()
                .unwrap()
                .union_cache_len(),
        );
        context.recheck_source_file(file).unwrap();
        assert_eq!(
            (
                context.store().type_len(),
                context.store().mapper_len(),
                context.store().signature_len(),
                context
                    .store()
                    .intrinsic_bootstrap()
                    .unwrap()
                    .union_cache_len(),
            ),
            warm,
        );

        let store = context.store_mut_for_test();
        let (alias, parameter) = {
            let mapped_record = record(store, mapped);
            let TypeData::Mapped(data) = mapped_record.data() else {
                unreachable!("mapped constituent was identified above")
            };
            (
                store
                    .type_alias(mapped_record.alias().unwrap())
                    .unwrap()
                    .symbol()
                    .unwrap(),
                data.type_parameter.unwrap(),
            )
        };
        let (constraint, target, instantiation_mapper, default_type) = {
            let TypeData::TypeParameter(data) = record(store, parameter).data() else {
                unreachable!("Record instantiation retains a cloned type parameter")
            };
            (
                data.constraint,
                data.target,
                data.mapper,
                data.resolved_default_type,
            )
        };
        assert!(store.set_type_parameter_resolution(
            parameter,
            constraint,
            target,
            None,
            default_type,
        ));
        assert_eq!(
            store.validate_union_constituent_with_array_targets(targets, mapped),
            Err(LiteralTypeCacheError::InvalidCachedUnion(mapped)),
        );
        assert!(store.set_type_parameter_resolution(
            parameter,
            constraint,
            target,
            instantiation_mapper,
            default_type,
        ));
        assert_eq!(
            store.validate_union_constituent_with_array_targets(targets, mapped),
            Ok(()),
        );

        let original_links = store.type_alias_links(alias).unwrap().clone();
        let mut poisoned_links = original_links.clone();
        poisoned_links
            .instantiations
            .as_mut()
            .unwrap()
            .retain(|_, cached| *cached != mapped);
        assert!(store.set_type_alias_links(alias, poisoned_links));
        assert_eq!(
            store.validate_union_constituent_with_array_targets(targets, mapped),
            Err(LiteralTypeCacheError::InvalidCachedUnion(mapped)),
        );
        assert!(store.set_type_alias_links(alias, original_links));
        assert_eq!(
            store.validate_union_constituent_with_array_targets(targets, mapped),
            Ok(()),
        );
    }

    fn deferred_indexed_union_context(
        parsed: &ParseResult,
        exact_optional_property_types: bool,
    ) -> (CanonicalCheckerContext<'_>, NodeRef, TypeId, TypeId) {
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(197);
        let mut context = CanonicalCheckerContext::new(
            completed_bindings(file, parsed),
            [(file, &parsed.arena)].into_iter().collect(),
            IntrinsicBootstrapOptions {
                strict_null_checks: true,
                exact_optional_property_types,
            },
        )
        .unwrap();
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let node = |kind| {
            parsed
                .arena
                .iter()
                .find_map(|(node, record)| {
                    (record.kind == kind).then_some(NodeRef::new(parsed.arena.id(), file, node))
                })
                .unwrap()
        };
        let indexed_node = node(SyntaxKind::IndexedAccessType);
        let indexed = context
            .store()
            .type_node_links(indexed_node)
            .unwrap()
            .resolved_type
            .unwrap();
        let mapped = context
            .store()
            .type_node_links(node(SyntaxKind::MappedType))
            .unwrap()
            .resolved_type
            .unwrap();
        let TypeData::Mapped(mapped) = context.store().type_payload(mapped).unwrap().data() else {
            panic!("the source must retain its mapped type")
        };
        let template = mapped.template_type.unwrap();
        (context, indexed_node, indexed, template)
    }

    fn deferred_indexed_union_snapshot(store: &TestStore) -> (CheckerStateSnapshot, usize, usize) {
        (
            checker_state(store),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
            store
                .intrinsic_bootstrap()
                .unwrap()
                .union_of_union_cache_len(),
        )
    }

    fn assert_deferred_indexed_union_rejected(
        store: &mut TestStore,
        indexed: TypeId,
        template: TypeId,
        sentinel: TypeId,
    ) {
        let before = deferred_indexed_union_snapshot(store);
        assert!(store.validate_union_constituent(indexed).is_err());
        assert!(canonical_anonymous_union(store, &[template, sentinel]).is_err());
        assert_eq!(deferred_indexed_union_snapshot(store), before);
    }

    #[test]
    fn deferred_indexed_union_inputs_preserve_source_identity_and_warm_caches() {
        for body in [
            "interface Wrapper<T> { value: T } \
             type Soft<Model> = { [Key in keyof Model]?: Wrapper<Model[Key]> };",
            "interface Input { readonly [key: string]: number | undefined } \
             type Preserved = { [Key in keyof Input]+?: Input[Key] };",
        ] {
            let parsed = parse_source_file(&format!(
                "interface Array<T> {{}} interface ReadonlyArray<T> {{}} {body}",
            ));
            for exact in [false, true] {
                let (mut context, _, indexed, template) =
                    deferred_indexed_union_context(&parsed, exact);
                let store = context.store_mut_for_test();
                let sentinel = store
                    .intrinsic_bootstrap()
                    .unwrap()
                    .undefined_or_missing_type;
                let indexed_snapshot = |store: &TestStore| {
                    let record = store.type_payload(indexed).unwrap();
                    let TypeData::IndexedAccess(data) = record.data() else {
                        panic!("the deferred operand must keep its indexed-access record");
                    };
                    (
                        record.id(),
                        record.flags(),
                        record.object_flags(),
                        record.symbol(),
                        record.alias(),
                        data.clone(),
                    )
                };
                let indexed_record = indexed_snapshot(store);
                let before = deferred_indexed_union_snapshot(store);
                assert_eq!(store.validate_union_constituent(indexed), Ok(()));
                assert_eq!(deferred_indexed_union_snapshot(store), before);
                let union = canonical_anonymous_union(store, &[template, sentinel]).unwrap();
                assert_eq!(union_types(store, union).len(), 2);
                assert!(union_types(store, union).contains(&template));
                assert!(union_types(store, union).contains(&sentinel));

                let warm = deferred_indexed_union_snapshot(store);
                for _ in 0..2 {
                    assert_eq!(store.validate_union_constituent(indexed), Ok(()));
                    assert_eq!(store.validate_union_constituent(union), Ok(()));
                    assert_eq!(
                        canonical_anonymous_union(store, &[sentinel, template]),
                        Ok(union),
                    );
                    assert_eq!(deferred_indexed_union_snapshot(store), warm);
                    assert_eq!(indexed_snapshot(store), indexed_record);
                }
            }
        }
    }

    #[test]
    fn deferred_indexed_union_rejects_stale_source_ownership_and_warm_metadata() {
        for body in [
            "interface Wrapper<T> { value: T } \
             type Soft<Model> = { [Key in keyof Model]?: Wrapper<Model[Key]> };",
            "interface Input { readonly [key: string]: number | undefined } \
             type Preserved = { [Key in keyof Input]+?: Input[Key] };",
        ] {
            let parsed = parse_source_file(&format!(
                "interface Array<T> {{}} interface ReadonlyArray<T> {{}} {body}",
            ));
            let (mut context, indexed_node, indexed, template) =
                deferred_indexed_union_context(&parsed, true);
            let store = context.store_mut_for_test();
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            let sentinel = bootstrap.undefined_or_missing_type;
            let number = bootstrap.number_type;
            let union = canonical_anonymous_union(store, &[template, sentinel]).unwrap();
            let TypeData::IndexedAccess(data) = store.type_payload(indexed).unwrap().data() else {
                panic!("the source must retain its deferred indexed access")
            };
            let object = data.object_type;
            let key = data.index_type;
            let key_owner = cached_ordinary_type_parameter_owner(store, key).unwrap();
            let declarations = store
                .symbol(key_owner)
                .unwrap()
                .declarations()
                .unwrap()
                .to_vec();
            let object_owner = store.type_payload(object).unwrap().symbol().unwrap();
            let borrowed = store
                .symbol(object_owner)
                .unwrap()
                .declarations()
                .unwrap()
                .to_vec();
            assert!(store.set_symbol_declarations(key_owner, Some(borrowed), None));
            assert_deferred_indexed_union_rejected(store, indexed, template, sentinel);
            assert!(store.set_symbol_declarations(key_owner, Some(declarations), None));

            let links = store.declared_type_links(key_owner).unwrap().clone();
            let mut wrong_links = links.clone();
            wrong_links.declared_type = Some(number);
            assert!(store.set_declared_type_links(key_owner, wrong_links));
            assert_deferred_indexed_union_rejected(store, indexed, template, sentinel);
            assert!(store.set_declared_type_links(key_owner, links));

            assert!(store.set_type_symbol(indexed, Some(key_owner)));
            assert_deferred_indexed_union_rejected(store, indexed, template, sentinel);
            assert!(store.set_type_symbol(indexed, None));
            let alias = store.alloc_type_alias(None).unwrap();
            assert!(store.set_type_alias(indexed, Some(alias)));
            assert_deferred_indexed_union_rejected(store, indexed, template, sentinel);
            assert!(store.set_type_alias(indexed, None));
            assert!(store.set_resolved_base_constraint(indexed, Some(number)));
            assert_deferred_indexed_union_rejected(store, indexed, template, sentinel);
            assert!(store.set_resolved_base_constraint(indexed, None));

            if template == indexed {
                let links = store.type_node_links(indexed_node).unwrap().clone();
                let mut wrong_links = links.clone();
                wrong_links.resolved_type = Some(number);
                assert!(store.set_type_node_links(indexed_node, wrong_links));
                assert_deferred_indexed_union_rejected(store, indexed, template, sentinel);
                assert!(store.set_type_node_links(indexed_node, links));
            }
            let repaired = deferred_indexed_union_snapshot(store);
            assert_eq!(
                canonical_anonymous_union(store, &[template, sentinel]),
                Ok(union),
            );
            assert_eq!(deferred_indexed_union_snapshot(store), repaired);
        }
    }

    #[test]
    fn deferred_indexed_union_rejects_wrong_operands_and_duplicate_identity() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Wrapper<T> { value: T } ",
            "type Soft<Model> = { [Key in keyof Model]?: Wrapper<Model[Key]> };",
        ));
        let (mut context, _, indexed, template) = deferred_indexed_union_context(&parsed, true);
        let store = context.store_mut_for_test();
        let bootstrap = store.intrinsic_bootstrap().unwrap();
        let sentinel = bootstrap.undefined_or_missing_type;
        let number = bootstrap.number_type;
        canonical_anonymous_union(store, &[template, sentinel]).unwrap();
        let TypeData::IndexedAccess(data) = store.type_payload(indexed).unwrap().data() else {
            panic!("the source must retain its deferred indexed access")
        };
        let object = data.object_type;
        let key = data.index_type;
        let orphan = store.alloc_type_parameter(None).unwrap();
        for (object, key) in [
            (number, key),
            (object, number),
            (orphan, key),
            (object, orphan),
        ] {
            let forged = store
                .alloc_indexed_access_type(object, key, AccessFlags::NONE)
                .unwrap();
            assert_deferred_indexed_union_rejected(store, forged, forged, sentinel);
        }

        let duplicate = store
            .alloc_indexed_access_type(object, key, AccessFlags::NONE)
            .unwrap();
        let before = deferred_indexed_union_snapshot(store);
        assert_eq!(
            store.validate_union_constituent(indexed),
            Err(LiteralTypeCacheError::InvalidCachedUnion(indexed)),
        );
        assert_eq!(
            store.validate_union_constituent(duplicate),
            Err(LiteralTypeCacheError::InvalidCachedUnion(duplicate)),
        );
        assert_deferred_indexed_union_rejected(store, indexed, template, sentinel);
        assert_eq!(deferred_indexed_union_snapshot(store), before);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Covers real merged ownership and its cold/warm poison paths.
    fn merged_array_type_parameters_authenticate_concat_unions_and_reject_forgery() {
        let base = parse_source_file(concat!(
            "interface Array<T> { ",
            "concat(...items: (T | ConcatArray<T>)[]): T[]; ",
            "}",
        ));
        let augmentation = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface ReadonlyArray<T> {} ",
            "interface ConcatArray<T> {}",
        ));
        let base_file = FileId::new(150);
        let augmentation_file = FileId::new(151);
        let mut binder = CanonicalBinder::new();
        for (parsed, file) in [(&base, base_file), (&augmentation, augmentation_file)] {
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            binder
                .bind_source_file_with_facts(
                    &parsed.arena,
                    parsed.source_file,
                    file,
                    CanonicalSourceFileFacts::new_with_default_library(
                        EscapedName::source(format!("\"/lib-{}.d.ts\"", file.index())),
                        CanonicalSourceLanguage::TypeScript,
                        true,
                        true,
                        CanonicalModuleState::Script,
                    ),
                )
                .unwrap();
            binder
                .bind_typescript_declaration_slice(&parsed.arena, file)
                .unwrap();
        }
        let mut context = CanonicalCheckerContext::new(
            binder.finish(),
            vec![
                (base_file, &base.arena),
                (augmentation_file, &augmentation.arena),
            ],
            CanonicalCheckerOptions::default(),
        )
        .unwrap();
        let global_types = context.global_types().clone();
        let (
            array_owner,
            concat_owner,
            parameter,
            parameter_symbol,
            parameter_parent,
            declarations,
        ) = {
            let store = context.store();
            let array_record = store.type_payload(global_types.array_type).unwrap();
            let TypeData::Interface(array) = array_record.data() else {
                panic!("the merged Array must retain its generic interface target")
            };
            let [parameter] = array.reference.resolved_type_arguments.as_deref().unwrap() else {
                panic!("the merged Array must retain one canonical type parameter")
            };
            let parameter_symbol = cached_ordinary_type_parameter_owner(store, *parameter)
                .expect("the merged parameter must own its declared type");
            let parameter_record = store.symbol(parameter_symbol).unwrap();
            assert_eq!(
                parameter_record.flags(),
                SymbolFlags::TYPE_PARAMETER | SymbolFlags::TRANSIENT,
            );
            let array_owner = array_record.symbol().unwrap();
            assert_eq!(
                store.get_parent_of_symbol(parameter_symbol),
                Some(array_owner)
            );
            let declarations = parameter_record.declarations().unwrap().to_vec();
            assert_eq!(declarations.len(), 2);
            let concat_owner = store
                .symbol_table(context.globals())
                .and_then(|globals| globals.get_source("ConcatArray"))
                .and_then(|owner| store.get_merged_symbol(owner))
                .unwrap();
            (
                array_owner,
                concat_owner,
                *parameter,
                parameter_symbol,
                parameter_record.parent().unwrap(),
                declarations,
            )
        };
        let concat_target = context.get_declared_type_of_symbol(concat_owner).unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let store = context.store_mut_for_test();
        let concat = store
            .create_direct_generic_reference_type(concat_target, &[parameter])
            .unwrap();

        assert_eq!(
            store.validate_union_constituent_with_global_types(&global_types, parameter),
            Ok(()),
        );
        let union = store
            .expression_union_type_with_global_types(
                &global_types,
                &[parameter, concat],
                UnionReduction::Literal,
            )
            .unwrap();
        assert_eq!(union_types(store, union).len(), 2);
        assert!(union_types(store, union).contains(&parameter));
        assert!(union_types(store, union).contains(&concat));

        let warm = (
            store.type_len(),
            store.type_alias_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        );
        assert_eq!(
            store.expression_union_type_with_global_types(
                &global_types,
                &[concat, parameter],
                UnionReduction::Literal,
            ),
            Ok(union),
        );
        assert_eq!(
            (
                store.type_len(),
                store.type_alias_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ),
            warm,
        );

        let rejected = Err(LiteralTypeCacheError::UnsupportedUnionConstituent(
            parameter,
        ));
        assert!(store.set_symbol_declarations(parameter_symbol, Some(vec![declarations[0]]), None));
        assert_eq!(
            store.validate_union_constituent_with_global_types(&global_types, parameter),
            rejected,
        );
        assert!(store.set_symbol_declarations(parameter_symbol, Some(declarations.clone()), None));

        let foreign_declaration = store
            .symbol(concat_owner)
            .and_then(ts_binder::semantic::Symbol::members)
            .and_then(|members| store.symbol_table(members))
            .and_then(|members| members.get_source("T"))
            .and_then(|symbol| store.symbol(symbol))
            .and_then(ts_binder::semantic::Symbol::declarations)
            .and_then(|declarations| declarations.first())
            .copied()
            .unwrap();
        assert!(store.set_symbol_declarations(
            parameter_symbol,
            Some(vec![declarations[0], foreign_declaration]),
            None,
        ));
        assert_eq!(
            store.validate_union_constituent_with_global_types(&global_types, parameter),
            rejected,
        );
        assert!(store.set_symbol_declarations(parameter_symbol, Some(declarations), None));

        assert!(store.set_symbol_relationships(
            parameter_symbol,
            None,
            None,
            Some(concat_owner),
            None,
        ));
        assert_eq!(
            store.validate_union_constituent_with_global_types(&global_types, parameter),
            rejected,
        );
        assert!(store.set_symbol_relationships(
            parameter_symbol,
            None,
            None,
            Some(parameter_parent),
            None,
        ));
        assert_eq!(
            store.get_parent_of_symbol(parameter_symbol),
            Some(array_owner)
        );

        let (constraint, target, mapper, default_type, base_constraint) = {
            let TypeData::TypeParameter(data) = store.type_payload(parameter).unwrap().data()
            else {
                panic!("the merged parameter must retain its canonical type payload")
            };
            (
                data.constraint,
                data.target,
                data.mapper,
                data.resolved_default_type,
                data.constrained.resolved_base_constraint,
            )
        };
        assert!(store.set_type_parameter_resolution(
            parameter,
            Some(number),
            target,
            mapper,
            default_type,
        ));
        assert_eq!(
            store.validate_union_constituent_with_global_types(&global_types, parameter),
            rejected,
        );
        assert!(store.set_type_parameter_resolution(
            parameter,
            constraint,
            target,
            mapper,
            default_type,
        ));

        assert!(store.set_resolved_base_constraint(parameter, Some(number)));
        assert_eq!(
            store.validate_union_constituent_with_global_types(&global_types, parameter),
            rejected,
        );
        assert!(store.set_resolved_base_constraint(parameter, base_constraint));
        assert_eq!(
            store.expression_union_type_with_global_types(
                &global_types,
                &[parameter, concat],
                UnionReduction::Literal,
            ),
            Ok(union),
        );
        assert_eq!(
            (
                store.type_len(),
                store.type_alias_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ),
            warm,
        );
    }

    #[test]
    fn constructor_union_order_uses_program_file_ranks() {
        let high = parse_source_file("class Zebra {} const z = Zebra;");
        let low = parse_source_file("class Alpha {} const a = Alpha;");
        let middle = parse_source_file("class Middle {} const m = Middle;");
        let files = [
            (FileId::new(20), &high, "z", "typeof Zebra"),
            (FileId::new(3), &low, "a", "typeof Alpha"),
            (FileId::new(11), &middle, "m", "typeof Middle"),
        ];
        for order in [[0, 1, 2], [2, 1, 0]] {
            let mut binder = CanonicalBinder::new();
            for index in [1, 2, 0] {
                let (file, parsed, _, _) = files[index];
                assert!(parsed.diagnostics.is_empty());
                binder
                    .bind_source_file_with_facts(
                        &parsed.arena,
                        parsed.source_file,
                        file,
                        CanonicalSourceFileFacts::new(
                            EscapedName::source(format!("\"/project/{}.ts\"", file.index())),
                            CanonicalSourceLanguage::TypeScript,
                            false,
                            CanonicalModuleState::Script,
                        ),
                    )
                    .unwrap();
            }
            for (file, parsed, _, _) in files {
                binder
                    .bind_typescript_declaration_slice(&parsed.arena, file)
                    .unwrap();
            }
            let mut context = CanonicalCheckerContext::new(
                binder.finish(),
                order
                    .map(|index| (files[index].0, &files[index].1.arena))
                    .to_vec(),
                CanonicalCheckerOptions::default(),
            )
            .unwrap();
            assert_eq!(context.file_order(), order.map(|index| files[index].0));
            for (rank, index) in order.into_iter().enumerate() {
                assert_eq!(context.store().source_file_rank(files[index].0), Some(rank));
            }
            let mut constructors = Vec::new();
            for index in order.into_iter().rev() {
                let (file, parsed, variable, _) = files[index];
                constructors.push(
                    context
                        .get_type_at_location(variable_initializer(parsed, file, variable))
                        .unwrap(),
                );
            }
            let globals = context.global_types().clone();
            let union = context
                .store_mut_for_test()
                .expression_union_type_with_global_types(
                    &globals,
                    &constructors,
                    UnionReduction::None,
                )
                .unwrap();
            assert_eq!(
                context.type_to_string(union).unwrap(),
                order.map(|index| files[index].3).join(" | "),
            );
            constructors.reverse();
            assert_eq!(union_types(context.store(), union), constructors);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)] // Check allocation order, pairwise order, and cache replay together.
    fn constructor_union_order_is_transitive_across_object_payloads() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "class Zebra {} class Alpha {}",
        ));
        let file = FileId::new(149);
        for nonempty in [false, true] {
            let mut context = checker_context(file, &parsed);
            let classes = parsed
                .arena
                .iter()
                .filter_map(|(node, record)| {
                    (record.kind == SyntaxKind::ClassDeclaration).then_some(NodeRef::new(
                        parsed.arena.id(),
                        file,
                        node,
                    ))
                })
                .map(|node| context.file(file).unwrap().1.symbol(node).unwrap())
                .collect::<Vec<_>>();
            let [first_symbol, second_symbol] = classes.as_slice() else {
                panic!("the source must contain two class declarations")
            };
            // Source queries check the whole file, so publish each class directly.
            let second = context
                .get_nongeneric_class_members(*second_symbol)
                .unwrap()
                .shells()
                .value_type();
            let number = context.store().intrinsic_bootstrap().unwrap().number_type;
            let required = context
                .store()
                .create_tuple_element_info(ElementFlags::REQUIRED, None)
                .unwrap();
            let element_types = [number];
            let element_infos = [required];
            let element_count = usize::from(nonempty);
            let tuple = context
                .store_mut_for_test()
                .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                    &element_types[..element_count],
                    &element_infos[..element_count],
                    false,
                ))
                .unwrap();
            let first = context
                .get_nongeneric_class_members(*first_symbol)
                .unwrap()
                .shells()
                .value_type();
            assert!(
                second.get() < tuple.get() && tuple.get() < first.get(),
                "expected second < tuple < first, got {second:?}, {tuple:?}, {first:?}",
            );
            assert!(
                matches!(
                    context.store().type_payload(tuple).unwrap().data(),
                    TypeData::TypeReference(_) if nonempty
                ) || matches!(
                    context.store().type_payload(tuple).unwrap().data(),
                    TypeData::Tuple(_) if !nonempty
                )
            );
            let expected = [first, second, tuple];
            let globals = context.global_types().clone();
            let store = context.store_mut_for_test();
            for (left_rank, left) in expected.into_iter().enumerate() {
                for (right_rank, right) in expected.into_iter().enumerate() {
                    assert_eq!(
                        store.compare_union_types(left, right),
                        Ok(left_rank.cmp(&right_rank)),
                    );
                }
            }
            let union = store
                .expression_union_type_with_global_types(&globals, &expected, UnionReduction::None)
                .unwrap();
            let allocations = (
                store.type_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            );
            for indices in [
                [0, 1, 2],
                [0, 2, 1],
                [1, 0, 2],
                [1, 2, 0],
                [2, 0, 1],
                [2, 1, 0],
            ] {
                let [left, middle, right] = indices.map(|index| expected[index]);
                for inputs in [
                    vec![left, middle, right],
                    vec![left, middle, right, left, right],
                ] {
                    assert_eq!(
                        store.expression_union_type_with_global_types(
                            &globals,
                            &inputs,
                            UnionReduction::None,
                        ),
                        Ok(union),
                    );
                    assert_eq!(union_types(store, union), expected);
                    assert_eq!(
                        (
                            store.type_len(),
                            store.intrinsic_bootstrap().unwrap().union_cache_len(),
                        ),
                        allocations,
                    );
                }
            }
        }
    }

    #[test]
    fn constructor_union_order_rejects_borrowed_class_declarations() {
        let parsed = parse_source_file(
            "class Zebra {} class Alpha {} const first = Zebra; const second = Alpha;",
        );
        let file = FileId::new(150);
        let mut context = checker_context(file, &parsed);
        let first = context
            .get_type_at_location(variable_initializer(&parsed, file, "first"))
            .unwrap();
        let second = context
            .get_type_at_location(variable_initializer(&parsed, file, "second"))
            .unwrap();
        let globals = context.global_types().clone();
        let store = context.store_mut_for_test();
        let first_symbol = store.type_payload(first).unwrap().symbol().unwrap();
        let second_symbol = store.type_payload(second).unwrap().symbol().unwrap();
        let first_record = store.symbol(first_symbol).unwrap();
        let declarations = first_record.declarations().unwrap().to_vec();
        let value_declaration = first_record.value_declaration();
        let second_record = store.symbol(second_symbol).unwrap();
        let borrowed = second_record.declarations().unwrap().to_vec();
        let borrowed_value = second_record.value_declaration();
        let union = store
            .expression_union_type_with_global_types(
                &globals,
                &[first, second],
                UnionReduction::None,
            )
            .unwrap();
        let allocations = (
            store.type_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        );
        assert!(store.set_symbol_declarations(first_symbol, Some(borrowed), borrowed_value));
        assert!(!store.source_symbol_declarations_match(first_symbol));
        assert_eq!(
            store.validate_union_constituent_with_global_types(&globals, first),
            Err(LiteralTypeCacheError::InvalidCachedUnion(first)),
        );
        assert_eq!(
            store.compare_union_types(first, second),
            Err(LiteralTypeCacheError::InvalidCachedUnion(first)),
        );
        assert!(
            store
                .expression_union_type_with_global_types(
                    &globals,
                    &[first, second],
                    UnionReduction::None,
                )
                .is_err(),
        );
        assert_eq!(
            (
                store.type_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ),
            allocations,
        );
        assert!(store.set_symbol_declarations(first_symbol, Some(declarations), value_declaration));
        assert!(store.source_symbol_declarations_match(first_symbol));
        assert_eq!(
            store.expression_union_type_with_global_types(
                &globals,
                &[second, first],
                UnionReduction::None,
            ),
            Ok(union),
        );
    }

    #[test]
    fn recursive_tuple_members_keep_structural_and_member_visits_separate() {
        for children in ["[Tree2, Tree1]", "[Tree2, Tree2]", "[Array<Tree2>, Tree1]"] {
            let parsed = parse_source_file(&format!(
                "interface Array<T> {{}} interface ReadonlyArray<T> {{}} \
                 interface Tree1 {{ children: [Tree1, Tree2]; }} \
                 interface Tree2 {{ children: {children}; }}"
            ));
            assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
            let file = FileId::new(196);
            let mut context = CanonicalCheckerContext::new(
                completed_bindings(file, &parsed),
                [(file, &parsed.arena)].into_iter().collect(),
                IntrinsicBootstrapOptions {
                    strict_null_checks: true,
                    ..IntrinsicBootstrapOptions::default()
                },
            )
            .unwrap();
            context
                .check_source_file(file)
                .unwrap_or_else(|error| panic!("{children}: {error:?}"));
            let interfaces = ["Tree1", "Tree2"].map(|name| {
                let store = context.store();
                let owner = store
                    .symbol_table(store.intrinsic_bootstrap().unwrap().globals)
                    .and_then(|globals| globals.get_source(name))
                    .and_then(|owner| store.get_merged_symbol(owner))
                    .unwrap();
                context.get_declared_type_of_symbol(owner).unwrap()
            });
            let globals = context.global_types().clone();
            let targets = CanonicalArrayTargets::from_global_types(&globals);
            let store = context.store_mut_for_test();
            let tuples = interfaces.map(|interface| {
                object_members::resolved_declared_property_types(store, interface).unwrap()[0]
            });
            for root in interfaces.into_iter().chain(tuples) {
                assert_eq!(
                    store.validate_union_constituent_with_global_types(&globals, root),
                    Ok(()),
                    "{children}: {root:?}",
                );
                assert_eq!(
                    store.validate_cached_array_capability_with_array_targets(targets, root),
                    Ok(()),
                    "{children}: {root:?}",
                );
            }
            let union = store
                .expression_union_type_with_global_types(&globals, &tuples, UnionReduction::None)
                .unwrap();
            for _ in 0..2 {
                assert_eq!(
                    store.validate_cached_union_result_with_array_targets(targets, union, None),
                    Ok(()),
                    "{children}",
                );
            }
        }
    }

    #[test]
    fn tuple_validation_rejects_direct_containment_cycles() {
        let mut store = initialized(IntrinsicBootstrapOptions::default());
        let number = store.intrinsic_bootstrap().unwrap().number_type;
        let info = store
            .create_tuple_element_info(ElementFlags::REQUIRED, None)
            .unwrap();
        let seed = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&[number], &[info], false))
            .unwrap();
        let target = store.canonical_tuple_shape(seed).unwrap().unwrap().target();
        let cyclic = store.alloc_type_reference(ObjectFlags::NONE, None).unwrap();
        assert!(store.set_object_target_and_mapper(cyclic, Some(target), None));
        assert!(store.set_type_reference_resolution(cyclic, None, Some(vec![cyclic])));
        assert!(store.try_reserve_object_instantiations(target, 1));
        assert_eq!(
            store.insert_object_instantiation(target, type_list_key(&[cyclic]), cyclic),
            Some(cyclic),
        );
        assert_eq!(
            store
                .canonical_tuple_shape(cyclic)
                .unwrap()
                .unwrap()
                .element_types(),
            [cyclic],
        );
        assert_eq!(
            store.validate_union_constituent(cyclic),
            Err(LiteralTypeCacheError::InvalidCachedUnion(cyclic)),
        );
        assert_eq!(
            store.validate_cached_array_capability(cyclic),
            Err(LiteralTypeCacheError::InvalidCachedUnion(cyclic)),
        );
    }

    #[test]
    fn recursive_tuple_members_still_validate_later_array_elements() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} interface ReadonlyArray<T> {} ",
            "interface Tree { children: [Tree, Array<number>]; }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(197);
        let mut context = checker_context(file, &parsed);
        context.check_source_file(file).unwrap();
        let owner = context
            .store()
            .symbol_table(context.store().intrinsic_bootstrap().unwrap().globals)
            .and_then(|globals| globals.get_source("Tree"))
            .and_then(|owner| context.store().get_merged_symbol(owner))
            .unwrap();
        let tree = context.get_declared_type_of_symbol(owner).unwrap();
        let globals = context.global_types().clone();
        let targets = CanonicalArrayTargets::from_global_types(&globals);
        let store = context.store_mut_for_test();
        let tuple = object_members::resolved_declared_property_types(store, tree).unwrap()[0];
        let array = store
            .canonical_tuple_shape(tuple)
            .unwrap()
            .unwrap()
            .element_types()[1];
        let (number, string) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        assert!(store.set_type_reference_resolution(array, None, Some(vec![string])));
        for root in [tree, tuple] {
            for result in [
                store.validate_union_constituent_with_global_types(&globals, root),
                store.validate_cached_array_capability_with_array_targets(targets, root),
            ] {
                assert!(
                    matches!(
                        result,
                        Err(LiteralTypeCacheError::ArrayType { type_, .. }) if type_ == array
                    ),
                    "the recursive first element must not hide the invalid sibling: {result:?}",
                );
            }
        }
        assert!(store.set_type_reference_resolution(array, None, Some(vec![number])));
        for root in [tree, tuple] {
            assert_eq!(
                store.validate_union_constituent_with_global_types(&globals, root),
                Ok(()),
            );
            assert_eq!(
                store.validate_cached_array_capability_with_array_targets(targets, root),
                Ok(()),
            );
        }
    }

    #[test]
    fn tuple_literal_union_constituents_preserve_authenticated_clone_ownership() {
        let parsed = parse_source_file("interface Array<T> {} interface ReadonlyArray<T> {}");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut context = checker_context(FileId::new(148), &parsed);
        let global_types = context.global_types().clone();
        let (number, string) = {
            let bootstrap = context.store().intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.string_type)
        };
        let store = context.store_mut_for_test();
        let required = store
            .create_tuple_element_info(ElementFlags::REQUIRED, None)
            .unwrap();
        let infos = [required, required];
        let first = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[number, string],
                &infos,
                false,
            ))
            .unwrap();
        let second = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[string, number],
                &infos,
                false,
            ))
            .unwrap();
        let readonly = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(
                &[number, string],
                &infos,
                true,
            ))
            .unwrap();
        let empty = store
            .create_canonical_tuple_type(CanonicalTupleTypeRequest::new(&[], &[], false))
            .unwrap();
        let first_literal = store
            .create_array_literal_type(&global_types, first)
            .unwrap();
        let second_literal = store
            .create_array_literal_type(&global_types, second)
            .unwrap();
        let readonly_literal = store
            .create_array_literal_type(&global_types, readonly)
            .unwrap();
        let empty_literal = store
            .create_array_literal_type(&global_types, empty)
            .unwrap();

        for tuple in [
            first,
            second,
            readonly,
            empty,
            first_literal,
            second_literal,
            readonly_literal,
            empty_literal,
        ] {
            assert_eq!(
                store.validate_union_constituent_with_global_types(&global_types, tuple),
                Ok(()),
            );
            assert_eq!(
                store.validate_cached_array_capability_with_array_targets(
                    CanonicalArrayTargets::from_global_types(&global_types),
                    tuple,
                ),
                Ok(()),
            );
        }

        let union = store
            .expression_union_type_with_global_types(
                &global_types,
                &[first_literal, second_literal],
                UnionReduction::None,
            )
            .unwrap();
        let mut expected = [first_literal, second_literal];
        expected.sort_unstable();
        assert_eq!(union_types(store, union), expected.as_slice());
        let warm = (
            store.type_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        );
        assert_eq!(
            store.expression_union_type_with_global_types(
                &global_types,
                &[second_literal, first_literal],
                UnionReduction::None,
            ),
            Ok(union),
        );
        assert_eq!(
            (
                store.type_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ),
            warm,
        );

        let (flags, symbol, target, arguments) = {
            let record = store.type_payload(first_literal).unwrap();
            let TypeData::TypeReference(reference) = record.data() else {
                panic!("tuple literals retain a concrete reference clone")
            };
            (
                record.object_flags(),
                record.symbol(),
                reference.object.target,
                reference.resolved_type_arguments.clone(),
            )
        };
        let forged = store.alloc_type_reference(flags, symbol).unwrap();
        assert!(store.set_object_target_and_mapper(forged, target, None));
        assert!(store.set_type_reference_resolution(forged, None, arguments));
        let forged_state = (
            store.type_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        );
        assert_eq!(
            store.validate_union_constituent_with_global_types(&global_types, forged),
            Err(LiteralTypeCacheError::InvalidCachedUnion(forged)),
        );
        assert_eq!(
            store.validate_cached_array_capability_with_array_targets(
                CanonicalArrayTargets::from_global_types(&global_types),
                forged,
            ),
            Err(LiteralTypeCacheError::InvalidCachedUnion(forged)),
        );
        assert_eq!(
            (
                store.type_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ),
            forged_state,
        );

        assert!(store.set_type_object_flags(first_literal, flags | ObjectFlags::FROM_TYPE_NODE));
        assert_eq!(
            store.validate_union_constituent_with_global_types(&global_types, first_literal),
            Err(LiteralTypeCacheError::InvalidCachedUnion(first_literal)),
        );
        assert!(store.set_type_object_flags(first_literal, flags));
        assert_eq!(
            store.validate_union_constituent_with_global_types(&global_types, first_literal),
            Ok(()),
        );

        let array = store
            .create_canonical_array_type(&global_types, number, false)
            .unwrap();
        let (flags, symbol, target, arguments) = {
            let record = store.type_payload(array).unwrap();
            let TypeData::TypeReference(reference) = record.data() else {
                panic!("the configured array must retain a canonical type reference")
            };
            (
                record.object_flags(),
                record.symbol(),
                reference.object.target,
                reference.resolved_type_arguments.clone(),
            )
        };
        let forged_array = store.alloc_type_reference(flags, symbol).unwrap();
        assert!(store.set_object_target_and_mapper(forged_array, target, None));
        assert!(store.set_type_reference_resolution(forged_array, None, arguments));
        assert!(matches!(
            store.validate_union_constituent_with_global_types(&global_types, forged_array),
            Err(LiteralTypeCacheError::ArrayType { type_, .. }) if type_ == forged_array
        ));
    }

    #[test]
    fn unresolved_jsx_element_heritage_shells_are_authenticated_union_constituents() {
        let parsed = parse_source_file(concat!(
            "interface ReactElement<T> { value: T } ",
            "declare namespace JSX { interface Element extends ReactElement<any> {} }",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(149);
        let mut context = checker_context(file, &parsed);
        let owner = {
            let store = context.store();
            let namespace = store
                .symbol_table(context.globals())
                .and_then(|globals| globals.get_source("JSX"))
                .unwrap();
            store
                .symbol(namespace)
                .and_then(ts_binder::semantic::Symbol::exports)
                .and_then(|exports| store.symbol_table(exports))
                .and_then(|exports| exports.get_source("Element"))
                .and_then(|element| store.get_merged_symbol(element))
                .unwrap()
        };
        let element = context.get_declared_type_of_symbol(owner).unwrap();
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let store = context.store_mut_for_test();
        let TypeData::Interface(interface) = store.type_payload(element).unwrap().data() else {
            panic!("JSX.Element must retain its declared interface shell")
        };
        assert!(!interface.base_types_resolved);
        assert!(interface.resolved_base_types.is_none());
        assert!(
            store
                .direct_interface_heritage_provenance(element)
                .is_none()
        );

        assert_eq!(store.validate_union_constituent(element), Ok(()));
        let union = store.literal_union_type(&[element, number], None).unwrap();
        assert_eq!(union_types(store, union), &[number, element]);

        let warm = (
            store.type_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        );
        assert_eq!(
            store.literal_union_type(&[element, number], None),
            Ok(union)
        );
        assert_eq!(
            (
                store.type_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ),
            warm,
        );

        assert!(store.set_interface_base_resolution(element, true, None, None));
        assert_eq!(
            store.validate_union_constituent(element),
            Err(LiteralTypeCacheError::InvalidCachedUnion(element)),
        );
    }

    #[test]
    fn inherited_interface_union_constituents_require_exact_heritage_provenance() {
        let parsed = parse_source_file(concat!(
            "interface Base { inherited: number }\n",
            "interface Derived extends Base { own: string }\n",
            "declare const value: Derived;\n",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(144);
        let mut context = checker_context(file, &parsed);
        context.check_source_file(file).unwrap();
        let declaration = parsed
            .arena
            .iter()
            .find_map(|(node, record)| {
                let NodeData::InterfaceDeclaration(interface) = &record.data else {
                    return None;
                };
                let NodeData::Identifier(name) = &parsed.arena.get(interface.name)?.data else {
                    return None;
                };
                (name.text == "Derived").then_some(NodeRef::new(parsed.arena.id(), file, node))
            })
            .expect("fixture declares Derived");
        let owner = context
            .file(file)
            .unwrap()
            .1
            .symbol(declaration)
            .and_then(|owner| context.store().get_merged_symbol(owner))
            .expect("Derived has a canonical declaration symbol");
        let inherited = context
            .store()
            .declared_type_links(owner)
            .and_then(|links| links.declared_type)
            .expect("Derived has a resolved declared type");
        let number = context.store().intrinsic_bootstrap().unwrap().number_type;
        let store = context.store_mut_for_test();

        assert_eq!(store.validate_union_constituent(inherited), Ok(()));
        let union = store
            .literal_union_type(&[inherited, number], None)
            .unwrap();
        assert_eq!(union_types(store, union), &[number, inherited]);
        let warm = (
            store.type_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        );
        assert_eq!(
            store.literal_union_type(&[inherited, number], None),
            Ok(union)
        );
        assert_eq!(
            (
                store.type_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ),
            warm,
        );

        assert!(store.set_interface_base_resolution(inherited, true, None, None));
        assert_eq!(
            store.validate_union_constituent(inherited),
            Err(LiteralTypeCacheError::InvalidCachedUnion(inherited)),
        );
        let poisoned = (
            store.type_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
        );
        assert_eq!(
            store.literal_union_type(&[inherited, number], None),
            Err(LiteralTypeCacheError::InvalidCachedUnion(inherited)),
        );
        assert_eq!(
            (
                store.type_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
            ),
            poisoned,
        );
    }

    #[test]
    fn structured_expression_subtype_reduction_preserves_fresh_excess_shapes() {
        let parsed = parse_source_file(concat!(
            "const first: any = { id: 1 };",
            "const equal: any = { id: 2 };",
            "const excess: any = { id: 3, name: 'ok' };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(142);
        let mut context = checker_context(file, &parsed);
        context.check_source_file(file).unwrap();
        let first = checked_expression_type(&context, variable_initializer(&parsed, file, "first"));
        let equal = checked_expression_type(&context, variable_initializer(&parsed, file, "equal"));
        let excess =
            checked_expression_type(&context, variable_initializer(&parsed, file, "excess"));
        let store = context.store_mut_for_test();

        let reduced = store
            .expression_union_type(&[first, equal], UnionReduction::Subtype)
            .unwrap();
        assert_eq!(
            reduced, first,
            "the later structurally identical fresh shape is a redundant strict subtype"
        );
        let warm = (
            store.type_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
            store.relation_state_snapshot(),
        );
        assert_eq!(
            store
                .expression_union_type(&[equal, first], UnionReduction::Subtype)
                .unwrap(),
            reduced
        );
        assert_eq!(
            (
                store.type_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
                store.relation_state_snapshot(),
            ),
            warm
        );
        let retained = store
            .expression_union_type(&[first, excess], UnionReduction::Subtype)
            .unwrap();
        assert_eq!(union_types(store, retained), &[first, excess]);
        assert!(
            record(store, retained)
                .object_flags()
                .contains(ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL)
        );
    }

    #[test]
    fn subtype_reduction_preserves_declared_optional_properties_beside_literals() {
        let parsed = parse_source_file(concat!(
            "const literal = { ready: true };",
            "declare const optional: { ready: boolean; detail?: undefined };",
            "declare const required: { ready: boolean; detail: string };",
            "const optionalValue = optional;",
            "const requiredValue = required;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(153);
        let mut context = checker_context(file, &parsed);
        context.check_source_file(file).unwrap();
        assert!(context.diagnostics().is_empty());
        let literal =
            checked_expression_type(&context, variable_initializer(&parsed, file, "literal"));
        let optional = checked_expression_type(
            &context,
            variable_initializer(&parsed, file, "optionalValue"),
        );
        let required = checked_expression_type(
            &context,
            variable_initializer(&parsed, file, "requiredValue"),
        );
        let store = context.store_mut_for_test();
        let declared = store
            .expression_union_type(&[optional, required], UnionReduction::Literal)
            .unwrap();
        for inputs in [[literal, optional], [optional, literal]] {
            assert_eq!(
                store.expression_union_type(&inputs, UnionReduction::Subtype),
                Ok(optional),
            );
        }
        for inputs in [[declared, literal], [literal, declared]] {
            assert_eq!(
                store.expression_union_type(&inputs, UnionReduction::Subtype),
                Ok(declared),
            );
        }
        assert_eq!(union_types(store, declared), &[optional, required]);
        assert!(
            record(store, literal)
                .object_flags()
                .contains(ObjectFlags::OBJECT_LITERAL | ObjectFlags::FRESH_LITERAL)
        );
    }

    #[test]
    fn object_subtype_reduction_skips_incompatible_authenticated_unit_properties() {
        let parsed = parse_source_file(concat!(
            "interface First { kind: 'first'; value: number } ",
            "interface Second { kind: 'second'; value: number } ",
            "declare const declaredSecond: Second; ",
            "const first: First = { kind: 'first', value: 1 }; ",
            "const second: Second = { kind: 'second', value: 2 }; ",
            "const matching: First = { kind: 'first', value: 3 }; ",
            "const declared: any = declaredSecond;",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(150);
        let mut context = checker_context(file, &parsed);
        context.check_source_file(file).unwrap();

        let first = checked_expression_type(&context, variable_initializer(&parsed, file, "first"));
        let second =
            checked_expression_type(&context, variable_initializer(&parsed, file, "second"));
        let matching =
            checked_expression_type(&context, variable_initializer(&parsed, file, "matching"));
        let declared =
            checked_expression_type(&context, variable_initializer(&parsed, file, "declared"));
        let store = context.store_mut_for_test();

        let pristine_relations = store.relation_state_snapshot();
        let fresh_union = store
            .expression_union_type(&[first, second], UnionReduction::Subtype)
            .unwrap();
        let mut expected = [first, second];
        expected.sort_unstable();
        assert_eq!(union_types(store, fresh_union), expected.as_slice());
        assert_eq!(store.relation_state_snapshot(), pristine_relations);

        let mixed_union = store
            .expression_union_type(&[first, declared], UnionReduction::Subtype)
            .unwrap();
        let mut expected = [first, declared];
        expected.sort_unstable();
        assert_eq!(union_types(store, mixed_union), expected.as_slice());
        assert_eq!(store.relation_state_snapshot(), pristine_relations);

        let warm = (
            store.type_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
            store.relation_state_snapshot(),
        );
        assert_eq!(
            store.expression_union_type(&[declared, first], UnionReduction::Subtype),
            Ok(mixed_union),
        );
        assert_eq!(
            (
                store.type_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
                store.relation_state_snapshot(),
            ),
            warm,
        );

        let reduced = store
            .expression_union_type(&[first, matching, second], UnionReduction::Subtype)
            .unwrap();
        let mut expected = [first, second];
        expected.sort_unstable();
        assert_eq!(union_types(store, reduced), expected.as_slice());
        assert_eq!(
            store.relation_state_snapshot().strict_subtype.entries,
            pristine_relations.strict_subtype.entries + 1,
        );

        let property = record(store, declared)
            .data()
            .structured()
            .and_then(|structured| structured.properties.as_deref())
            .and_then(|properties| properties.first())
            .copied()
            .unwrap();
        let expected_links = store.value_symbol_links(property).unwrap().clone();
        let mut poisoned_links = expected_links.clone();
        poisoned_links.write_type = Some(store.intrinsic_bootstrap().unwrap().number_type);
        assert!(store.set_value_symbol_links(property, poisoned_links));
        let poisoned = (
            store.type_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
            store.relation_state_snapshot(),
        );
        assert_eq!(
            store.expression_union_type(&[first, declared], UnionReduction::Subtype),
            Err(LiteralTypeCacheError::InvalidCachedUnion(declared)),
        );
        assert_eq!(
            (
                store.type_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
                store.relation_state_snapshot(),
            ),
            poisoned,
        );
        assert!(store.set_value_symbol_links(property, expected_links));
        assert_eq!(
            store.expression_union_type(&[declared, first], UnionReduction::Subtype),
            Ok(mixed_union),
        );
    }

    #[test]
    fn derived_object_subtype_discriminants_preserve_nested_and_contextual_provenance() {
        let parsed = parse_source_file(concat!(
            "interface Array<T> {} ",
            "interface NestedFirst { kind: 'first'; values: number[] } ",
            "interface NestedSecond { kind: 'second'; values: number[] } ",
            "interface ContextFirst { kind: 'context-first'; first: number } ",
            "interface ContextSecond { kind: 'context-second'; second: number } ",
            "const first: NestedFirst = { kind: 'first', values: [1] }; ",
            "const second: NestedSecond = { kind: 'second', values: [2] }; ",
            "const contextFirst: ContextFirst = { kind: 'context-first', first: 1 }; ",
            "const contextSecond: ContextSecond = { kind: 'context-second', second: 2 };",
        ));
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(152);
        let mut context = checker_context(file, &parsed);
        context.check_source_file(file).unwrap();

        let first = checked_expression_type(&context, variable_initializer(&parsed, file, "first"));
        let second =
            checked_expression_type(&context, variable_initializer(&parsed, file, "second"));
        let context_first = checked_expression_type(
            &context,
            variable_initializer(&parsed, file, "contextFirst"),
        );
        let context_second = checked_expression_type(
            &context,
            variable_initializer(&parsed, file, "contextSecond"),
        );
        let global_types = context.global_types().clone();
        let store = context.store_mut_for_test();

        let widened_first = store
            .get_widened_type_with_global_types(first, &global_types)
            .unwrap();
        let widened_second = store
            .get_widened_type_with_global_types(second, &global_types)
            .unwrap();
        for widened in [widened_first, widened_second] {
            assert!(matches!(
                store.validate_derived_object_literal_with_global_types(widened, &global_types),
                DerivedObjectLiteralValidation::Valid { .. }
            ));
            let properties = record(store, widened)
                .data()
                .structured()
                .and_then(|structured| structured.properties.as_deref())
                .unwrap();
            assert_eq!(properties.len(), 2);
        }

        let pristine_relations = store.relation_state_snapshot();
        let widened_union = store
            .expression_union_type_with_global_types(
                &global_types,
                &[widened_first, widened_second],
                UnionReduction::Subtype,
            )
            .unwrap();
        let mut expected = [widened_first, widened_second];
        expected.sort_unstable();
        assert_eq!(union_types(store, widened_union), expected.as_slice());
        assert_eq!(store.relation_state_snapshot(), pristine_relations);

        let warm = (
            store.type_len(),
            store.symbol_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
            store.relation_state_snapshot(),
        );
        assert_eq!(
            store.expression_union_type_with_global_types(
                &global_types,
                &[widened_second, widened_first],
                UnionReduction::Subtype,
            ),
            Ok(widened_union),
        );
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
                store.relation_state_snapshot(),
            ),
            warm,
        );

        let context_union = store
            .expression_union_type_with_global_types(
                &global_types,
                &[context_first, context_second],
                UnionReduction::Subtype,
            )
            .unwrap();
        let contextual = store
            .get_widened_type_with_global_types(context_union, &global_types)
            .unwrap();
        let contextual_members = union_types(store, contextual).to_vec();
        assert_eq!(contextual_members.len(), 2);
        for member in &contextual_members {
            let properties = record(store, *member)
                .data()
                .structured()
                .and_then(|structured| structured.properties.as_deref())
                .unwrap();
            assert_eq!(properties.len(), 3);
            let optional = properties
                .iter()
                .copied()
                .find(|property| {
                    store
                        .symbol(*property)
                        .is_some_and(|record| record.flags().contains(SymbolFlags::OPTIONAL))
                })
                .unwrap();
            assert!(store.validate_contextual_widened_object_property(*member, optional));
        }
        let contextual_relations = store.relation_state_snapshot();
        assert_eq!(
            store.expression_union_type_with_global_types(
                &global_types,
                &contextual_members,
                UnionReduction::Subtype,
            ),
            Ok(contextual),
        );
        assert_eq!(store.relation_state_snapshot(), contextual_relations);

        let property = record(store, widened_first)
            .data()
            .structured()
            .and_then(|structured| structured.properties.as_deref())
            .and_then(|properties| {
                properties.iter().find(|property| {
                    store
                        .symbol(**property)
                        .is_some_and(|record| record.name().as_utf8() == Some("values"))
                })
            })
            .copied()
            .unwrap();
        let expected_links = store.value_symbol_links(property).unwrap().clone();
        let mut poisoned_links = expected_links.clone();
        poisoned_links.write_type = Some(store.intrinsic_bootstrap().unwrap().number_type);
        assert!(store.set_value_symbol_links(property, poisoned_links));
        let poisoned = (
            store.type_len(),
            store.symbol_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
            store.relation_state_snapshot(),
        );
        assert_eq!(
            store.expression_union_type_with_global_types(
                &global_types,
                &[widened_first, widened_second],
                UnionReduction::Subtype,
            ),
            Err(LiteralTypeCacheError::InvalidCachedUnion(widened_first)),
        );
        assert_eq!(
            (
                store.type_len(),
                store.symbol_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
                store.relation_state_snapshot(),
            ),
            poisoned,
        );
        assert!(store.set_value_symbol_links(property, expected_links));
        assert_eq!(
            store.expression_union_type_with_global_types(
                &global_types,
                &[widened_second, widened_first],
                UnionReduction::Subtype,
            ),
            Ok(widened_union),
        );
    }

    #[test]
    fn subtype_reduction_preserves_canonical_empty_objects_over_symbol_owned_empty_objects() {
        let parsed = parse_source_file("const empty: any = {}; const value: any = { item: 1 };");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(147);
        let mut context = checker_context(file, &parsed);
        context.check_source_file(file).unwrap();
        let fresh = checked_expression_type(&context, variable_initializer(&parsed, file, "empty"));
        let nonempty =
            checked_expression_type(&context, variable_initializer(&parsed, file, "value"));
        let store = context.store_mut_for_test();
        let (empty_object, unknown_empty_object, empty_type_literal) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (
                bootstrap.empty_object_type,
                bootstrap.unknown_empty_object_type,
                bootstrap.empty_type_literal_type,
            )
        };

        assert!(store.is_authenticated_symbol_owned_empty_anonymous_object(fresh));
        assert!(store.is_authenticated_symbol_owned_empty_anonymous_object(empty_type_literal));
        assert!(!store.is_authenticated_symbol_owned_empty_anonymous_object(nonempty));

        for canonical in [empty_object, unknown_empty_object] {
            for target in [fresh, empty_type_literal] {
                let mut types = Vec::new();
                store.insert_union_type(&mut types, target).unwrap();
                store.insert_union_type(&mut types, canonical).unwrap();
                store.remove_union_subtypes(&mut types, true, None).unwrap();
                assert_eq!(types, [canonical]);
            }
        }

        let warm = store.relation_state_snapshot();
        assert_eq!(
            store.expression_union_type(&[unknown_empty_object, fresh], UnionReduction::Subtype),
            Ok(unknown_empty_object),
        );
        assert_eq!(
            store.expression_union_type(&[fresh, unknown_empty_object], UnionReduction::Subtype),
            Ok(unknown_empty_object),
        );
        assert_eq!(store.relation_state_snapshot(), warm);
    }

    #[test]
    fn expression_union_reductions_preserve_literals_and_reject_poison_atomically() {
        let parsed = parse_source_file("const value: any = { id: 1 };");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let file = FileId::new(143);
        let mut context = checker_context(file, &parsed);
        context.check_source_file(file).unwrap();
        let object =
            checked_expression_type(&context, variable_initializer(&parsed, file, "value"));
        let store = context.store_mut_for_test();
        let (number, never) = {
            let bootstrap = store.intrinsic_bootstrap().unwrap();
            (bootstrap.number_type, bootstrap.never_type)
        };
        let literal = store.regular_number_literal_type(Number::new(1.0)).unwrap();

        let unreduced = store
            .expression_union_type(&[literal, number], UnionReduction::None)
            .unwrap();
        assert_eq!(union_types(store, unreduced), &[number, literal]);
        assert!(
            record(store, unreduced)
                .object_flags()
                .contains(ObjectFlags::PRIMITIVE_UNION)
        );
        assert_eq!(
            store
                .expression_union_type(&[literal, number], UnionReduction::Literal)
                .unwrap(),
            number
        );
        assert_eq!(
            store
                .expression_union_type(&[], UnionReduction::Subtype)
                .unwrap(),
            never
        );

        let structured = store
            .expression_union_type(&[number, object], UnionReduction::None)
            .unwrap();
        assert!(store.add_type_object_flags(object, ObjectFlags::NON_INFERRABLE_TYPE));
        let before = (
            store.type_len(),
            store.type_alias_len(),
            store.intrinsic_bootstrap().unwrap().union_cache_len(),
            store
                .intrinsic_bootstrap()
                .unwrap()
                .union_of_union_cache_len(),
            store.relation_state_snapshot(),
        );
        assert_eq!(
            store.expression_union_type(&[number, object], UnionReduction::None),
            Err(LiteralTypeCacheError::InvalidCachedUnion(structured))
        );
        assert_eq!(
            (
                store.type_len(),
                store.type_alias_len(),
                store.intrinsic_bootstrap().unwrap().union_cache_len(),
                store
                    .intrinsic_bootstrap()
                    .unwrap()
                    .union_of_union_cache_len(),
                store.relation_state_snapshot(),
            ),
            before
        );
    }

    #[test]
    fn prepared_union_budget_is_store_branded_and_single_use() {
        let mut first = initialized(IntrinsicBootstrapOptions::default());
        let mut second = initialized(IntrinsicBootstrapOptions::default());
        let first_types = {
            let bootstrap = first.intrinsic_bootstrap().unwrap();
            [bootstrap.string_type, bootstrap.number_type]
        };
        let second_types = {
            let bootstrap = second.intrinsic_bootstrap().unwrap();
            [bootstrap.string_type, bootstrap.number_type]
        };
        let mut prepared = first.prepare_type_query_types(&[], &[], &[], 1, 0).unwrap();

        assert_eq!(
            second.literal_union_type_prepared(&second_types, None, &mut prepared),
            Err(LiteralTypeCacheError::InvalidPreparedQuery)
        );
        assert!(
            first
                .literal_union_type_prepared(&first_types, None, &mut prepared)
                .is_ok()
        );
        assert_eq!(
            first.literal_union_type_prepared(&first_types, None, &mut prepared),
            Err(LiteralTypeCacheError::InvalidPreparedQuery)
        );
    }
}
