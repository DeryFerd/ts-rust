//! Exact relation-key, recursion-identity, flag, and cache substrate from the
//! pinned checker.
//!
//! This module ports the dependency-closed state substrate from
//! `internal/checker/checker.go` and `internal/checker/relater.go` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`. Relation-key construction is
//! deliberately capability-gated: the canonical graph can produce exact
//! simple keys and fully resolved generic keys whenever the depth-limited
//! encoding does not need a constraint query (notably `ignoreConstraints`).
//! Source-class proofs can also establish an absent constraint on an original
//! formal. Other unresolved constraints return an error before a key is exposed.

use std::{collections::HashMap, ops};

use ts_ast::NodeRef;
use ts_binder::{SemanticSymbolId, SymbolFlags};
use xxhash_rust::xxh3::Xxh3;

use super::{
    ids::TypeId,
    mapper::CanonicalTypeMapperStore,
    store::SemanticStore,
    type_records::{CacheHashKey, TypeData, TypeRecord, TypeReferenceData},
    types::{ObjectFlags, TypeFlags},
};

const RELATION_COMPARISON_BUDGET_BASE: isize = 16_000_000;
const RELATION_COMPARISON_BUDGET_DIVISOR: isize = 8;

/// The dependency-closed portion of pinned `keyBuilder` used by relation keys.
///
/// Upstream feeds each field directly to zeebo's streaming XXH3-128 hasher.
/// `xxhash-rust` implements the same unseeded algorithm, and each integer is
/// explicitly encoded in the same little-endian width before it is fed to the
/// stream. Symbol, alias, and node writers belong to other cache algorithms
/// and are intentionally not fabricated here.
struct KeyBuilder {
    hasher: Xxh3,
    #[cfg(test)]
    bytes: Vec<u8>,
}

impl Default for KeyBuilder {
    fn default() -> Self {
        Self {
            hasher: Xxh3::new(),
            #[cfg(test)]
            bytes: Vec::new(),
        }
    }
}

impl KeyBuilder {
    fn write(&mut self, bytes: &[u8]) {
        self.hasher.update(bytes);
        #[cfg(test)]
        self.bytes.extend_from_slice(bytes);
    }

    fn write_byte(&mut self, value: u8) {
        self.write(&[value]);
    }

    fn write_u32(&mut self, value: u32) {
        self.write(&value.to_le_bytes());
    }

    fn write_u64(&mut self, value: u64) {
        self.write(&value.to_le_bytes());
    }

    fn write_int(&mut self, value: usize) {
        self.write_u64(
            u64::try_from(value).expect("relation-key index must fit the pinned uint64 encoding"),
        );
    }

    fn write_type(&mut self, value: TypeId) {
        self.write_u32(value.get());
    }

    fn hash(&self) -> CacheHashKey {
        CacheHashKey::new(self.hasher.digest128())
    }

    #[cfg(test)]
    fn encoded_bytes(&self) -> &[u8] {
        &self.bytes
    }
}

/// Exact output of the dependency-closed `getRelationKey` path.
///
/// This remains semantic-module-private until constraint resolution is ported.
#[allow(dead_code)] // Consumed by the relation algorithm once that layer lands.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct BuiltRelationKey {
    key: CacheHashKey,
    constrained: bool,
    #[cfg(test)]
    encoded: Vec<u8>,
}

#[allow(dead_code)]
impl BuiltRelationKey {
    #[must_use]
    pub(super) const fn key(&self) -> CacheHashKey {
        self.key
    }

    #[must_use]
    pub(super) const fn constrained(&self) -> bool {
        self.constrained
    }

    #[cfg(test)]
    fn encoded_bytes(&self) -> &[u8] {
        &self.encoded
    }
}

/// Why an exact relation key is not available from the current canonical
/// graph. No variant carries a partial or usable cache key.
#[allow(dead_code)] // Public within `semantic` for the forthcoming relater.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum RelationKeyUnavailable {
    Type(TypeId),
    TypeReferenceArguments(TypeId),
    TypeReferenceTarget(TypeId),
    TypeParameterConstraint(TypeId),
    CyclicGenericArguments(TypeId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum GenericReferenceState {
    Generic,
    NonGeneric,
}

#[allow(dead_code)] // Constructed by the checker constraint-query capability.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeParameterConstraintState {
    Unconstrained,
    Constrained,
}

struct GenericWriteState {
    type_parameters: Vec<TypeId>,
    constrained: bool,
}

/// Typed equivalent of pinned `RecursionId.value`'s three permitted pointer
/// classes. Store-branded IDs and `NodeRef` preserve pointer identity without
/// allowing unrelated identity kinds to compare equal.
#[allow(dead_code)] // Consumed by recursion tracking once the relater lands.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum RecursionIdentity {
    Node(NodeRef),
    Symbol(SemanticSymbolId),
    Type(TypeId),
}

/// A canonical record required by `getRecursionIdentity` was unavailable.
#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum RecursionIdentityUnavailable {
    Type(TypeId),
    Symbol(SemanticSymbolId),
    TypeReferenceTarget(TypeId),
    ConditionalRoot(TypeId),
}

macro_rules! relation_flags {
    ($name:ident, $repr:ty) => {
        #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        #[repr(transparent)]
        pub struct $name($repr);

        impl $name {
            #[must_use]
            pub const fn bits(self) -> $repr {
                self.0
            }

            #[must_use]
            pub const fn contains(self, other: Self) -> bool {
                self.0 & other.0 == other.0
            }

            #[must_use]
            pub const fn intersects(self, other: Self) -> bool {
                self.0 & other.0 != 0
            }

            #[must_use]
            pub const fn is_empty(self) -> bool {
                self.0 == 0
            }
        }

        impl ops::BitAnd for $name {
            type Output = Self;

            fn bitand(self, rhs: Self) -> Self::Output {
                Self(self.0 & rhs.0)
            }
        }

        impl ops::BitAndAssign for $name {
            fn bitand_assign(&mut self, rhs: Self) {
                self.0 &= rhs.0;
            }
        }

        impl ops::BitOr for $name {
            type Output = Self;

            fn bitor(self, rhs: Self) -> Self::Output {
                Self(self.0 | rhs.0)
            }
        }

        impl ops::BitOrAssign for $name {
            fn bitor_assign(&mut self, rhs: Self) {
                self.0 |= rhs.0;
            }
        }

        impl ops::BitXor for $name {
            type Output = Self;

            fn bitxor(self, rhs: Self) -> Self::Output {
                Self(self.0 ^ rhs.0)
            }
        }

        impl ops::BitXorAssign for $name {
            fn bitxor_assign(&mut self, rhs: Self) {
                self.0 ^= rhs.0;
            }
        }

        impl ops::Not for $name {
            type Output = Self;

            fn not(self) -> Self::Output {
                Self(!self.0)
            }
        }
    };
}

relation_flags!(SignatureCheckMode, u32);

impl SignatureCheckMode {
    pub const NONE: Self = Self(0);
    pub const BIVARIANT_CALLBACK: Self = Self(1 << 0);
    pub const STRICT_CALLBACK: Self = Self(1 << 1);
    pub const IGNORE_RETURN_TYPES: Self = Self(1 << 2);
    pub const STRICT_ARITY: Self = Self(1 << 3);
    pub const STRICT_TOP_SIGNATURE: Self = Self(1 << 4);
    pub const CALLBACK: Self = Self(Self::BIVARIANT_CALLBACK.0 | Self::STRICT_CALLBACK.0);
}

relation_flags!(MinArgumentCountFlags, u32);

impl MinArgumentCountFlags {
    pub const NONE: Self = Self(0);
    pub const STRONG_ARITY_FOR_UNTYPED_JS: Self = Self(1 << 0);
    pub const VOID_IS_NON_OPTIONAL: Self = Self(1 << 1);
}

relation_flags!(IntersectionState, u32);

impl IntersectionState {
    pub const NONE: Self = Self(0);
    pub const SOURCE: Self = Self(1 << 0);
    pub const TARGET: Self = Self(1 << 1);
}

relation_flags!(RecursionFlags, u32);

impl RecursionFlags {
    pub const NONE: Self = Self(0);
    pub const SOURCE: Self = Self(1 << 0);
    pub const TARGET: Self = Self(1 << 1);
    pub const BOTH: Self = Self(Self::SOURCE.0 | Self::TARGET.0);
}

relation_flags!(ExpandingFlags, u8);

impl ExpandingFlags {
    pub const NONE: Self = Self(0);
    pub const SOURCE: Self = Self(1 << 0);
    pub const TARGET: Self = Self(1 << 1);
    pub const BOTH: Self = Self(Self::SOURCE.0 | Self::TARGET.0);
}

relation_flags!(RelationComparisonResult, u32);

impl RelationComparisonResult {
    pub const NONE: Self = Self(0);
    pub const SUCCEEDED: Self = Self(1 << 0);
    pub const FAILED: Self = Self(1 << 1);
    pub const REPORTS_UNMEASURABLE: Self = Self(1 << 3);
    pub const REPORTS_UNRELIABLE: Self = Self(1 << 4);
    pub const COMPLEXITY_OVERFLOW: Self = Self(1 << 5);
    pub const STACK_DEPTH_OVERFLOW: Self = Self(1 << 6);
    pub const REPORTS_MASK: Self = Self(Self::REPORTS_UNMEASURABLE.0 | Self::REPORTS_UNRELIABLE.0);
    pub const OVERFLOW: Self = Self(Self::COMPLEXITY_OVERFLOW.0 | Self::STACK_DEPTH_OVERFLOW.0);
}

/// Stable identity of one of `Checker`'s five distinct relation owners.
///
/// Upstream compares `*Relation` pointers. The canonical store keeps those
/// owners private and uses this closed selector without assigning them a
/// fabricated numeric representation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum RelationKind {
    Subtype,
    StrictSubtype,
    Assignable,
    Comparable,
    Identity,
}

impl RelationKind {
    pub const ALL: [Self; 5] = [
        Self::Subtype,
        Self::StrictSubtype,
        Self::Assignable,
        Self::Comparable,
        Self::Identity,
    ];

    #[must_use]
    pub const fn is_identity(self) -> bool {
        matches!(self, Self::Identity)
    }
}

fn type_reference_data(record: &TypeRecord) -> Option<&TypeReferenceData> {
    match record.data() {
        TypeData::TypeReference(data) => Some(data),
        TypeData::Interface(data) => Some(&data.reference),
        TypeData::Tuple(data) => Some(&data.interface.reference),
        _ => None,
    }
}

impl CanonicalTypeMapperStore {
    /// Uses the current source-class proof for original unconstrained formals.
    pub(super) fn relation_key_with_source_class_parameters(
        &self,
        source: TypeId,
        target: TypeId,
        intersection_state: IntersectionState,
        is_identity: bool,
        ignore_constraints: bool,
    ) -> Result<BuiltRelationKey, RelationKeyUnavailable> {
        self.relation_key_with_constraint_query(
            source,
            target,
            intersection_state,
            is_identity,
            ignore_constraints,
            |parameter| {
                super::classes::source_class_unconstrained_type_parameter(self, parameter)
                    .then_some(TypeParameterConstraintState::Unconstrained)
            },
        )
    }
}

impl<MapperPayload> SemanticStore<TypeRecord, MapperPayload> {
    /// Builds a relation key only when every upstream query needed to choose
    /// and encode that key is represented in the canonical graph.
    ///
    /// `ignore_constraints` is the exact pinned mode bit. When it is `false`,
    /// a generic key whose depth-limited encoding reaches a type parameter
    /// remains unavailable until the checker constraint query is ported.
    /// Simple relation keys never require that capability.
    #[allow(dead_code)] // Entry point for the forthcoming relation algorithm.
    pub(super) fn relation_key_if_available(
        &self,
        source: TypeId,
        target: TypeId,
        intersection_state: IntersectionState,
        is_identity: bool,
        ignore_constraints: bool,
    ) -> Result<BuiltRelationKey, RelationKeyUnavailable> {
        self.relation_key_with_constraint_query(
            source,
            target,
            intersection_state,
            is_identity,
            ignore_constraints,
            |_| None,
        )
    }

    fn relation_key_with_constraint_query(
        &self,
        mut source: TypeId,
        mut target: TypeId,
        intersection_state: IntersectionState,
        is_identity: bool,
        ignore_constraints: bool,
        mut constraint_query: impl FnMut(TypeId) -> Option<TypeParameterConstraintState>,
    ) -> Result<BuiltRelationKey, RelationKeyUnavailable> {
        if self.type_payload(source).is_none() {
            return Err(RelationKeyUnavailable::Type(source));
        }
        if self.type_payload(target).is_none() {
            return Err(RelationKeyUnavailable::Type(target));
        }
        if is_identity && source.get() > target.get() {
            (source, target) = (target, source);
        }

        let mut builder = KeyBuilder::default();
        let source_state = self.generic_reference_state(source, &mut Vec::new());
        let use_generic_encoding = match source_state {
            Ok(GenericReferenceState::NonGeneric) => false,
            Ok(GenericReferenceState::Generic) => {
                self.generic_reference_state(target, &mut Vec::new())?
                    == GenericReferenceState::Generic
            }
            Err(source_error) => {
                // The branch condition is a conjunction. A target known to be
                // non-generic makes the simple byte stream exact even while
                // source arguments are unresolved; every other case needs the
                // missing source query.
                match self.generic_reference_state(target, &mut Vec::new()) {
                    Ok(GenericReferenceState::NonGeneric) => false,
                    Ok(GenericReferenceState::Generic) | Err(_) => return Err(source_error),
                }
            }
        };

        let constrained = if use_generic_encoding {
            builder.write_byte(b'g');
            self.write_generic_type_references(
                &mut builder,
                source,
                target,
                ignore_constraints,
                &mut constraint_query,
            )?
        } else {
            builder.write_byte(b's');
            builder.write_type(source);
            builder.write_type(target);
            false
        };
        builder.write_u32(intersection_state.bits());
        Ok(BuiltRelationKey {
            key: builder.hash(),
            constrained,
            #[cfg(test)]
            encoded: builder.encoded_bytes().to_vec(),
        })
    }

    fn generic_reference_state(
        &self,
        type_id: TypeId,
        active: &mut Vec<TypeId>,
    ) -> Result<GenericReferenceState, RelationKeyUnavailable> {
        let record = self
            .type_payload(type_id)
            .ok_or(RelationKeyUnavailable::Type(type_id))?;
        if !record.object_flags().intersects(ObjectFlags::REFERENCE) {
            return Ok(GenericReferenceState::NonGeneric);
        }
        let reference = type_reference_data(record).ok_or(RelationKeyUnavailable::Type(type_id))?;
        if reference.node.is_some() {
            return Ok(GenericReferenceState::NonGeneric);
        }
        let arguments = reference
            .resolved_type_arguments
            .as_deref()
            .ok_or(RelationKeyUnavailable::TypeReferenceArguments(type_id))?;
        if active.contains(&type_id) {
            return Err(RelationKeyUnavailable::CyclicGenericArguments(type_id));
        }

        active.push(type_id);
        let result = (|| {
            for argument in arguments {
                let argument_record = self
                    .type_payload(*argument)
                    .ok_or(RelationKeyUnavailable::Type(*argument))?;
                if argument_record
                    .flags()
                    .intersects(TypeFlags::TYPE_PARAMETER)
                    || self.generic_reference_state(*argument, active)?
                        == GenericReferenceState::Generic
                {
                    return Ok(GenericReferenceState::Generic);
                }
            }
            Ok(GenericReferenceState::NonGeneric)
        })();
        active.pop();
        result
    }

    fn write_generic_type_references(
        &self,
        builder: &mut KeyBuilder,
        source: TypeId,
        target: TypeId,
        ignore_constraints: bool,
        constraint_query: &mut impl FnMut(TypeId) -> Option<TypeParameterConstraintState>,
    ) -> Result<bool, RelationKeyUnavailable> {
        let mut state = GenericWriteState {
            type_parameters: Vec::with_capacity(8),
            constrained: false,
        };
        self.write_generic_type_reference(
            builder,
            source,
            0,
            ignore_constraints,
            constraint_query,
            &mut state,
        )?;
        builder.write_byte(b',');
        self.write_generic_type_reference(
            builder,
            target,
            0,
            ignore_constraints,
            constraint_query,
            &mut state,
        )?;
        Ok(state.constrained)
    }

    fn write_generic_type_reference(
        &self,
        builder: &mut KeyBuilder,
        reference_id: TypeId,
        depth: usize,
        ignore_constraints: bool,
        constraint_query: &mut impl FnMut(TypeId) -> Option<TypeParameterConstraintState>,
        state: &mut GenericWriteState,
    ) -> Result<(), RelationKeyUnavailable> {
        let record = self
            .type_payload(reference_id)
            .ok_or(RelationKeyUnavailable::Type(reference_id))?;
        let reference =
            type_reference_data(record).ok_or(RelationKeyUnavailable::Type(reference_id))?;
        let target = reference
            .object
            .target
            .ok_or(RelationKeyUnavailable::TypeReferenceTarget(reference_id))?;
        let arguments = reference
            .resolved_type_arguments
            .as_deref()
            .ok_or(RelationKeyUnavailable::TypeReferenceArguments(reference_id))?;
        builder.write_type(target);

        for argument in arguments {
            let argument_record = self
                .type_payload(*argument)
                .ok_or(RelationKeyUnavailable::Type(*argument))?;
            if argument_record
                .flags()
                .intersects(TypeFlags::TYPE_PARAMETER)
            {
                let unconstrained = if ignore_constraints {
                    true
                } else {
                    match constraint_query(*argument)
                        .ok_or(RelationKeyUnavailable::TypeParameterConstraint(*argument))?
                    {
                        TypeParameterConstraintState::Unconstrained => true,
                        TypeParameterConstraintState::Constrained => {
                            state.constrained = true;
                            false
                        }
                    }
                };
                if unconstrained {
                    let index = state
                        .type_parameters
                        .iter()
                        .position(|candidate| candidate == argument)
                        .unwrap_or_else(|| {
                            let index = state.type_parameters.len();
                            state.type_parameters.push(*argument);
                            index
                        });
                    builder.write_byte(b'=');
                    builder.write_int(index);
                    continue;
                }
            } else if depth < 4
                && self.generic_reference_state(*argument, &mut Vec::new())?
                    == GenericReferenceState::Generic
            {
                builder.write_byte(b'<');
                self.write_generic_type_reference(
                    builder,
                    *argument,
                    depth + 1,
                    ignore_constraints,
                    constraint_query,
                    state,
                )?;
                builder.write_byte(b'>');
                continue;
            }
            builder.write_byte(b'-');
            builder.write_type(*argument);
        }
        Ok(())
    }

    /// Exact, typed extraction of pinned `getRecursionIdentity` before mapped
    /// target unwrapping and intersection matching.
    #[allow(dead_code)] // Entry point for the forthcoming recursion tracker.
    pub(super) fn recursion_identity_if_available(
        &self,
        type_id: TypeId,
    ) -> Result<RecursionIdentity, RecursionIdentityUnavailable> {
        let record = self
            .type_payload(type_id)
            .ok_or(RecursionIdentityUnavailable::Type(type_id))?;

        if record.flags().intersects(TypeFlags::OBJECT)
            && !record
                .object_flags()
                .intersects(ObjectFlags::OBJECT_LITERAL | ObjectFlags::ARRAY_LITERAL)
        {
            if record.object_flags().intersects(ObjectFlags::REFERENCE) {
                let reference = type_reference_data(record)
                    .ok_or(RecursionIdentityUnavailable::Type(type_id))?;
                if let Some(node) = reference.node {
                    return Ok(RecursionIdentity::Node(node));
                }
            }

            if let Some(symbol_id) = record.symbol() {
                let symbol = self
                    .symbol(symbol_id)
                    .ok_or(RecursionIdentityUnavailable::Symbol(symbol_id))?;
                let is_class_static_side = record.object_flags().intersects(ObjectFlags::ANONYMOUS)
                    && symbol.flags().intersects(SymbolFlags::CLASS);
                if !is_class_static_side
                    && !record
                        .object_flags()
                        .intersects(ObjectFlags::FROM_TYPE_NODE)
                {
                    return Ok(RecursionIdentity::Symbol(symbol_id));
                }
            }

            if record.object_flags().intersects(ObjectFlags::REFERENCE)
                && !record
                    .object_flags()
                    .intersects(ObjectFlags::FROM_TYPE_NODE)
            {
                let reference = type_reference_data(record)
                    .ok_or(RecursionIdentityUnavailable::Type(type_id))?;
                let target = reference
                    .object
                    .target
                    .ok_or(RecursionIdentityUnavailable::TypeReferenceTarget(type_id))?;
                let target_record = self
                    .type_payload(target)
                    .ok_or(RecursionIdentityUnavailable::Type(target))?;
                if target_record.object_flags().intersects(ObjectFlags::TUPLE) {
                    return Ok(RecursionIdentity::Type(target));
                }
            }
        }

        if record.flags().intersects(TypeFlags::TYPE_PARAMETER)
            && let Some(symbol_id) = record.symbol()
        {
            if self.symbol(symbol_id).is_none() {
                return Err(RecursionIdentityUnavailable::Symbol(symbol_id));
            }
            return Ok(RecursionIdentity::Symbol(symbol_id));
        }

        if record.flags().intersects(TypeFlags::INDEXED_ACCESS) {
            let mut leftmost = type_id;
            loop {
                let leftmost_record = self
                    .type_payload(leftmost)
                    .ok_or(RecursionIdentityUnavailable::Type(leftmost))?;
                let TypeData::IndexedAccess(indexed) = leftmost_record.data() else {
                    break;
                };
                leftmost = indexed.object_type;
            }
            return Ok(RecursionIdentity::Type(leftmost));
        }

        if record.flags().intersects(TypeFlags::CONDITIONAL) {
            let TypeData::Conditional(conditional) = record.data() else {
                return Err(RecursionIdentityUnavailable::Type(type_id));
            };
            let root = self
                .conditional_root(conditional.root)
                .ok_or(RecursionIdentityUnavailable::ConditionalRoot(type_id))?;
            return Ok(RecursionIdentity::Node(root.node()));
        }

        Ok(RecursionIdentity::Type(type_id))
    }
}

/// Observable nil/allocation and entry-count state of one relation cache.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RelationCacheSnapshot {
    pub allocated: bool,
    pub entries: usize,
}

impl RelationCacheSnapshot {
    pub(super) const fn is_pristine(self) -> bool {
        !self.allocated && self.entries == 0
    }
}

/// State of all five relation owners plus the eagerly created enum cache.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct RelationStateSnapshot {
    pub subtype: RelationCacheSnapshot,
    pub strict_subtype: RelationCacheSnapshot,
    pub assignable: RelationCacheSnapshot,
    pub comparable: RelationCacheSnapshot,
    pub identity: RelationCacheSnapshot,
    pub enum_relation_entries: usize,
}

impl RelationStateSnapshot {
    pub(super) const fn is_pristine(self) -> bool {
        self.subtype.is_pristine()
            && self.strict_subtype.is_pristine()
            && self.assignable.is_pristine()
            && self.comparable.is_pristine()
            && self.identity.is_pristine()
            && self.enum_relation_entries == 0
    }
}

/// Exact `Relation.results` state. `None` is a nil Go map; `Some({})` is an
/// allocated map, although the pinned `set` operation normally inserts the
/// first entry as it allocates.
#[derive(Debug, Default)]
struct Relation {
    results: Option<HashMap<CacheHashKey, RelationComparisonResult>>,
}

impl Relation {
    fn get(&self, key: CacheHashKey) -> RelationComparisonResult {
        self.results
            .as_ref()
            .and_then(|results| results.get(&key))
            .copied()
            .unwrap_or_default()
    }

    fn set(&mut self, key: CacheHashKey, result: RelationComparisonResult) {
        self.results
            .get_or_insert_with(HashMap::new)
            .insert(key, result);
    }

    fn size(&self) -> usize {
        self.results.as_ref().map_or(0, HashMap::len)
    }

    fn snapshot(&self) -> RelationCacheSnapshot {
        RelationCacheSnapshot {
            allocated: self.results.is_some(),
            entries: self.size(),
        }
    }

    fn comparison_budget(&self) -> isize {
        comparison_budget_for_size(self.size())
    }
}

fn comparison_budget_for_size(size: usize) -> isize {
    let size =
        isize::try_from(size).expect("relation cache size must fit the platform pointer width");
    (RELATION_COMPARISON_BUDGET_BASE - size) / RELATION_COMPARISON_BUDGET_DIVISOR
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct EnumRelationKey {
    source_id: u64,
    target_id: u64,
}

/// Private ownership of the five pointer-distinct relations and enum cache.
#[derive(Debug, Default)]
pub(super) struct RelationCaches {
    subtype: Relation,
    strict_subtype: Relation,
    assignable: Relation,
    comparable: Relation,
    identity: Relation,
    enum_relation: HashMap<EnumRelationKey, RelationComparisonResult>,
}

impl RelationCaches {
    fn relation(&self, kind: RelationKind) -> &Relation {
        match kind {
            RelationKind::Subtype => &self.subtype,
            RelationKind::StrictSubtype => &self.strict_subtype,
            RelationKind::Assignable => &self.assignable,
            RelationKind::Comparable => &self.comparable,
            RelationKind::Identity => &self.identity,
        }
    }

    fn relation_mut(&mut self, kind: RelationKind) -> &mut Relation {
        match kind {
            RelationKind::Subtype => &mut self.subtype,
            RelationKind::StrictSubtype => &mut self.strict_subtype,
            RelationKind::Assignable => &mut self.assignable,
            RelationKind::Comparable => &mut self.comparable,
            RelationKind::Identity => &mut self.identity,
        }
    }

    pub(super) fn get(&self, kind: RelationKind, key: CacheHashKey) -> RelationComparisonResult {
        self.relation(kind).get(key)
    }

    pub(super) fn set(
        &mut self,
        kind: RelationKind,
        key: CacheHashKey,
        result: RelationComparisonResult,
    ) {
        self.relation_mut(kind).set(key, result);
    }

    pub(super) fn size(&self, kind: RelationKind) -> usize {
        self.relation(kind).size()
    }

    pub(super) fn is_allocated(&self, kind: RelationKind) -> bool {
        self.relation(kind).results.is_some()
    }

    pub(super) fn comparison_budget(&self, kind: RelationKind) -> isize {
        self.relation(kind).comparison_budget()
    }

    pub(super) fn enum_get(&self, source_id: u64, target_id: u64) -> RelationComparisonResult {
        self.enum_relation
            .get(&EnumRelationKey {
                source_id,
                target_id,
            })
            .copied()
            .unwrap_or_default()
    }

    pub(super) fn enum_set(
        &mut self,
        source_id: u64,
        target_id: u64,
        result: RelationComparisonResult,
    ) {
        self.enum_relation.insert(
            EnumRelationKey {
                source_id,
                target_id,
            },
            result,
        );
    }

    pub(super) fn enum_size(&self) -> usize {
        self.enum_relation.len()
    }

    pub(super) fn snapshot(&self) -> RelationStateSnapshot {
        RelationStateSnapshot {
            subtype: self.subtype.snapshot(),
            strict_subtype: self.strict_subtype.snapshot(),
            assignable: self.assignable.snapshot(),
            comparable: self.comparable.snapshot(),
            identity: self.identity.snapshot(),
            enum_relation_entries: self.enum_relation.len(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, mem::size_of};

    use ts_ast::{FileId, NodeRef, SyntaxKind};
    use ts_binder::{EscapedName, SemanticSymbolId, SymbolData, SymbolFlags};
    use ts_parser::parse_source_file;

    use super::{
        ExpandingFlags, IntersectionState, KeyBuilder, MinArgumentCountFlags, RecursionFlags,
        RecursionIdentity, RecursionIdentityUnavailable, Relation, RelationCacheSnapshot,
        RelationCaches, RelationComparisonResult, RelationKeyUnavailable, RelationKind,
        RelationStateSnapshot, SignatureCheckMode, TypeParameterConstraintState,
        comparison_budget_for_size,
    };
    use crate::semantic::{
        AstScope, CacheHashKey, CanonicalSemanticStore, TypeId,
        types::{AccessFlags, ObjectFlags, TypeFlags},
    };

    type TestStore = CanonicalSemanticStore<()>;

    struct TestFixture {
        store: TestStore,
        conditional_node: NodeRef,
        reference_node: NodeRef,
    }

    fn test_fixture() -> TestFixture {
        let parsed = parse_source_file(
            "type Result<T> = T extends string ? T : never;\n\
             type Reference = Array<string>;",
        );
        let scope = AstScope::new(FileId::new(0), &parsed.arena);
        let node_of_kind = |kind| {
            let (node, _) = parsed
                .arena
                .iter()
                .find(|(_, node)| node.kind == kind)
                .unwrap_or_else(|| panic!("fixture is missing {kind:?}"));
            scope.node_ref(node).unwrap()
        };
        let conditional_node = node_of_kind(SyntaxKind::ConditionalType);
        let reference_node = node_of_kind(SyntaxKind::TypeReference);
        let mut store = TestStore::new();
        assert!(store.register_ast_scope(scope));
        TestFixture {
            store,
            conditional_node,
            reference_node,
        }
    }

    fn alloc_symbol(store: &mut TestStore, flags: SymbolFlags, name: &str) -> SemanticSymbolId {
        store
            .alloc_symbol(SymbolData::new(flags, EscapedName::source(name)))
            .unwrap()
    }

    fn alloc_resolved_reference(
        store: &mut TestStore,
        target: TypeId,
        arguments: Vec<TypeId>,
    ) -> TypeId {
        let reference = store.alloc_type_reference(ObjectFlags::NONE, None).unwrap();
        assert!(store.set_object_target_and_mapper(reference, Some(target), None));
        assert!(store.set_type_reference_resolution(reference, None, Some(arguments)));
        reference
    }

    fn push_u32(bytes: &mut Vec<u8>, value: u32) {
        bytes.extend_from_slice(&value.to_le_bytes());
    }

    fn push_u64(bytes: &mut Vec<u8>, value: u64) {
        bytes.extend_from_slice(&value.to_le_bytes());
    }

    #[test]
    fn key_builder_matches_pinned_zeebo_xxh3_vectors_and_integer_encoding() {
        // `github.com/zeebo/xxh3@v1.1.0/compat_test.go::testVecs128`.
        // Vector N hashes bytes 1 through N, and Uint128 is Hi<<64|Lo.
        let vectors = [
            (0, 0x99aa_06d3_0147_98d8_6001_c324_468d_497f_u128),
            (1, 0x5102_5a44_9183_5505_e12e_f9d2_eb86_ceeb_u128),
            (3, 0xac77_eb88_cbc4_b8d4_ebce_9b76_32ae_733b_u128),
            (4, 0x49a0_4899_597a_3567_5376_53a0_d995_5b86_u128),
            (8, 0x2ab4_63fd_db09_a0b8_3e86_75c5_7268_fb02_u128),
            (16, 0x6d84_a882_f641_1b41_eada_8231_04bd_7174_u128),
        ];
        for (length, expected) in vectors {
            let mut builder = KeyBuilder::default();
            for byte in 1..=length {
                builder.write_byte(u8::try_from(byte).unwrap());
            }
            assert_eq!(builder.hash(), CacheHashKey::new(expected));
        }

        let mut builder = KeyBuilder::default();
        builder.write_byte(0xa5);
        builder.write_u32(0x1234_5678);
        builder.write_u64(0x0123_4567_89ab_cdef);
        builder.write_int(0x0102_0304);
        assert_eq!(
            builder.encoded_bytes(),
            &[
                0xa5, 0x78, 0x56, 0x34, 0x12, 0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01, 0x04,
                0x03, 0x02, 0x01, 0x00, 0x00, 0x00, 0x00,
            ]
        );
    }

    #[test]
    fn simple_relation_keys_preserve_direction_identity_symmetry_and_state_bytes() {
        let mut store = TestStore::new();
        let source = store
            .alloc_intrinsic_type(TypeFlags::STRING, "string")
            .unwrap();
        let target = store
            .alloc_intrinsic_type(TypeFlags::NUMBER, "number")
            .unwrap();
        assert_eq!((source.get(), target.get()), (1, 2));

        let directed = store
            .relation_key_if_available(source, target, IntersectionState::NONE, false, false)
            .unwrap();
        assert!(!directed.constrained());
        assert_eq!(
            directed.encoded_bytes(),
            &[b's', 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
        );

        let reverse = store
            .relation_key_if_available(target, source, IntersectionState::NONE, false, false)
            .unwrap();
        assert_ne!(directed.key(), reverse.key());
        assert_eq!(
            reverse.encoded_bytes(),
            &[b's', 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
        );

        let identity_forward = store
            .relation_key_if_available(source, target, IntersectionState::NONE, true, false)
            .unwrap();
        let identity_reverse = store
            .relation_key_if_available(target, source, IntersectionState::NONE, true, false)
            .unwrap();
        assert_eq!(identity_forward, identity_reverse);
        assert_eq!(identity_forward, directed);

        let intersection = store
            .relation_key_if_available(
                source,
                target,
                IntersectionState::SOURCE | IntersectionState::TARGET,
                false,
                false,
            )
            .unwrap();
        assert_eq!(
            intersection.encoded_bytes(),
            &[b's', 1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0]
        );
        assert_ne!(directed.key(), intersection.key());

        assert_eq!(
            directed.key(),
            CacheHashKey::new(0x745d_0323_1907_e2c6_2035_ebb4_cf37_8831)
        );
        assert_eq!(
            reverse.key(),
            CacheHashKey::new(0x73f9_af1d_3798_3919_3ab8_e5bb_0075_70c3)
        );
        assert_eq!(
            intersection.key(),
            CacheHashKey::new(0xa160_f778_2b60_2e54_d1fe_9e57_969b_b709)
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One byte-stream matrix shares parameter identities.
    fn generic_relation_encoding_reuses_parameter_indices_and_gates_constraints() {
        let mut store = TestStore::new();
        let source_target = store
            .alloc_interface_type(ObjectFlags::INTERFACE, None)
            .unwrap();
        let target_target = store
            .alloc_interface_type(ObjectFlags::INTERFACE, None)
            .unwrap();
        let concrete = store
            .alloc_intrinsic_type(TypeFlags::STRING, "string")
            .unwrap();
        let source_parameter = store.alloc_type_parameter(None).unwrap();
        let target_parameter = store.alloc_type_parameter(None).unwrap();
        let source = alloc_resolved_reference(
            &mut store,
            source_target,
            vec![source_parameter, source_parameter, concrete],
        );
        let target = alloc_resolved_reference(
            &mut store,
            target_target,
            vec![target_parameter, source_parameter],
        );
        assert_eq!(
            (
                source_target.get(),
                target_target.get(),
                concrete.get(),
                source_parameter.get(),
                target_parameter.get(),
                source.get(),
                target.get(),
            ),
            (1, 2, 3, 4, 5, 6, 7)
        );

        let ignored = store
            .relation_key_if_available(source, target, IntersectionState::NONE, false, true)
            .unwrap();
        let mut ignored_bytes = vec![b'g'];
        push_u32(&mut ignored_bytes, 1);
        ignored_bytes.push(b'=');
        push_u64(&mut ignored_bytes, 0);
        ignored_bytes.push(b'=');
        push_u64(&mut ignored_bytes, 0);
        ignored_bytes.push(b'-');
        push_u32(&mut ignored_bytes, 3);
        ignored_bytes.push(b',');
        push_u32(&mut ignored_bytes, 2);
        ignored_bytes.push(b'=');
        push_u64(&mut ignored_bytes, 1);
        ignored_bytes.push(b'=');
        push_u64(&mut ignored_bytes, 0);
        push_u32(&mut ignored_bytes, 0);
        assert_eq!(ignored.encoded_bytes(), ignored_bytes);
        assert!(!ignored.constrained());

        assert_eq!(
            store.relation_key_if_available(source, target, IntersectionState::NONE, false, false,),
            Err(RelationKeyUnavailable::TypeParameterConstraint(
                source_parameter
            ))
        );

        let constrained = store
            .relation_key_with_constraint_query(
                source,
                target,
                IntersectionState::NONE,
                false,
                false,
                |parameter| {
                    Some(if parameter == target_parameter {
                        TypeParameterConstraintState::Constrained
                    } else {
                        TypeParameterConstraintState::Unconstrained
                    })
                },
            )
            .unwrap();
        let mut constrained_bytes = vec![b'g'];
        push_u32(&mut constrained_bytes, 1);
        constrained_bytes.push(b'=');
        push_u64(&mut constrained_bytes, 0);
        constrained_bytes.push(b'=');
        push_u64(&mut constrained_bytes, 0);
        constrained_bytes.push(b'-');
        push_u32(&mut constrained_bytes, 3);
        constrained_bytes.push(b',');
        push_u32(&mut constrained_bytes, 2);
        constrained_bytes.push(b'-');
        push_u32(&mut constrained_bytes, 5);
        constrained_bytes.push(b'=');
        push_u64(&mut constrained_bytes, 0);
        push_u32(&mut constrained_bytes, 0);
        assert_eq!(constrained.encoded_bytes(), constrained_bytes);
        assert!(constrained.constrained());
        assert_ne!(ignored.key(), constrained.key());

        let identity_reverse = store
            .relation_key_if_available(target, source, IntersectionState::NONE, true, true)
            .unwrap();
        let identity_forward = store
            .relation_key_if_available(source, target, IntersectionState::NONE, true, true)
            .unwrap();
        assert_eq!(identity_reverse, identity_forward);

        assert_eq!(
            ignored.key(),
            CacheHashKey::new(0x2f51_ab14_94cb_386e_c32f_70d5_73f0_fc65)
        );
        assert_eq!(
            constrained.key(),
            CacheHashKey::new(0x704c_3e93_0367_6d2a_ecd8_67e4_dd5e_5bd9)
        );
    }

    #[test]
    fn generic_relation_key_fails_closed_only_when_missing_data_can_change_the_stream() {
        let mut store = TestStore::new();
        let interface = store
            .alloc_interface_type(ObjectFlags::INTERFACE, None)
            .unwrap();
        let concrete = store
            .alloc_intrinsic_type(TypeFlags::STRING, "string")
            .unwrap();
        let parameter = store.alloc_type_parameter(None).unwrap();
        let generic = alloc_resolved_reference(&mut store, interface, vec![parameter]);

        let unresolved = store.alloc_type_reference(ObjectFlags::NONE, None).unwrap();
        assert!(store.set_object_target_and_mapper(unresolved, Some(interface), None));

        // A definitely non-generic target makes the conjunction false, so the
        // simple stream is exact without resolving the source arguments.
        let simple = store
            .relation_key_if_available(unresolved, concrete, IntersectionState::NONE, false, false)
            .unwrap();
        let mut expected = vec![b's'];
        push_u32(&mut expected, unresolved.get());
        push_u32(&mut expected, concrete.get());
        push_u32(&mut expected, 0);
        assert_eq!(simple.encoded_bytes(), expected);

        assert_eq!(
            store.relation_key_if_available(
                unresolved,
                generic,
                IntersectionState::NONE,
                false,
                true,
            ),
            Err(RelationKeyUnavailable::TypeReferenceArguments(unresolved))
        );

        let missing_target = store.alloc_type_reference(ObjectFlags::NONE, None).unwrap();
        assert!(store.set_type_reference_resolution(missing_target, None, Some(vec![parameter])));
        assert_eq!(
            store.relation_key_if_available(
                missing_target,
                generic,
                IntersectionState::NONE,
                false,
                true,
            ),
            Err(RelationKeyUnavailable::TypeReferenceTarget(missing_target))
        );

        let cyclic = store.alloc_type_reference(ObjectFlags::NONE, None).unwrap();
        assert!(store.set_object_target_and_mapper(cyclic, Some(interface), None));
        assert!(store.set_type_reference_resolution(cyclic, None, Some(vec![cyclic])));
        assert_eq!(
            store.relation_key_if_available(cyclic, generic, IntersectionState::NONE, false, true,),
            Err(RelationKeyUnavailable::CyclicGenericArguments(cyclic))
        );

        let foreign = TestStore::new()
            .alloc_intrinsic_type(TypeFlags::STRING, "foreign")
            .unwrap();
        assert_eq!(
            store.relation_key_if_available(
                foreign,
                concrete,
                IntersectionState::NONE,
                false,
                false,
            ),
            Err(RelationKeyUnavailable::Type(foreign))
        );
    }

    #[test]
    fn generic_relation_encoding_stops_nested_expansion_at_depth_four() {
        let mut store = TestStore::new();
        let target = store
            .alloc_interface_type(ObjectFlags::INTERFACE, None)
            .unwrap();
        let parameter = store.alloc_type_parameter(None).unwrap();
        let depth_five = alloc_resolved_reference(&mut store, target, vec![parameter]);
        let depth_four = alloc_resolved_reference(&mut store, target, vec![depth_five]);
        let depth_three = alloc_resolved_reference(&mut store, target, vec![depth_four]);
        let depth_two = alloc_resolved_reference(&mut store, target, vec![depth_three]);
        let depth_one = alloc_resolved_reference(&mut store, target, vec![depth_two]);
        let outer = alloc_resolved_reference(&mut store, target, vec![depth_one]);
        assert_eq!(
            (
                target.get(),
                parameter.get(),
                depth_five.get(),
                depth_four.get(),
                depth_three.get(),
                depth_two.get(),
                depth_one.get(),
                outer.get(),
            ),
            (1, 2, 3, 4, 5, 6, 7, 8)
        );

        let key = store
            .relation_key_if_available(outer, outer, IntersectionState::TARGET, false, true)
            .unwrap();
        let mut one_side = Vec::new();
        push_u32(&mut one_side, target.get());
        for _ in 0..4 {
            one_side.push(b'<');
            push_u32(&mut one_side, target.get());
        }
        one_side.push(b'-');
        push_u32(&mut one_side, depth_five.get());
        one_side.extend_from_slice(b">>>>");

        let mut expected = vec![b'g'];
        expected.extend_from_slice(&one_side);
        expected.push(b',');
        expected.extend_from_slice(&one_side);
        push_u32(&mut expected, IntersectionState::TARGET.bits());
        assert_eq!(key.encoded_bytes(), expected);
        assert!(!key.encoded_bytes().contains(&b'='));
        assert_eq!(
            key.key(),
            CacheHashKey::new(0x275a_444c_0c4b_feb6_b80a_1b45_a3b4_eeba)
        );

        // The only type parameter is below the cutoff and therefore never
        // reaches getConstraintOfTypeParameter in the pinned writer.
        let without_ignored_constraints = store
            .relation_key_if_available(outer, outer, IntersectionState::TARGET, false, false)
            .unwrap();
        assert_eq!(without_ignored_constraints, key);
    }

    #[test]
    #[allow(clippy::too_many_lines)] // One branch-precedence matrix mirrors upstream order.
    fn recursion_identity_preserves_upstream_branch_order_and_typed_identity() {
        let mut fixture = test_fixture();
        let store = &mut fixture.store;
        let base = store
            .alloc_intrinsic_type(TypeFlags::STRING, "string")
            .unwrap();
        assert_eq!(
            store.recursion_identity_if_available(base),
            Ok(RecursionIdentity::Type(base))
        );

        let object_symbol = alloc_symbol(store, SymbolFlags::TYPE_LITERAL, "ObjectOrigin");
        let class_symbol = alloc_symbol(store, SymbolFlags::CLASS, "ClassOrigin");
        let parameter_symbol = alloc_symbol(store, SymbolFlags::TYPE_PARAMETER, "T");

        let ordinary_object = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(object_symbol))
            .unwrap();
        assert_eq!(
            store.recursion_identity_if_available(ordinary_object),
            Ok(RecursionIdentity::Symbol(object_symbol))
        );

        let object_literal = store
            .alloc_plain_object_type(
                ObjectFlags::ANONYMOUS | ObjectFlags::OBJECT_LITERAL,
                Some(object_symbol),
            )
            .unwrap();
        let array_literal = store
            .alloc_plain_object_type(
                ObjectFlags::ANONYMOUS | ObjectFlags::ARRAY_LITERAL,
                Some(object_symbol),
            )
            .unwrap();
        assert_eq!(
            store.recursion_identity_if_available(object_literal),
            Ok(RecursionIdentity::Type(object_literal))
        );
        assert_eq!(
            store.recursion_identity_if_available(array_literal),
            Ok(RecursionIdentity::Type(array_literal))
        );

        let class_static_side = store
            .alloc_plain_object_type(ObjectFlags::ANONYMOUS, Some(class_symbol))
            .unwrap();
        assert_eq!(
            store.recursion_identity_if_available(class_static_side),
            Ok(RecursionIdentity::Type(class_static_side))
        );

        let from_type_node = store
            .alloc_plain_object_type(
                ObjectFlags::ANONYMOUS | ObjectFlags::FROM_TYPE_NODE,
                Some(object_symbol),
            )
            .unwrap();
        assert_eq!(
            store.recursion_identity_if_available(from_type_node),
            Ok(RecursionIdentity::Type(from_type_node))
        );

        let deferred_reference = store
            .alloc_type_reference(ObjectFlags::NONE, Some(object_symbol))
            .unwrap();
        assert!(store.set_type_reference_resolution(
            deferred_reference,
            Some(fixture.reference_node),
            None
        ));
        assert_eq!(
            store.recursion_identity_if_available(deferred_reference),
            Ok(RecursionIdentity::Node(fixture.reference_node))
        );

        let symbol_reference = store
            .alloc_type_reference(ObjectFlags::NONE, Some(object_symbol))
            .unwrap();
        assert_eq!(
            store.recursion_identity_if_available(symbol_reference),
            Ok(RecursionIdentity::Symbol(object_symbol))
        );

        let tuple_metadata = store.create_tuple_metadata(Vec::new(), false).unwrap();
        let tuple_target = store
            .alloc_tuple_type(ObjectFlags::NONE, None, tuple_metadata)
            .unwrap();
        let tuple_reference = alloc_resolved_reference(store, tuple_target, Vec::new());
        assert_eq!(
            store.recursion_identity_if_available(tuple_reference),
            Ok(RecursionIdentity::Type(tuple_target))
        );

        let tuple_from_type_node = alloc_resolved_reference(store, tuple_target, Vec::new());
        assert!(store.set_type_object_flags(
            tuple_from_type_node,
            ObjectFlags::REFERENCE | ObjectFlags::FROM_TYPE_NODE
        ));
        assert_eq!(
            store.recursion_identity_if_available(tuple_from_type_node),
            Ok(RecursionIdentity::Type(tuple_from_type_node))
        );

        let type_parameter = store.alloc_type_parameter(Some(parameter_symbol)).unwrap();
        let anonymous_parameter = store.alloc_type_parameter(None).unwrap();
        assert_eq!(
            store.recursion_identity_if_available(type_parameter),
            Ok(RecursionIdentity::Symbol(parameter_symbol))
        );
        assert_eq!(
            store.recursion_identity_if_available(anonymous_parameter),
            Ok(RecursionIdentity::Type(anonymous_parameter))
        );

        let indexed_inner = store
            .alloc_indexed_access_type(base, base, AccessFlags::NONE)
            .unwrap();
        let indexed_outer = store
            .alloc_indexed_access_type(indexed_inner, base, AccessFlags::NONE)
            .unwrap();
        assert_eq!(
            store.recursion_identity_if_available(indexed_outer),
            Ok(RecursionIdentity::Type(base))
        );

        let root = store
            .alloc_conditional_root(fixture.conditional_node, base, base, true, None, None, None)
            .unwrap();
        let conditional = store
            .alloc_conditional_type(root, base, base, None, None)
            .unwrap();
        assert_eq!(
            store.recursion_identity_if_available(conditional),
            Ok(RecursionIdentity::Node(fixture.conditional_node))
        );
    }

    #[test]
    fn recursion_identity_rejects_foreign_and_incomplete_reference_provenance() {
        let mut store = TestStore::new();
        let incomplete_tuple = store
            .alloc_tuple_type(
                ObjectFlags::NONE,
                None,
                store.create_tuple_metadata(Vec::new(), false).unwrap(),
            )
            .unwrap();
        assert_eq!(
            store.recursion_identity_if_available(incomplete_tuple),
            Err(RecursionIdentityUnavailable::TypeReferenceTarget(
                incomplete_tuple
            ))
        );

        let mut foreign_store = TestStore::new();
        let foreign = foreign_store
            .alloc_intrinsic_type(TypeFlags::STRING, "foreign")
            .unwrap();
        assert_eq!(
            store.recursion_identity_if_available(foreign),
            Err(RecursionIdentityUnavailable::Type(foreign))
        );
    }

    #[test]
    fn relation_flag_values_and_composites_match_the_pinned_checker() {
        assert_eq!(size_of::<SignatureCheckMode>(), size_of::<u32>());
        assert_eq!(size_of::<MinArgumentCountFlags>(), size_of::<u32>());
        assert_eq!(size_of::<IntersectionState>(), size_of::<u32>());
        assert_eq!(size_of::<RecursionFlags>(), size_of::<u32>());
        assert_eq!(size_of::<ExpandingFlags>(), size_of::<u8>());
        assert_eq!(size_of::<RelationComparisonResult>(), size_of::<u32>());

        assert_eq!(SignatureCheckMode::NONE.bits(), 0);
        assert_eq!(SignatureCheckMode::BIVARIANT_CALLBACK.bits(), 1);
        assert_eq!(SignatureCheckMode::STRICT_CALLBACK.bits(), 2);
        assert_eq!(SignatureCheckMode::IGNORE_RETURN_TYPES.bits(), 4);
        assert_eq!(SignatureCheckMode::STRICT_ARITY.bits(), 8);
        assert_eq!(SignatureCheckMode::STRICT_TOP_SIGNATURE.bits(), 16);
        assert_eq!(SignatureCheckMode::CALLBACK.bits(), 3);

        assert_eq!(MinArgumentCountFlags::NONE.bits(), 0);
        assert_eq!(MinArgumentCountFlags::STRONG_ARITY_FOR_UNTYPED_JS.bits(), 1);
        assert_eq!(MinArgumentCountFlags::VOID_IS_NON_OPTIONAL.bits(), 2);

        assert_eq!(IntersectionState::NONE.bits(), 0);
        assert_eq!(IntersectionState::SOURCE.bits(), 1);
        assert_eq!(IntersectionState::TARGET.bits(), 2);
        assert_eq!(
            (IntersectionState::SOURCE | IntersectionState::TARGET).bits(),
            3
        );

        assert_eq!(RecursionFlags::NONE.bits(), 0);
        assert_eq!(RecursionFlags::SOURCE.bits(), 1);
        assert_eq!(RecursionFlags::TARGET.bits(), 2);
        assert_eq!(RecursionFlags::BOTH.bits(), 3);

        assert_eq!(ExpandingFlags::NONE.bits(), 0);
        assert_eq!(ExpandingFlags::SOURCE.bits(), 1);
        assert_eq!(ExpandingFlags::TARGET.bits(), 2);
        assert_eq!(ExpandingFlags::BOTH.bits(), 3);

        assert_eq!(RelationComparisonResult::NONE.bits(), 0);
        assert_eq!(RelationComparisonResult::SUCCEEDED.bits(), 1);
        assert_eq!(RelationComparisonResult::FAILED.bits(), 2);
        assert_eq!(RelationComparisonResult::REPORTS_UNMEASURABLE.bits(), 8);
        assert_eq!(RelationComparisonResult::REPORTS_UNRELIABLE.bits(), 16);
        assert_eq!(RelationComparisonResult::COMPLEXITY_OVERFLOW.bits(), 32);
        assert_eq!(RelationComparisonResult::STACK_DEPTH_OVERFLOW.bits(), 64);
        assert_eq!(RelationComparisonResult::REPORTS_MASK.bits(), 24);
        assert_eq!(RelationComparisonResult::OVERFLOW.bits(), 96);

        let result = RelationComparisonResult::FAILED
            | RelationComparisonResult::REPORTS_UNRELIABLE
            | RelationComparisonResult::COMPLEXITY_OVERFLOW;
        assert!(result.contains(RelationComparisonResult::FAILED));
        assert!(result.intersects(RelationComparisonResult::OVERFLOW));
        assert_eq!(
            (result & RelationComparisonResult::REPORTS_MASK).bits(),
            RelationComparisonResult::REPORTS_UNRELIABLE.bits()
        );
    }

    #[test]
    fn relation_cache_is_lazy_and_preserves_exact_get_set_size_and_budget() {
        let mut caches = RelationCaches::default();
        let key = CacheHashKey::from_halves(1, 2);
        assert_eq!(caches.snapshot(), RelationStateSnapshot::default());
        assert!(!caches.is_allocated(RelationKind::Assignable));
        assert_eq!(
            caches.get(RelationKind::Assignable, key),
            RelationComparisonResult::NONE
        );
        assert!(!caches.is_allocated(RelationKind::Assignable));
        assert_eq!(caches.size(RelationKind::Assignable), 0);
        assert_eq!(
            caches.comparison_budget(RelationKind::Assignable),
            2_000_000
        );

        caches.set(
            RelationKind::Assignable,
            key,
            RelationComparisonResult::FAILED | RelationComparisonResult::REPORTS_UNMEASURABLE,
        );
        assert!(caches.is_allocated(RelationKind::Assignable));
        assert_eq!(caches.size(RelationKind::Assignable), 1);
        assert_eq!(
            caches.comparison_budget(RelationKind::Assignable),
            1_999_999
        );
        assert_eq!(
            caches.get(RelationKind::Assignable, key),
            RelationComparisonResult::FAILED | RelationComparisonResult::REPORTS_UNMEASURABLE
        );

        caches.set(
            RelationKind::Assignable,
            key,
            RelationComparisonResult::SUCCEEDED,
        );
        assert_eq!(caches.size(RelationKind::Assignable), 1);
        assert_eq!(
            caches.get(RelationKind::Assignable, key),
            RelationComparisonResult::SUCCEEDED
        );

        let second = CacheHashKey::from_halves(3, 4);
        caches.set(
            RelationKind::Assignable,
            second,
            RelationComparisonResult::NONE,
        );
        assert_eq!(caches.size(RelationKind::Assignable), 2);
        assert_eq!(
            caches.get(RelationKind::Assignable, second),
            RelationComparisonResult::NONE
        );
        assert_eq!(
            caches.comparison_budget(RelationKind::Assignable),
            1_999_999
        );
    }

    #[test]
    fn allocated_empty_relation_map_remains_distinct_from_nil() {
        let nil = Relation::default();
        let allocated = Relation {
            results: Some(HashMap::new()),
        };
        let key = CacheHashKey::new(1);
        assert_eq!(nil.get(key), RelationComparisonResult::NONE);
        assert_eq!(allocated.get(key), RelationComparisonResult::NONE);
        assert_eq!(nil.size(), 0);
        assert_eq!(allocated.size(), 0);
        assert_eq!(nil.comparison_budget(), allocated.comparison_budget());
        assert_eq!(nil.snapshot(), RelationCacheSnapshot::default());
        assert_eq!(
            allocated.snapshot(),
            RelationCacheSnapshot {
                allocated: true,
                entries: 0,
            }
        );
        assert_ne!(nil.snapshot(), allocated.snapshot());
    }

    #[test]
    fn relation_comparison_budget_preserves_go_integer_division_boundaries() {
        assert_eq!(comparison_budget_for_size(0), 2_000_000);
        assert_eq!(comparison_budget_for_size(1), 1_999_999);
        assert_eq!(comparison_budget_for_size(8), 1_999_999);
        assert_eq!(comparison_budget_for_size(9), 1_999_998);
        assert_eq!(comparison_budget_for_size(15_999_992), 1);
        assert_eq!(comparison_budget_for_size(15_999_993), 0);
        assert_eq!(comparison_budget_for_size(16_000_000), 0);
        assert_eq!(comparison_budget_for_size(16_000_007), 0);
        assert_eq!(comparison_budget_for_size(16_000_008), -1);
    }

    #[test]
    fn five_relation_owners_keep_the_same_key_isolated() {
        let mut caches = RelationCaches::default();
        let key = CacheHashKey::new(9);
        let values = [
            RelationComparisonResult::SUCCEEDED,
            RelationComparisonResult::FAILED,
            RelationComparisonResult::REPORTS_UNMEASURABLE,
            RelationComparisonResult::REPORTS_UNRELIABLE,
            RelationComparisonResult::COMPLEXITY_OVERFLOW,
        ];
        for (kind, value) in RelationKind::ALL.into_iter().zip(values) {
            caches.set(kind, key, value);
        }
        for (kind, value) in RelationKind::ALL.into_iter().zip(values) {
            assert_eq!(caches.get(kind, key), value);
            assert_eq!(caches.size(kind), 1);
            assert!(caches.is_allocated(kind));
        }
        assert!(RelationKind::Identity.is_identity());
        assert!(!RelationKind::Assignable.is_identity());
    }
}
