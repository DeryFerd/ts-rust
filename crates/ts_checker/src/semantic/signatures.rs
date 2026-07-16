//! Semantic enums and flags used by canonical signature, tuple, and index records.
//!
//! Values are pinned to typescript-go `internal/checker/types.go` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`.

use ts_ast::NodeRef;

use super::ids::{
    IndexInfoId, SemanticStoreId, SemanticSymbolId, SignatureId, TypeId, TypeMapperId,
    TypePredicateId, TypedArena,
};

macro_rules! impl_flag_operators {
    ($flags:ty) => {
        impl std::ops::BitAnd for $flags {
            type Output = Self;

            fn bitand(self, rhs: Self) -> Self::Output {
                Self(self.0 & rhs.0)
            }
        }

        impl std::ops::BitAndAssign for $flags {
            fn bitand_assign(&mut self, rhs: Self) {
                self.0 &= rhs.0;
            }
        }

        impl std::ops::BitOr for $flags {
            type Output = Self;

            fn bitor(self, rhs: Self) -> Self::Output {
                Self(self.0 | rhs.0)
            }
        }

        impl std::ops::BitOrAssign for $flags {
            fn bitor_assign(&mut self, rhs: Self) {
                self.0 |= rhs.0;
            }
        }

        impl std::ops::BitXor for $flags {
            type Output = Self;

            fn bitxor(self, rhs: Self) -> Self::Output {
                Self(self.0 ^ rhs.0)
            }
        }

        impl std::ops::Not for $flags {
            type Output = Self;

            fn not(self) -> Self::Output {
                Self(!self.0)
            }
        }
    };
}

/// Selects call or construct signatures.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(i32)]
pub enum SignatureKind {
    #[default]
    Call = 0,
    Construct = 1,
}

/// Metadata propagated while signatures are instantiated and combined.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct SignatureFlags(u32);

impl SignatureFlags {
    pub const NONE: Self = Self(0);
    pub const HAS_REST_PARAMETER: Self = Self(1 << 0);
    pub const HAS_LITERAL_TYPES: Self = Self(1 << 1);
    pub const CONSTRUCT: Self = Self(1 << 2);
    pub const ABSTRACT: Self = Self(1 << 3);
    pub const IS_INNER_CALL_CHAIN: Self = Self(1 << 4);
    pub const IS_OUTER_CALL_CHAIN: Self = Self(1 << 5);
    pub const IS_UNTYPED_SIGNATURE_IN_JS_FILE: Self = Self(1 << 6);
    pub const IS_NON_INFERRABLE: Self = Self(1 << 7);
    pub const IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE: Self = Self(1 << 8);

    /// Flags copied to instantiated signatures.
    ///
    /// Call-chain position is deliberately excluded so recursive return-type
    /// instantiation does not repeatedly add `undefined`.
    pub const PROPAGATING_FLAGS: Self = Self(
        Self::HAS_REST_PARAMETER.0
            | Self::HAS_LITERAL_TYPES.0
            | Self::CONSTRUCT.0
            | Self::ABSTRACT.0
            | Self::IS_UNTYPED_SIGNATURE_IN_JS_FILE.0
            | Self::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE.0,
    );
    pub const CALL_CHAIN_FLAGS: Self =
        Self(Self::IS_INNER_CALL_CHAIN.0 | Self::IS_OUTER_CALL_CHAIN.0);

    #[must_use]
    pub const fn bits(self) -> u32 {
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

impl_flag_operators!(SignatureFlags);

/// The storage and arity behavior of one tuple element.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct ElementFlags(u32);

impl ElementFlags {
    pub const NONE: Self = Self(0);
    pub const REQUIRED: Self = Self(1 << 0);
    pub const OPTIONAL: Self = Self(1 << 1);
    pub const REST: Self = Self(1 << 2);
    pub const VARIADIC: Self = Self(1 << 3);

    pub const FIXED: Self = Self(Self::REQUIRED.0 | Self::OPTIONAL.0);
    pub const VARIABLE: Self = Self(Self::REST.0 | Self::VARIADIC.0);
    pub const NON_REQUIRED: Self = Self(Self::OPTIONAL.0 | Self::REST.0 | Self::VARIADIC.0);
    pub const NON_REST: Self = Self(Self::REQUIRED.0 | Self::OPTIONAL.0 | Self::VARIADIC.0);

    #[must_use]
    pub const fn bits(self) -> u32 {
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

impl_flag_operators!(ElementFlags);

/// Controls canonical index-type construction and reduction.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct IndexFlags(u32);

impl IndexFlags {
    pub const NONE: Self = Self(0);
    pub const STRINGS_ONLY: Self = Self(1 << 0);
    pub const NO_INDEX_SIGNATURES: Self = Self(1 << 1);
    pub const NO_REDUCIBLE_CHECK: Self = Self(1 << 2);

    #[must_use]
    pub const fn bits(self) -> u32 {
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

impl_flag_operators!(IndexFlags);

/// The syntactic form represented by a type predicate.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(i32)]
pub enum TypePredicateKind {
    #[default]
    This = 0,
    Identifier = 1,
    AssertsThis = 2,
    AssertsIdentifier = 3,
}

/// Four-valued result of a canonical type relation.
///
/// The representation makes bitwise AND select the lesser and bitwise OR the
/// greater value in `False < Unknown < Maybe < True`. `Maybe` marks a relation
/// that depends on itself; `Unknown` marks a variance check that depends on
/// itself and therefore must not be cached as a circular variance result.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
#[repr(i8)]
pub enum Ternary {
    #[default]
    False = 0,
    Unknown = 1,
    Maybe = 3,
    True = -1,
}

impl Ternary {
    const fn from_value(value: i8) -> Self {
        match value {
            0 => Self::False,
            1 => Self::Unknown,
            3 => Self::Maybe,
            -1 => Self::True,
            _ => panic!("invalid Ternary bitwise result"),
        }
    }
}

impl std::ops::BitAnd for Ternary {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::from_value((self as i8) & (rhs as i8))
    }
}

impl std::ops::BitAndAssign for Ternary {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl std::ops::BitOr for Ternary {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::from_value((self as i8) | (rhs as i8))
    }
}

impl std::ops::BitOrAssign for Ternary {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

/// Canonical call or construct signature.
///
/// This is the ID-based equivalent of typescript-go's `Signature`. Pointer
/// fields become IDs in their owning semantic arenas and AST pointers become
/// program-wide [`NodeRef`] values. Allocation is restricted to the aggregate
/// [`super::SemanticStore`], so IDs and references cannot cross programs.
#[derive(Debug, Eq, PartialEq)]
pub struct Signature {
    id: SignatureId,
    flags: SignatureFlags,
    min_argument_count: i32,
    resolved_min_argument_count: i32,
    declaration: Option<NodeRef>,
    type_parameters: Vec<TypeId>,
    parameters: Vec<SemanticSymbolId>,
    this_parameter: Option<SemanticSymbolId>,
    resolved_return_type: Option<TypeId>,
    resolved_type_predicate: Option<TypePredicateId>,
    target: Option<SignatureId>,
    mapper: Option<TypeMapperId>,
    isolated_signature_type: Option<TypeId>,
    composite: Option<CompositeSignature>,
}

impl Signature {
    #[must_use]
    pub const fn id(&self) -> SignatureId {
        self.id
    }

    #[must_use]
    pub const fn flags(&self) -> SignatureFlags {
        self.flags
    }

    #[must_use]
    pub const fn min_argument_count(&self) -> i32 {
        self.min_argument_count
    }

    /// Returns `-1` until lazy minimum-argument resolution has completed.
    #[must_use]
    pub const fn resolved_min_argument_count(&self) -> i32 {
        self.resolved_min_argument_count
    }

    #[must_use]
    pub const fn declaration(&self) -> Option<NodeRef> {
        self.declaration
    }

    #[must_use]
    pub fn type_parameters(&self) -> &[TypeId] {
        &self.type_parameters
    }

    #[must_use]
    pub fn parameters(&self) -> &[SemanticSymbolId] {
        &self.parameters
    }

    #[must_use]
    pub const fn this_parameter(&self) -> Option<SemanticSymbolId> {
        self.this_parameter
    }

    #[must_use]
    pub const fn resolved_return_type(&self) -> Option<TypeId> {
        self.resolved_return_type
    }

    #[must_use]
    pub const fn resolved_type_predicate(&self) -> Option<TypePredicateId> {
        self.resolved_type_predicate
    }

    #[must_use]
    pub const fn target(&self) -> Option<SignatureId> {
        self.target
    }

    #[must_use]
    pub const fn mapper(&self) -> Option<TypeMapperId> {
        self.mapper
    }

    #[must_use]
    pub const fn isolated_signature_type(&self) -> Option<TypeId> {
        self.isolated_signature_type
    }

    #[must_use]
    pub const fn composite(&self) -> Option<&CompositeSignature> {
        self.composite.as_ref()
    }

    #[must_use]
    pub const fn has_rest_parameter(&self) -> bool {
        self.flags.contains(SignatureFlags::HAS_REST_PARAMETER)
    }
}

/// Store-owned storage for canonical signatures.
#[derive(Debug)]
pub(super) struct SignatureArena {
    signatures: TypedArena<SignatureId, Signature>,
}

impl SignatureArena {
    pub(super) fn new(store: SemanticStoreId) -> Self {
        Self {
            signatures: TypedArena::new(store),
        }
    }

    /// Implements the record initialization performed by
    /// typescript-go `checker.go::newSignature`.
    ///
    /// `target`, `mapper`, `isolated_signature_type`, and `composite` start
    /// absent, and `resolved_min_argument_count` starts at the exact upstream
    /// sentinel value `-1`.
    ///
    /// # Panics
    ///
    /// Panics before modifying the arena if all `u32` identities have already
    /// been allocated.
    #[allow(clippy::too_many_arguments)] // Mirrors upstream newSignature exactly.
    pub(super) fn alloc(
        &mut self,
        flags: SignatureFlags,
        declaration: Option<NodeRef>,
        type_parameters: Vec<TypeId>,
        this_parameter: Option<SemanticSymbolId>,
        parameters: Vec<SemanticSymbolId>,
        resolved_return_type: Option<TypeId>,
        resolved_type_predicate: Option<TypePredicateId>,
        min_argument_count: i32,
    ) -> SignatureId {
        self.signatures.alloc_with(|id| Signature {
            id,
            flags,
            min_argument_count,
            resolved_min_argument_count: -1,
            declaration,
            type_parameters,
            parameters,
            this_parameter,
            resolved_return_type,
            resolved_type_predicate,
            target: None,
            mapper: None,
            isolated_signature_type: None,
            composite: None,
        })
    }

    #[must_use]
    pub(super) fn get(&self, id: SignatureId) -> Option<&Signature> {
        self.signatures.get(id)
    }

    #[must_use]
    pub(super) fn len(&self) -> usize {
        self.signatures.len()
    }

    pub(super) fn try_reserve(&mut self, additional: usize) -> bool {
        self.signatures.try_reserve(additional)
    }

    #[must_use]
    pub(super) fn iter(&self) -> impl ExactSizeIterator<Item = (SignatureId, &Signature)> {
        self.signatures.iter()
    }

    /// Updates the lazy cache written by
    /// typescript-go `getMinArgumentCount`.
    pub(super) fn set_resolved_min_argument_count(&mut self, id: SignatureId, count: i32) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.resolved_min_argument_count = count;
        true
    }

    /// Updates the lazy return-type slot used during signature resolution.
    pub(super) fn set_resolved_return_type(
        &mut self,
        id: SignatureId,
        type_id: Option<TypeId>,
    ) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.resolved_return_type = type_id;
        true
    }

    /// Updates the lazy type-predicate slot used during signature resolution.
    pub(super) fn set_resolved_type_predicate(
        &mut self,
        id: SignatureId,
        predicate: Option<TypePredicateId>,
    ) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.resolved_type_predicate = predicate;
        true
    }

    /// Updates the lazily constructed isolated signature type.
    pub(super) fn set_isolated_signature_type(
        &mut self,
        id: SignatureId,
        type_id: Option<TypeId>,
    ) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.isolated_signature_type = type_id;
        true
    }

    /// Records the source signature and mapper for an instantiated signature.
    ///
    /// A target from outside this arena is rejected. Mapper identity belongs
    /// to the program's canonical mapper arena and is therefore type-checked
    /// here but validated by the eventual aggregate semantic store.
    pub(super) fn set_target_and_mapper(
        &mut self,
        id: SignatureId,
        target: Option<SignatureId>,
        mapper: Option<TypeMapperId>,
    ) -> bool {
        if target.is_some_and(|target| self.signatures.get(target).is_none()) {
            return false;
        }
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.target = target;
        signature.mapper = mapper;
        true
    }

    /// Attaches immutable union/intersection provenance to a signature.
    ///
    /// Every constituent must already exist in this arena, preventing a
    /// composite record from silently holding an out-of-range signature ID.
    pub(super) fn set_composite(
        &mut self,
        id: SignatureId,
        composite: Option<CompositeSignature>,
    ) -> bool {
        if composite.as_ref().is_some_and(|composite| {
            composite
                .signatures()
                .iter()
                .any(|signature| self.signatures.get(*signature).is_none())
        }) {
            return false;
        }
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.composite = composite;
        true
    }

    pub(super) fn set_flags(&mut self, id: SignatureId, flags: SignatureFlags) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.flags = flags;
        true
    }

    pub(super) fn set_type_parameters(
        &mut self,
        id: SignatureId,
        type_parameters: Vec<TypeId>,
    ) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.type_parameters = type_parameters;
        true
    }

    pub(super) fn set_this_parameter(
        &mut self,
        id: SignatureId,
        this_parameter: Option<SemanticSymbolId>,
    ) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.this_parameter = this_parameter;
        true
    }
}

/// Constituent signatures combined as a union or intersection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompositeSignature {
    is_union: bool,
    signatures: Vec<SignatureId>,
}

impl CompositeSignature {
    pub(super) const fn new(is_union: bool, signatures: Vec<SignatureId>) -> Self {
        Self {
            is_union,
            signatures,
        }
    }

    #[must_use]
    pub const fn is_union(&self) -> bool {
        self.is_union
    }

    #[must_use]
    pub fn signatures(&self) -> &[SignatureId] {
        &self.signatures
    }
}

/// Canonical semantic type predicate.
#[derive(Debug, Eq, PartialEq)]
pub struct TypePredicate {
    id: TypePredicateId,
    kind: TypePredicateKind,
    parameter_index: i32,
    parameter_name: String,
    type_id: Option<TypeId>,
}

impl TypePredicate {
    #[must_use]
    pub const fn id(&self) -> TypePredicateId {
        self.id
    }

    #[must_use]
    pub const fn kind(&self) -> TypePredicateKind {
        self.kind
    }

    #[must_use]
    pub const fn parameter_index(&self) -> i32 {
        self.parameter_index
    }

    #[must_use]
    pub fn parameter_name(&self) -> &str {
        &self.parameter_name
    }

    /// The narrowed type, if one was written. Assertion predicates may omit it.
    #[must_use]
    pub const fn type_id(&self) -> Option<TypeId> {
        self.type_id
    }
}

/// Store-owned storage for canonical type predicates.
#[derive(Debug)]
pub(super) struct TypePredicateArena {
    predicates: TypedArena<TypePredicateId, TypePredicate>,
}

impl TypePredicateArena {
    pub(super) fn new(store: SemanticStoreId) -> Self {
        Self {
            predicates: TypedArena::new(store),
        }
    }

    /// # Panics
    ///
    /// Panics before modifying the arena if all `u32` identities have already
    /// been allocated.
    pub(super) fn alloc(
        &mut self,
        kind: TypePredicateKind,
        parameter_index: i32,
        parameter_name: impl Into<String>,
        type_id: Option<TypeId>,
    ) -> TypePredicateId {
        let parameter_name = parameter_name.into();
        self.predicates.alloc_with(|id| TypePredicate {
            id,
            kind,
            parameter_index,
            parameter_name,
            type_id,
        })
    }

    #[must_use]
    pub(super) fn get(&self, id: TypePredicateId) -> Option<&TypePredicate> {
        self.predicates.get(id)
    }

    #[must_use]
    pub(super) fn len(&self) -> usize {
        self.predicates.len()
    }
}

/// Canonical index-signature information.
#[derive(Debug, Eq, PartialEq)]
pub struct IndexInfo {
    id: IndexInfoId,
    key_type: TypeId,
    value_type: TypeId,
    is_readonly: bool,
    declaration: Option<NodeRef>,
    index_symbol: Option<SemanticSymbolId>,
    components: Vec<NodeRef>,
}

impl IndexInfo {
    #[must_use]
    pub const fn id(&self) -> IndexInfoId {
        self.id
    }

    #[must_use]
    pub const fn key_type(&self) -> TypeId {
        self.key_type
    }

    #[must_use]
    pub const fn value_type(&self) -> TypeId {
        self.value_type
    }

    #[must_use]
    pub const fn is_readonly(&self) -> bool {
        self.is_readonly
    }

    #[must_use]
    pub const fn declaration(&self) -> Option<NodeRef> {
        self.declaration
    }

    #[must_use]
    pub const fn index_symbol(&self) -> Option<SemanticSymbolId> {
        self.index_symbol
    }

    #[must_use]
    pub fn components(&self) -> &[NodeRef] {
        &self.components
    }
}

/// Store-owned storage for canonical index information.
#[derive(Debug)]
pub(super) struct IndexInfoArena {
    infos: TypedArena<IndexInfoId, IndexInfo>,
}

impl IndexInfoArena {
    pub(super) fn new(store: SemanticStoreId) -> Self {
        Self {
            infos: TypedArena::new(store),
        }
    }

    #[must_use]
    pub(super) fn try_reserve(&mut self, additional: usize) -> bool {
        self.infos.try_reserve(additional)
    }

    /// Implements the record initialization performed by
    /// typescript-go `checker.go::newIndexInfo`.
    ///
    /// # Panics
    ///
    /// Panics before modifying the arena if all `u32` identities have already
    /// been allocated.
    pub(super) fn alloc(
        &mut self,
        key_type: TypeId,
        value_type: TypeId,
        is_readonly: bool,
        declaration: Option<NodeRef>,
        components: Vec<NodeRef>,
    ) -> IndexInfoId {
        self.infos.alloc_with(|id| IndexInfo {
            id,
            key_type,
            value_type,
            is_readonly,
            declaration,
            index_symbol: None,
            components,
        })
    }

    #[must_use]
    pub(super) fn get(&self, id: IndexInfoId) -> Option<&IndexInfo> {
        self.infos.get(id)
    }

    #[must_use]
    pub(super) fn len(&self) -> usize {
        self.infos.len()
    }

    /// Updates the synthetic property symbol lazily created for this index.
    pub(super) fn set_index_symbol(
        &mut self,
        id: IndexInfoId,
        symbol: Option<SemanticSymbolId>,
    ) -> bool {
        let Some(info) = self.infos.get_mut(id) else {
            return false;
        };
        info.index_symbol = symbol;
        true
    }
}

/// Flags and optional label declaration for one tuple element.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TupleElementInfo {
    flags: ElementFlags,
    labeled_declaration: Option<NodeRef>,
}

impl TupleElementInfo {
    pub(super) const fn new(flags: ElementFlags, labeled_declaration: Option<NodeRef>) -> Self {
        Self {
            flags,
            labeled_declaration,
        }
    }

    #[must_use]
    pub const fn flags(self) -> ElementFlags {
        self.flags
    }

    #[must_use]
    pub const fn labeled_declaration(self) -> Option<NodeRef> {
        self.labeled_declaration
    }
}

/// Tuple-specific metadata from typescript-go's `TupleType` record.
///
/// The embedded interface/type payload is deliberately outside this
/// dependency-closed cluster. Length and combined-flag fields are derived with
/// the same rules as `checker.go::createTupleTargetType`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TupleMetadata {
    element_infos: Vec<TupleElementInfo>,
    min_length: usize,
    fixed_length: usize,
    combined_flags: ElementFlags,
    readonly: bool,
}

impl TupleMetadata {
    pub(super) fn new(element_infos: Vec<TupleElementInfo>, readonly: bool) -> Self {
        let mut min_length = 0;
        let mut combined_flags = ElementFlags::NONE;
        let mut fixed_length = element_infos.len();
        for (index, info) in element_infos.iter().enumerate() {
            let flags = info.flags();
            if flags.intersects(ElementFlags::REQUIRED | ElementFlags::VARIADIC) {
                min_length += 1;
            }
            combined_flags |= flags;
            if fixed_length == element_infos.len()
                && combined_flags.intersects(ElementFlags::VARIABLE)
            {
                fixed_length = index;
            }
        }
        Self {
            element_infos,
            min_length,
            fixed_length,
            combined_flags,
            readonly,
        }
    }

    #[must_use]
    pub fn element_infos(&self) -> &[TupleElementInfo] {
        &self.element_infos
    }

    #[must_use]
    pub fn element_flags(&self) -> Vec<ElementFlags> {
        self.element_infos.iter().map(|info| info.flags()).collect()
    }

    #[must_use]
    pub const fn min_length(&self) -> usize {
        self.min_length
    }

    #[must_use]
    pub const fn fixed_length(&self) -> usize {
        self.fixed_length
    }

    #[must_use]
    pub const fn combined_flags(&self) -> ElementFlags {
        self.combined_flags
    }

    #[must_use]
    pub const fn is_readonly(&self) -> bool {
        self.readonly
    }
}

#[cfg(test)]
mod tests {
    use std::mem::size_of;

    use super::{
        ElementFlags, IndexFlags, SignatureFlags, SignatureKind, Ternary, TypePredicateKind,
    };

    #[test]
    fn signature_kinds_match_upstream_repr_and_values() {
        assert_eq!(size_of::<SignatureKind>(), size_of::<i32>());
        assert_eq!(
            [SignatureKind::Call as i32, SignatureKind::Construct as i32],
            [0, 1]
        );
    }

    #[test]
    fn signature_flags_match_every_upstream_numeric_value() {
        assert_eq!(size_of::<SignatureFlags>(), size_of::<u32>());
        assert_eq!(
            [
                SignatureFlags::NONE.bits(),
                SignatureFlags::HAS_REST_PARAMETER.bits(),
                SignatureFlags::HAS_LITERAL_TYPES.bits(),
                SignatureFlags::CONSTRUCT.bits(),
                SignatureFlags::ABSTRACT.bits(),
                SignatureFlags::IS_INNER_CALL_CHAIN.bits(),
                SignatureFlags::IS_OUTER_CALL_CHAIN.bits(),
                SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE.bits(),
                SignatureFlags::IS_NON_INFERRABLE.bits(),
                SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE.bits(),
                SignatureFlags::PROPAGATING_FLAGS.bits(),
                SignatureFlags::CALL_CHAIN_FLAGS.bits(),
            ],
            [0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 335, 48]
        );
        assert!(
            SignatureFlags::PROPAGATING_FLAGS
                .contains(SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE)
        );
        assert_eq!(
            SignatureFlags::HAS_REST_PARAMETER
                | SignatureFlags::HAS_LITERAL_TYPES
                | SignatureFlags::CONSTRUCT
                | SignatureFlags::ABSTRACT
                | SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE
                | SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE,
            SignatureFlags::PROPAGATING_FLAGS
        );
        assert_eq!(
            SignatureFlags::IS_INNER_CALL_CHAIN | SignatureFlags::IS_OUTER_CALL_CHAIN,
            SignatureFlags::CALL_CHAIN_FLAGS
        );
        assert!(!SignatureFlags::PROPAGATING_FLAGS.intersects(SignatureFlags::CALL_CHAIN_FLAGS));
        assert!(!SignatureFlags::PROPAGATING_FLAGS.intersects(SignatureFlags::IS_NON_INFERRABLE));
    }

    #[test]
    fn element_flags_match_every_upstream_numeric_and_composite_value() {
        assert_eq!(size_of::<ElementFlags>(), size_of::<u32>());
        assert_eq!(
            [
                ElementFlags::NONE.bits(),
                ElementFlags::REQUIRED.bits(),
                ElementFlags::OPTIONAL.bits(),
                ElementFlags::REST.bits(),
                ElementFlags::VARIADIC.bits(),
                ElementFlags::FIXED.bits(),
                ElementFlags::VARIABLE.bits(),
                ElementFlags::NON_REQUIRED.bits(),
                ElementFlags::NON_REST.bits(),
            ],
            [0, 1, 2, 4, 8, 3, 12, 14, 11]
        );
        assert_eq!(
            ElementFlags::REQUIRED | ElementFlags::OPTIONAL,
            ElementFlags::FIXED
        );
        assert_eq!(
            ElementFlags::REST | ElementFlags::VARIADIC,
            ElementFlags::VARIABLE
        );
        assert_eq!(
            ElementFlags::OPTIONAL | ElementFlags::REST | ElementFlags::VARIADIC,
            ElementFlags::NON_REQUIRED
        );
        assert_eq!(
            ElementFlags::REQUIRED | ElementFlags::OPTIONAL | ElementFlags::VARIADIC,
            ElementFlags::NON_REST
        );
    }

    #[test]
    fn index_flags_match_every_upstream_numeric_value() {
        assert_eq!(size_of::<IndexFlags>(), size_of::<u32>());
        assert_eq!(
            [
                IndexFlags::NONE.bits(),
                IndexFlags::STRINGS_ONLY.bits(),
                IndexFlags::NO_INDEX_SIGNATURES.bits(),
                IndexFlags::NO_REDUCIBLE_CHECK.bits(),
            ],
            [0, 1, 2, 4]
        );
    }

    #[test]
    fn type_predicate_kinds_match_upstream_repr_and_values() {
        assert_eq!(size_of::<TypePredicateKind>(), size_of::<i32>());
        assert_eq!(
            [
                TypePredicateKind::This as i32,
                TypePredicateKind::Identifier as i32,
                TypePredicateKind::AssertsThis as i32,
                TypePredicateKind::AssertsIdentifier as i32,
            ],
            [0, 1, 2, 3]
        );
    }

    #[test]
    fn ternary_values_match_upstream_i8_repr() {
        assert_eq!(size_of::<Ternary>(), size_of::<i8>());
        assert_eq!(
            [
                Ternary::False as i8,
                Ternary::Unknown as i8,
                Ternary::Maybe as i8,
                Ternary::True as i8,
            ],
            [0, 1, 3, -1]
        );
    }

    #[test]
    fn ternary_and_truth_table_selects_the_lesser_value() {
        let values = [
            Ternary::False,
            Ternary::Unknown,
            Ternary::Maybe,
            Ternary::True,
        ];
        let expected = [
            [
                Ternary::False,
                Ternary::False,
                Ternary::False,
                Ternary::False,
            ],
            [
                Ternary::False,
                Ternary::Unknown,
                Ternary::Unknown,
                Ternary::Unknown,
            ],
            [
                Ternary::False,
                Ternary::Unknown,
                Ternary::Maybe,
                Ternary::Maybe,
            ],
            [
                Ternary::False,
                Ternary::Unknown,
                Ternary::Maybe,
                Ternary::True,
            ],
        ];

        for (left_index, left) in values.into_iter().enumerate() {
            for (right_index, right) in values.into_iter().enumerate() {
                assert_eq!(left & right, expected[left_index][right_index]);
                assert_eq!((left & right) as i8, (left as i8) & (right as i8));
                let mut assigned = left;
                assigned &= right;
                assert_eq!(assigned, expected[left_index][right_index]);
            }
        }
    }

    #[test]
    fn ternary_or_truth_table_selects_the_greater_value() {
        let values = [
            Ternary::False,
            Ternary::Unknown,
            Ternary::Maybe,
            Ternary::True,
        ];
        let expected = [
            [
                Ternary::False,
                Ternary::Unknown,
                Ternary::Maybe,
                Ternary::True,
            ],
            [
                Ternary::Unknown,
                Ternary::Unknown,
                Ternary::Maybe,
                Ternary::True,
            ],
            [
                Ternary::Maybe,
                Ternary::Maybe,
                Ternary::Maybe,
                Ternary::True,
            ],
            [Ternary::True, Ternary::True, Ternary::True, Ternary::True],
        ];

        for (left_index, left) in values.into_iter().enumerate() {
            for (right_index, right) in values.into_iter().enumerate() {
                assert_eq!(left | right, expected[left_index][right_index]);
                assert_eq!((left | right) as i8, (left as i8) | (right as i8));
                let mut assigned = left;
                assigned |= right;
                assert_eq!(assigned, expected[left_index][right_index]);
            }
        }
    }
}
