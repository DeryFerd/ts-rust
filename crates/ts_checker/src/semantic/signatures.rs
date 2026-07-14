//! Semantic enums and flags used by canonical signature, tuple, and index records.
//!
//! Values are pinned to typescript-go `internal/checker/types.go` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`.

use ts_ast::NodeRef;

use super::ids::{
    IndexInfoId, SemanticSymbolId, SignatureId, TypeId, TypeMapperId, TypePredicateId, TypedArena,
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
/// program-wide [`NodeRef`] values. Allocation is restricted to
/// [`SignatureArena`] so `id` cannot disagree with arena position.
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

/// Stable storage for canonical signatures.
#[derive(Debug, Default)]
pub struct SignatureArena {
    signatures: TypedArena<SignatureId, Signature>,
}

impl SignatureArena {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
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
    pub fn alloc(
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
    pub fn get(&self, id: SignatureId) -> Option<&Signature> {
        self.signatures.get(id)
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.signatures.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.signatures.is_empty()
    }

    #[must_use]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (SignatureId, &Signature)> {
        self.signatures.iter()
    }

    /// Updates the lazy cache written by
    /// typescript-go `getMinArgumentCount`.
    pub fn set_resolved_min_argument_count(&mut self, id: SignatureId, count: i32) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.resolved_min_argument_count = count;
        true
    }

    /// Updates the lazy return-type slot used during signature resolution.
    pub fn set_resolved_return_type(&mut self, id: SignatureId, type_id: Option<TypeId>) -> bool {
        let Some(signature) = self.signatures.get_mut(id) else {
            return false;
        };
        signature.resolved_return_type = type_id;
        true
    }

    /// Updates the lazy type-predicate slot used during signature resolution.
    pub fn set_resolved_type_predicate(
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
    pub fn set_isolated_signature_type(
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
    pub fn set_target_and_mapper(
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
    pub fn set_composite(
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
}

/// Constituent signatures combined as a union or intersection.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompositeSignature {
    is_union: bool,
    signatures: Vec<SignatureId>,
}

impl CompositeSignature {
    #[must_use]
    pub const fn new(is_union: bool, signatures: Vec<SignatureId>) -> Self {
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

/// Stable storage for canonical type predicates.
#[derive(Debug, Default)]
pub struct TypePredicateArena {
    predicates: TypedArena<TypePredicateId, TypePredicate>,
}

impl TypePredicateArena {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// # Panics
    ///
    /// Panics before modifying the arena if all `u32` identities have already
    /// been allocated.
    pub fn alloc(
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
    pub fn get(&self, id: TypePredicateId) -> Option<&TypePredicate> {
        self.predicates.get(id)
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.predicates.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.predicates.is_empty()
    }

    #[must_use]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (TypePredicateId, &TypePredicate)> {
        self.predicates.iter()
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

/// Stable storage for canonical index information.
#[derive(Debug, Default)]
pub struct IndexInfoArena {
    infos: TypedArena<IndexInfoId, IndexInfo>,
}

impl IndexInfoArena {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Implements the record initialization performed by
    /// typescript-go `checker.go::newIndexInfo`.
    ///
    /// # Panics
    ///
    /// Panics before modifying the arena if all `u32` identities have already
    /// been allocated.
    pub fn alloc(
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
    pub fn get(&self, id: IndexInfoId) -> Option<&IndexInfo> {
        self.infos.get(id)
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.infos.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.infos.is_empty()
    }

    #[must_use]
    pub fn iter(&self) -> impl ExactSizeIterator<Item = (IndexInfoId, &IndexInfo)> {
        self.infos.iter()
    }

    /// Updates the synthetic property symbol lazily created for this index.
    pub fn set_index_symbol(&mut self, id: IndexInfoId, symbol: Option<SemanticSymbolId>) -> bool {
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
    #[must_use]
    pub const fn new(flags: ElementFlags, labeled_declaration: Option<NodeRef>) -> Self {
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
    #[must_use]
    pub fn new(element_infos: Vec<TupleElementInfo>, readonly: bool) -> Self {
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

    use ts_ast::{FileId, NodeId, NodeRef};

    use super::super::ids::{SemanticSymbolArena, TypeArena, TypeMapperArena};
    use super::{
        CompositeSignature, ElementFlags, IndexFlags, IndexInfoArena, SignatureArena,
        SignatureFlags, SignatureKind, Ternary, TupleElementInfo, TupleMetadata,
        TypePredicateArena, TypePredicateKind,
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

    #[test]
    fn new_signature_matches_upstream_record_defaults_and_identity() {
        let declaration = NodeRef::new(FileId::new(4), NodeId::new(19));
        let mut types = TypeArena::new();
        let type_parameter = types.alloc("T");
        let return_type = types.alloc("string");
        let isolated_type = types.alloc("isolated");
        let mut symbols = SemanticSymbolArena::new();
        let this_parameter = symbols.alloc("this");
        let parameter = symbols.alloc("value");
        let mut predicates = TypePredicateArena::new();
        let predicate =
            predicates.alloc(TypePredicateKind::Identifier, 0, "value", Some(return_type));
        let mut signatures = SignatureArena::new();

        let id = signatures.alloc(
            SignatureFlags::HAS_REST_PARAMETER | SignatureFlags::HAS_LITERAL_TYPES,
            Some(declaration),
            vec![type_parameter],
            Some(this_parameter),
            vec![parameter],
            Some(return_type),
            Some(predicate),
            1,
        );
        let signature = signatures.get(id).unwrap();

        assert_eq!(id.get(), 1);
        assert_eq!(signature.id(), id);
        assert_eq!(
            signature.flags(),
            SignatureFlags::HAS_REST_PARAMETER | SignatureFlags::HAS_LITERAL_TYPES
        );
        assert!(signature.has_rest_parameter());
        assert_eq!(signature.min_argument_count(), 1);
        assert_eq!(signature.resolved_min_argument_count(), -1);
        assert_eq!(signature.declaration(), Some(declaration));
        assert_eq!(signature.type_parameters(), [type_parameter]);
        assert_eq!(signature.parameters(), [parameter]);
        assert_eq!(signature.this_parameter(), Some(this_parameter));
        assert_eq!(signature.resolved_return_type(), Some(return_type));
        assert_eq!(signature.resolved_type_predicate(), Some(predicate));
        assert_eq!(signature.target(), None);
        assert_eq!(signature.mapper(), None);
        assert_eq!(signature.isolated_signature_type(), None);
        assert_eq!(signature.composite(), None);

        assert!(signatures.set_resolved_min_argument_count(id, 2));
        assert!(signatures.set_resolved_return_type(id, None));
        assert!(signatures.set_resolved_type_predicate(id, None));
        assert!(signatures.set_isolated_signature_type(id, Some(isolated_type)));
        let resolved = signatures.get(id).unwrap();
        assert_eq!(resolved.resolved_min_argument_count(), 2);
        assert_eq!(resolved.resolved_return_type(), None);
        assert_eq!(resolved.resolved_type_predicate(), None);
        assert_eq!(resolved.isolated_signature_type(), Some(isolated_type));

        let second = signatures.alloc(
            SignatureFlags::NONE,
            None,
            Vec::new(),
            None,
            Vec::new(),
            None,
            None,
            0,
        );
        assert_eq!(second.get(), 2);
        assert_eq!(signatures.len(), 2);
        assert_eq!(
            signatures
                .iter()
                .map(|(signature, _)| signature.get())
                .collect::<Vec<_>>(),
            [1, 2]
        );
    }

    #[test]
    fn composite_signature_preserves_union_and_constituent_order() {
        let mut signatures = SignatureArena::new();
        let first = signatures.alloc(
            SignatureFlags::NONE,
            None,
            Vec::new(),
            None,
            Vec::new(),
            None,
            None,
            0,
        );
        let second = signatures.alloc(
            SignatureFlags::CONSTRUCT,
            None,
            Vec::new(),
            None,
            Vec::new(),
            None,
            None,
            0,
        );

        let union = CompositeSignature::new(true, vec![second, first]);
        assert!(union.is_union());
        assert_eq!(union.signatures(), [second, first]);

        let intersection = CompositeSignature::new(false, vec![first, second]);
        assert!(!intersection.is_union());
        assert_eq!(intersection.signatures(), [first, second]);

        let mut mappers = TypeMapperArena::new();
        let mapper = mappers.alloc("instantiate T");
        assert!(signatures.set_target_and_mapper(second, Some(first), Some(mapper)));
        assert_eq!(signatures.get(second).unwrap().target(), Some(first));
        assert_eq!(signatures.get(second).unwrap().mapper(), Some(mapper));

        assert!(signatures.set_composite(first, Some(union.clone())));
        assert_eq!(signatures.get(first).unwrap().composite(), Some(&union));
        assert!(signatures.set_composite(first, Some(intersection.clone())));
        assert_eq!(
            signatures.get(first).unwrap().composite(),
            Some(&intersection)
        );
        assert!(signatures.set_composite(first, None));
        assert_eq!(signatures.get(first).unwrap().composite(), None);

        let mut foreign = SignatureArena::new();
        let mut foreign_id = None;
        for _ in 0..3 {
            foreign_id = Some(foreign.alloc(
                SignatureFlags::NONE,
                None,
                Vec::new(),
                None,
                Vec::new(),
                None,
                None,
                0,
            ));
        }
        let out_of_range = foreign_id.unwrap();
        assert!(!signatures.set_target_and_mapper(second, Some(out_of_range), Some(mapper)));
        assert!(!signatures.set_composite(
            first,
            Some(CompositeSignature::new(true, vec![out_of_range]))
        ));
    }

    #[test]
    fn type_predicate_keeps_absent_assertion_type() {
        let mut predicates = TypePredicateArena::new();
        let id = predicates.alloc(TypePredicateKind::AssertsIdentifier, 3, "condition", None);
        let predicate = predicates.get(id).unwrap();

        assert_eq!(id.get(), 1);
        assert_eq!(predicate.id(), id);
        assert_eq!(predicate.kind(), TypePredicateKind::AssertsIdentifier);
        assert_eq!(predicate.parameter_index(), 3);
        assert_eq!(predicate.parameter_name(), "condition");
        assert_eq!(predicate.type_id(), None);
    }

    #[test]
    fn index_info_matches_upstream_record_shape_and_lazy_symbol_slot() {
        let declaration = NodeRef::new(FileId::new(2), NodeId::new(5));
        let first_component = NodeRef::new(FileId::new(2), NodeId::new(8));
        let second_component = NodeRef::new(FileId::new(7), NodeId::new(1));
        let mut types = TypeArena::new();
        let key_type = types.alloc("PropertyKey");
        let value_type = types.alloc("Value");
        let mut symbols = SemanticSymbolArena::new();
        let index_symbol = symbols.alloc("__index");
        let mut infos = IndexInfoArena::new();
        let id = infos.alloc(
            key_type,
            value_type,
            true,
            Some(declaration),
            vec![first_component, second_component],
        );

        let info = infos.get(id).unwrap();
        assert_eq!(id.get(), 1);
        assert_eq!(info.id(), id);
        assert_eq!(info.key_type(), key_type);
        assert_eq!(info.value_type(), value_type);
        assert!(info.is_readonly());
        assert_eq!(info.declaration(), Some(declaration));
        assert_eq!(info.index_symbol(), None);
        assert_eq!(info.components(), [first_component, second_component]);

        assert!(infos.set_index_symbol(id, Some(index_symbol)));
        assert_eq!(infos.get(id).unwrap().index_symbol(), Some(index_symbol));
    }

    #[test]
    fn tuple_metadata_matches_create_tuple_target_type_fields() {
        let label = NodeRef::new(FileId::new(9), NodeId::new(12));
        let infos = vec![
            TupleElementInfo::new(ElementFlags::REQUIRED, Some(label)),
            TupleElementInfo::new(ElementFlags::OPTIONAL, None),
            TupleElementInfo::new(ElementFlags::VARIADIC, None),
        ];
        let tuple = TupleMetadata::new(infos.clone(), true);

        assert_eq!(tuple.element_infos(), infos);
        assert_eq!(
            tuple.element_flags(),
            [
                ElementFlags::REQUIRED,
                ElementFlags::OPTIONAL,
                ElementFlags::VARIADIC,
            ]
        );
        assert_eq!(tuple.min_length(), 2);
        assert_eq!(tuple.fixed_length(), 2);
        assert_eq!(
            tuple.combined_flags(),
            ElementFlags::REQUIRED | ElementFlags::OPTIONAL | ElementFlags::VARIADIC
        );
        assert!(tuple.is_readonly());
        assert_eq!(tuple.element_infos()[0].flags(), ElementFlags::REQUIRED);
        assert_eq!(tuple.element_infos()[0].labeled_declaration(), Some(label));

        let empty = TupleMetadata::new(Vec::new(), false);
        assert_eq!(empty.min_length(), 0);
        assert_eq!(empty.fixed_length(), 0);
        assert_eq!(empty.combined_flags(), ElementFlags::NONE);
        assert!(!empty.is_readonly());
    }
}
