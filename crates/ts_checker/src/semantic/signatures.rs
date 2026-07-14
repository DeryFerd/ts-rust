//! Semantic enums and flags used by canonical signature, tuple, and index records.
//!
//! Values are pinned to typescript-go `internal/checker/types.go` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`.

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
