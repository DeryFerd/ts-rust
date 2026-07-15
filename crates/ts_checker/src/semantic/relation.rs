//! Exact relation flags and cache state from the pinned checker.
//!
//! This module ports the dependency-closed state substrate from
//! `internal/checker/relater.go` at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`. It intentionally does not
//! implement `getRelationKey`, recursion identities, simple relations, or
//! structural relation algorithms. Callers must supply the canonical
//! [`CacheHashKey`] produced by that later work.

use std::{collections::HashMap, ops};

use super::type_records::CacheHashKey;

const RELATION_COMPARISON_BUDGET_BASE: isize = 16_000_000;
const RELATION_COMPARISON_BUDGET_DIVISOR: isize = 8;

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

    use super::{
        ExpandingFlags, IntersectionState, MinArgumentCountFlags, RecursionFlags, Relation,
        RelationCacheSnapshot, RelationCaches, RelationComparisonResult, RelationKind,
        RelationStateSnapshot, SignatureCheckMode, comparison_budget_for_size,
    };
    use crate::semantic::CacheHashKey;

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
