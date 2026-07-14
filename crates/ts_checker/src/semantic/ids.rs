//! Program-local identities for the canonical semantic core.
//!
//! The numeric convention is pinned to typescript-go's checker counters at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`: zero is never a valid semantic
//! identity and the first arena allocation receives identity 1. These IDs are
//! meaningful only with the canonical semantic arenas that allocated them.
//!
//! This module deliberately has no conversion to the legacy checker IDs in
//! [`crate`]. Crossing that boundary would conflate two unrelated semantic
//! graphs merely because their counters happened to contain the same number.

use std::{marker::PhantomData, num::NonZeroU32};

macro_rules! define_semantic_id {
    ($name:ident, $description:literal) => {
        #[doc = $description]
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        #[repr(transparent)]
        pub struct $name(NonZeroU32);

        impl $name {
            /// Returns the upstream-compatible, one-based numeric identity.
            #[must_use]
            pub const fn get(self) -> u32 {
                self.0.get()
            }

            /// Returns the zero-based storage index used by the owning arena.
            #[must_use]
            pub const fn index(self) -> usize {
                (self.get() - 1) as usize
            }
        }

        impl ArenaId for $name {
            const ARENA_NAME: &'static str = stringify!($name);

            fn from_nonzero(raw: NonZeroU32) -> Self {
                Self(raw)
            }

            fn storage_index(self) -> usize {
                $name::index(self)
            }
        }
    };
}

pub(super) trait ArenaId: Copy {
    const ARENA_NAME: &'static str;

    fn from_nonzero(raw: NonZeroU32) -> Self;
    fn storage_index(self) -> usize;
}

define_semantic_id!(
    TypeId,
    "Identity of one canonical semantic type in a checker program."
);
define_semantic_id!(
    SignatureId,
    "Identity of one canonical call or construct signature."
);
define_semantic_id!(
    IndexInfoId,
    "Identity of one canonical index-signature information record."
);
define_semantic_id!(
    TypePredicateId,
    "Identity of one canonical type-predicate record."
);
define_semantic_id!(
    SemanticSymbolId,
    "Identity of one program-owned canonical semantic symbol."
);
define_semantic_id!(TypeMapperId, "Identity of one canonical type mapper.");

fn id_for_len<I: ArenaId>(len: usize) -> I {
    let zero_based = u32::try_from(len)
        .unwrap_or_else(|_| panic!("{} arena identity space exhausted", I::ARENA_NAME));
    let raw = zero_based
        .checked_add(1)
        .and_then(NonZeroU32::new)
        .unwrap_or_else(|| panic!("{} arena identity space exhausted", I::ARENA_NAME));
    I::from_nonzero(raw)
}

/// Dense storage whose key type cannot be exchanged with another semantic ID.
///
/// The ID is computed before the value is pushed, so exhaustion fails without
/// modifying the arena.
#[derive(Debug)]
pub(super) struct TypedArena<I, T> {
    entries: Vec<T>,
    id: PhantomData<fn() -> I>,
}

impl<I, T> Default for TypedArena<I, T> {
    fn default() -> Self {
        Self {
            entries: Vec::new(),
            id: PhantomData,
        }
    }
}

impl<I: ArenaId, T> TypedArena<I, T> {
    pub(super) fn alloc_with(&mut self, make_value: impl FnOnce(I) -> T) -> I {
        let id = id_for_len::<I>(self.entries.len());
        self.entries.push(make_value(id));
        id
    }

    pub(super) fn get(&self, id: I) -> Option<&T> {
        self.entries.get(id_index(id))
    }

    pub(super) fn get_mut(&mut self, id: I) -> Option<&mut T> {
        self.entries.get_mut(id_index(id))
    }

    pub(super) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(super) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub(super) fn iter(&self) -> impl ExactSizeIterator<Item = (I, &T)> {
        self.entries.iter().enumerate().map(|(index, value)| {
            let id = id_for_len::<I>(index);
            (id, value)
        })
    }
}

fn id_index<I: ArenaId>(id: I) -> usize {
    id.storage_index()
}

macro_rules! define_identity_arena {
    ($arena:ident, $id:ident, $description:literal) => {
        #[doc = $description]
        #[derive(Debug)]
        pub struct $arena<T> {
            entries: TypedArena<$id, T>,
        }

        impl<T> Default for $arena<T> {
            fn default() -> Self {
                Self {
                    entries: TypedArena::default(),
                }
            }
        }

        impl<T> $arena<T> {
            #[must_use]
            pub fn new() -> Self {
                Self::default()
            }

            /// Stores a payload and returns its canonical one-based identity.
            ///
            /// # Panics
            ///
            /// Panics before modifying the arena if all `u32` identities have
            /// already been allocated.
            pub fn alloc(&mut self, value: T) -> $id {
                self.entries.alloc_with(|_| value)
            }

            #[must_use]
            pub fn get(&self, id: $id) -> Option<&T> {
                self.entries.get(id)
            }

            #[must_use]
            pub fn len(&self) -> usize {
                self.entries.len()
            }

            #[must_use]
            pub fn is_empty(&self) -> bool {
                self.entries.is_empty()
            }

            #[must_use]
            pub fn iter(&self) -> impl ExactSizeIterator<Item = ($id, &T)> {
                self.entries.iter()
            }
        }
    };
}

define_identity_arena!(
    TypeArena,
    TypeId,
    "Typed storage for canonical type payloads. Full type payloads are ported separately."
);
define_identity_arena!(
    SemanticSymbolArena,
    SemanticSymbolId,
    "Typed storage for program-owned semantic symbol payloads."
);
define_identity_arena!(
    TypeMapperArena,
    TypeMapperId,
    "Typed storage for canonical mapper payloads. Mapper behavior is ported separately."
);

#[cfg(test)]
mod tests {
    use std::{mem::size_of, panic::catch_unwind};

    use super::{
        IndexInfoId, SemanticSymbolArena, SemanticSymbolId, SignatureId, TypeArena, TypeId,
        TypeMapperArena, TypeMapperId, TypePredicateId, id_for_len,
    };

    #[test]
    fn semantic_ids_are_nonzero_u32_values_with_option_niches() {
        assert_eq!(size_of::<TypeId>(), size_of::<u32>());
        assert_eq!(size_of::<Option<TypeId>>(), size_of::<u32>());
        assert_eq!(size_of::<SignatureId>(), size_of::<u32>());
        assert_eq!(size_of::<Option<SignatureId>>(), size_of::<u32>());
        assert_eq!(size_of::<IndexInfoId>(), size_of::<u32>());
        assert_eq!(size_of::<Option<IndexInfoId>>(), size_of::<u32>());
        assert_eq!(size_of::<TypePredicateId>(), size_of::<u32>());
        assert_eq!(size_of::<Option<TypePredicateId>>(), size_of::<u32>());
        assert_eq!(size_of::<SemanticSymbolId>(), size_of::<u32>());
        assert_eq!(size_of::<Option<SemanticSymbolId>>(), size_of::<u32>());
        assert_eq!(size_of::<TypeMapperId>(), size_of::<u32>());
        assert_eq!(size_of::<Option<TypeMapperId>>(), size_of::<u32>());
    }

    #[test]
    fn identity_arenas_allocate_one_based_dense_ids() {
        let mut types = TypeArena::new();
        let first_type = types.alloc("first");
        let second_type = types.alloc("second");
        assert_eq!((first_type.get(), first_type.index()), (1, 0));
        assert_eq!((second_type.get(), second_type.index()), (2, 1));
        assert_eq!(types.get(first_type), Some(&"first"));
        assert_eq!(
            types.iter().map(|(id, _)| id.get()).collect::<Vec<_>>(),
            [1, 2]
        );

        let mut symbols = SemanticSymbolArena::new();
        let symbol = symbols.alloc("value");
        assert_eq!(symbol.get(), 1);
        assert_eq!(symbols.get(symbol), Some(&"value"));

        let mut mappers = TypeMapperArena::new();
        let mapper = mappers.alloc("identity");
        assert_eq!(mapper.get(), 1);
        assert_eq!(mappers.get(mapper), Some(&"identity"));
    }

    #[test]
    fn semantic_id_allocation_fails_before_u32_wraparound() {
        let last = id_for_len::<TypeId>((u32::MAX - 1) as usize);
        assert_eq!(last.get(), u32::MAX);

        assert!(catch_unwind(|| id_for_len::<TypeId>(u32::MAX as usize)).is_err());
        assert!(catch_unwind(|| id_for_len::<SignatureId>(u32::MAX as usize)).is_err());
        assert!(catch_unwind(|| id_for_len::<IndexInfoId>(u32::MAX as usize)).is_err());
        assert!(catch_unwind(|| id_for_len::<TypePredicateId>(u32::MAX as usize)).is_err());
        assert!(catch_unwind(|| id_for_len::<SemanticSymbolId>(u32::MAX as usize)).is_err());
        assert!(catch_unwind(|| id_for_len::<TypeMapperId>(u32::MAX as usize)).is_err());
    }
}
