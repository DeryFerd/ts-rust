//! Program-local identities for the canonical semantic core.
//!
//! Local numeric identities follow typescript-go's checker counters at
//! `dc37b5249ab60e2bbce936f71b883e6c8136167e`: zero is never valid and the
//! first allocation receives identity 1. Every handle is additionally branded
//! with the globally unique [`SemanticStoreId`] of its owning store, so equal
//! local counters from different checker programs cannot alias.
//!
//! This module deliberately has no conversion to the legacy checker IDs in
//! [`crate`]. Crossing that boundary would conflate unrelated semantic graphs.

use std::{marker::PhantomData, num::NonZeroU32};

pub use ts_binder::{SemanticStoreId, SemanticSymbolId};

macro_rules! define_semantic_id {
    ($name:ident, $description:literal) => {
        #[doc = $description]
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name {
            store: SemanticStoreId,
            local: NonZeroU32,
        }

        impl $name {
            /// Returns the upstream-compatible, one-based local identity.
            #[must_use]
            pub const fn get(self) -> u32 {
                self.local.get()
            }

            /// Returns the zero-based storage index used by the owning store.
            #[must_use]
            pub const fn index(self) -> usize {
                (self.get() - 1) as usize
            }
        }

        impl ArenaId for $name {
            const ARENA_NAME: &'static str = stringify!($name);

            fn from_parts(store: SemanticStoreId, local: NonZeroU32) -> Self {
                Self { store, local }
            }

            fn store(self) -> SemanticStoreId {
                self.store
            }

            fn storage_index(self) -> usize {
                $name::index(self)
            }
        }
    };
}

pub(super) trait ArenaId: Copy {
    const ARENA_NAME: &'static str;

    fn from_parts(store: SemanticStoreId, local: NonZeroU32) -> Self;
    fn store(self) -> SemanticStoreId;
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
define_semantic_id!(TypeMapperId, "Identity of one canonical type mapper.");
define_semantic_id!(TypeAliasId, "Identity of one canonical type-alias record.");
define_semantic_id!(
    ConditionalRootId,
    "Identity of one shared canonical conditional-type root."
);

fn id_for_len<I: ArenaId>(store: SemanticStoreId, len: usize) -> I {
    let zero_based = u32::try_from(len)
        .unwrap_or_else(|_| panic!("{} arena identity space exhausted", I::ARENA_NAME));
    let local = zero_based
        .checked_add(1)
        .and_then(NonZeroU32::new)
        .unwrap_or_else(|| panic!("{} arena identity space exhausted", I::ARENA_NAME));
    I::from_parts(store, local)
}

/// Dense store-owned storage whose key type cannot be exchanged with another
/// semantic ID kind or another semantic store.
///
/// The ID is computed before the value is pushed, so exhaustion fails without
/// modifying the arena.
#[derive(Debug)]
pub(super) struct TypedArena<I, T> {
    store: SemanticStoreId,
    entries: Vec<T>,
    id: PhantomData<fn() -> I>,
}

impl<I: ArenaId, T> TypedArena<I, T> {
    pub(super) fn new(store: SemanticStoreId) -> Self {
        Self {
            store,
            entries: Vec::new(),
            id: PhantomData,
        }
    }

    pub(super) fn alloc_with(&mut self, make_value: impl FnOnce(I) -> T) -> I {
        let id = id_for_len::<I>(self.store, self.entries.len());
        self.entries.push(make_value(id));
        id
    }

    pub(super) fn try_reserve(&mut self, additional: usize) -> bool {
        self.entries
            .len()
            .checked_add(additional)
            .is_some_and(|len| u32::try_from(len).is_ok())
            && self.entries.try_reserve(additional).is_ok()
    }

    pub(super) fn get(&self, id: I) -> Option<&T> {
        (id.store() == self.store)
            .then(|| self.entries.get(id.storage_index()))
            .flatten()
    }

    pub(super) fn get_mut(&mut self, id: I) -> Option<&mut T> {
        (id.store() == self.store)
            .then(|| self.entries.get_mut(id.storage_index()))
            .flatten()
    }

    pub(super) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(super) fn iter(&self) -> impl ExactSizeIterator<Item = (I, &T)> {
        self.entries.iter().enumerate().map(|(index, value)| {
            let id = id_for_len::<I>(self.store, index);
            (id, value)
        })
    }
}

#[cfg(test)]
mod tests {
    use std::panic::catch_unwind;

    use ts_binder::SymbolStore;

    use super::{
        ConditionalRootId, IndexInfoId, SignatureId, TypeAliasId, TypeId, TypeMapperId,
        TypePredicateId, TypedArena, id_for_len,
    };

    #[test]
    fn local_identity_allocation_fails_before_wraparound() {
        let store = SymbolStore::new().id();
        let last = id_for_len::<TypeId>(store, (u32::MAX - 1) as usize);
        assert_eq!(last.get(), u32::MAX);
        assert!(catch_unwind(|| id_for_len::<TypeId>(store, u32::MAX as usize)).is_err());
        assert!(catch_unwind(|| id_for_len::<SignatureId>(store, u32::MAX as usize)).is_err());
        assert!(catch_unwind(|| id_for_len::<IndexInfoId>(store, u32::MAX as usize)).is_err());
        assert!(catch_unwind(|| id_for_len::<TypePredicateId>(store, u32::MAX as usize)).is_err());
        assert!(catch_unwind(|| id_for_len::<TypeMapperId>(store, u32::MAX as usize)).is_err());
        assert!(catch_unwind(|| id_for_len::<TypeAliasId>(store, u32::MAX as usize)).is_err());
        assert!(
            catch_unwind(|| id_for_len::<ConditionalRootId>(store, u32::MAX as usize)).is_err()
        );
    }

    #[test]
    fn typed_arenas_reject_equal_local_ids_from_another_store() {
        let first_store = SymbolStore::new().id();
        let second_store = SymbolStore::new().id();
        let mut first = TypedArena::<TypeId, _>::new(first_store);
        let mut second = TypedArena::<TypeId, _>::new(second_store);
        let first_id = first.alloc_with(|_| "first");
        let second_id = second.alloc_with(|_| "second");

        assert_eq!(first_id.get(), 1);
        assert_eq!(second_id.get(), 1);
        assert_ne!(first_id, second_id);
        assert_eq!(first.get(second_id), None);
        assert_eq!(second.get(first_id), None);
        assert_eq!(first.get(first_id), Some(&"first"));
        assert_eq!(second.get(second_id), Some(&"second"));
    }
}
