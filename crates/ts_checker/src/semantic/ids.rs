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

use std::{marker::PhantomData, num::NonZeroU32, num::NonZeroU64};

/// Opaque process-local identity for one canonical semantic store.
///
/// Moving a store preserves its identity. A newly constructed store always
/// receives a different identity.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SemanticStoreId(NonZeroU64);

impl std::fmt::Debug for SemanticStoreId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("SemanticStoreId")
    }
}

static LAST_SEMANTIC_STORE_ID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn allocate_semantic_store_id_from(counter: &std::sync::atomic::AtomicU64) -> SemanticStoreId {
    let previous = counter
        .fetch_update(
            std::sync::atomic::Ordering::Relaxed,
            std::sync::atomic::Ordering::Relaxed,
            |current| current.checked_add(1),
        )
        .unwrap_or_else(|_| panic!("semantic store identity space exhausted"));
    SemanticStoreId(
        NonZeroU64::new(previous + 1).expect("allocated semantic store identities are nonzero"),
    )
}

pub(super) fn allocate_semantic_store_id() -> SemanticStoreId {
    allocate_semantic_store_id_from(&LAST_SEMANTIC_STORE_ID)
}

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
define_semantic_id!(
    SemanticSymbolId,
    "Identity of one program-owned canonical semantic symbol."
);
define_semantic_id!(TypeMapperId, "Identity of one canonical type mapper.");

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
    use std::{panic::catch_unwind, sync::atomic::AtomicU64};

    use super::{
        IndexInfoId, SemanticSymbolId, SignatureId, TypeId, TypeMapperId, TypePredicateId,
        TypedArena, allocate_semantic_store_id, allocate_semantic_store_id_from, id_for_len,
    };

    #[test]
    fn store_and_local_identity_allocation_fail_before_wraparound() {
        let store_counter = AtomicU64::new(u64::MAX - 1);
        let last_store = allocate_semantic_store_id_from(&store_counter);
        assert_eq!(format!("{last_store:?}"), "SemanticStoreId");
        assert!(catch_unwind(|| allocate_semantic_store_id_from(&store_counter)).is_err());
        assert!(catch_unwind(|| allocate_semantic_store_id_from(&store_counter)).is_err());

        let store = allocate_semantic_store_id();
        let last = id_for_len::<TypeId>(store, (u32::MAX - 1) as usize);
        assert_eq!(last.get(), u32::MAX);
        assert!(catch_unwind(|| id_for_len::<TypeId>(store, u32::MAX as usize)).is_err());
        assert!(catch_unwind(|| id_for_len::<SignatureId>(store, u32::MAX as usize)).is_err());
        assert!(catch_unwind(|| id_for_len::<IndexInfoId>(store, u32::MAX as usize)).is_err());
        assert!(catch_unwind(|| id_for_len::<TypePredicateId>(store, u32::MAX as usize)).is_err());
        assert!(catch_unwind(|| id_for_len::<SemanticSymbolId>(store, u32::MAX as usize)).is_err());
        assert!(catch_unwind(|| id_for_len::<TypeMapperId>(store, u32::MAX as usize)).is_err());
    }

    #[test]
    fn typed_arenas_reject_equal_local_ids_from_another_store() {
        let first_store = allocate_semantic_store_id();
        let second_store = allocate_semantic_store_id();
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
