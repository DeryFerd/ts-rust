//! Go `internal/project/refcountcache.go`.
//!
//! PORT: one thread (see `project/dirty/interfaces.rs`). The entry mutexes
//! are dropped; `collections.SyncMap` is a `RefCell<FxHashMap>`. The "was
//! deleted while we were acquiring the lock" branches stay literal. On one
//! thread Deref removes an entry as soon as its count reaches zero, so they
//! only run with `DisableDeletion`.

use crate::project::prelude::*;
use std::cell::Cell;
use std::hash::Hash;

// Go: project/refcountcache.go:9 refCountCacheEntry
// PORT: `value` is `None` until the first Acquire sets it (Go holds the zero
// value there while the entry lock is held).
pub struct RefCountCacheEntry<V> {
    pub value: RefCell<Option<V>>,
    pub ref_count: Cell<i32>,
}

// Go: project/refcountcache.go:15 RefCountCacheOptions
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RefCountCacheOptions {
    // DisableDeletion prevents entries from being removed from the cache.
    // Used for testing.
    pub disable_deletion: bool,
}

// Go: project/refcountcache.go:21 RefCountCache
pub struct RefCountCache<K, V, AcquireArgs> {
    pub options: RefCountCacheOptions,
    pub entries: RefCell<FxHashMap<K, Rc<RefCountCacheEntry<V>>>>,

    pub parse: Box<dyn Fn(&K, AcquireArgs) -> V>,
}

// Go: project/refcountcache.go:28 NewRefCountCache
pub fn new_ref_count_cache<K, V, AcquireArgs>(
    options: RefCountCacheOptions,
    parse: impl Fn(&K, AcquireArgs) -> V + 'static,
) -> Rc<RefCountCache<K, V, AcquireArgs>> {
    Rc::new(RefCountCache {
        options,
        entries: RefCell::new(FxHashMap::default()),
        parse: Box::new(parse),
    })
}

impl<K: Eq + Hash + Clone, V: Clone, AcquireArgs> RefCountCache<K, V, AcquireArgs> {
    // Go: project/refcountcache.go:44 Acquire
    // Acquire retrieves or creates a cache entry for the given identity and hash.
    // If an entry exists with matching identity and hash, its refcount is incremented
    // and the cached value is returned. Otherwise, parse() is called to create the
    // value, which is stored and returned with refcount 1.
    //
    // The caller is responsible for calling Deref when done with the value.
    pub fn acquire(&self, identity: K, acquire_args: AcquireArgs) -> V {
        let (entry, loaded) = self.load_or_store_new_locked_entry(identity.clone());
        if !loaded {
            // New entry - parse the value
            let value = (self.parse)(&identity, acquire_args);
            *entry.value.borrow_mut() = Some(value);
            return entry
                .value
                .borrow()
                .clone()
                .expect("RefCountCache: value set above");
        }
        // PORT: on one thread a loaded entry always has its value (Go waits on
        // the entry lock while the first Acquire parses).
        entry
            .value
            .borrow()
            .clone()
            .expect("RefCountCache: entry value not set")
    }

    // Go: project/refcountcache.go:55 Has
    pub fn has(&self, identity: &K) -> bool {
        self.entries.borrow().contains_key(identity)
    }

    // Go: project/refcountcache.go:62 Ref
    // Ref increments the reference count for an existing entry.
    // Panics if the entry does not exist.
    pub fn ref_(&self, identity: &K) {
        let entry = self.entries.borrow().get(identity).cloned();
        let Some(entry) = entry else {
            panic!("cache entry not found");
        };
        if entry.ref_count.get() <= 0 && !self.options.disable_deletion {
            // Entry was deleted while we were acquiring the lock
            let (new_entry, _) = self.load_or_store_new_locked_entry(identity.clone());
            *new_entry.value.borrow_mut() = entry.value.borrow().clone();
            return;
        }
        entry.ref_count.set(entry.ref_count.get() + 1);
    }

    // Go: project/refcountcache.go:82 Deref
    // Deref decrements the reference count for an entry.
    // When the refcount reaches zero, the entry is removed from the cache
    // (unless DisableDeletion is set).
    pub fn deref(&self, identity: &K) {
        let entry = self.entries.borrow().get(identity).cloned();
        let Some(entry) = entry else {
            return;
        };
        entry.ref_count.set(entry.ref_count.get() - 1);
        if entry.ref_count.get() <= 0 && !self.options.disable_deletion {
            self.entries.borrow_mut().remove(identity);
        }
    }

    // Go: project/refcountcache.go:98 loadOrStoreNewLockedEntry
    // loadOrStoreNewLockedEntry loads an existing entry or creates a new one.
    // The returned entry's mutex is locked and its refCount is incremented
    // (or initialized to 1 in the case of a new entry).
    pub fn load_or_store_new_locked_entry(&self, key: K) -> (Rc<RefCountCacheEntry<V>>, bool) {
        let entry = Rc::new(RefCountCacheEntry {
            value: RefCell::new(None),
            ref_count: Cell::new(1),
        });
        // Go: c.entries.LoadOrStore(key, entry)
        let existing = self.entries.borrow().get(&key).cloned();
        if let Some(existing) = existing {
            if existing.ref_count.get() <= 0 && !self.options.disable_deletion {
                // Existing entry was deleted while we were acquiring the lock
                return self.load_or_store_new_locked_entry(key);
            }
            existing.ref_count.set(existing.ref_count.get() + 1);
            return (existing, true);
        }
        self.entries.borrow_mut().insert(key, entry.clone());
        (entry, false)
    }
}
