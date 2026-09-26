//! Go `internal/project/ownercache.go`.
//!
//! PORT: one thread (see `project/dirty/interfaces.rs`). The entry mutexes
//! are dropped; `collections.SyncMap` is a `RefCell<FxHashMap>`.

use crate::project::prelude::*;
use std::hash::Hash;

// Go: project/ownercache.go:9 ownerCacheEntry
// PORT: `value` is `None` until the first acquire sets it (Go holds the zero
// value there while the entry lock is held). Go `map[uint64]struct{}` is a
// set.
pub struct OwnerCacheEntry<V> {
    pub value: RefCell<Option<V>>,
    pub owners: RefCell<FxHashSet<u64>>,
}

// Go: project/ownercache.go:21 OwnerCache
// OwnerCache is like RefCountCache, but each entry tracks the set of its
// owners instead of a count. We use this to associate extended config cache
// entries with each snapshot that contains them, since the same config can
// be Acquired multiple times during config parsing while only appearing once in
// the ParsedCommandLine's list of extended files. When updating this code, check
// if the same changes should be made to RefCountCache as well.
pub struct OwnerCache<K, V, LoadArgs> {
    pub entries: RefCell<FxHashMap<K, Rc<OwnerCacheEntry<V>>>>,

    // PORT: Go nil func is `None`.
    pub is_expired: Option<Box<dyn Fn(&K, &V, &LoadArgs) -> bool>>,
    pub parse: Box<dyn Fn(&K, LoadArgs) -> V>,
}

// Go: project/ownercache.go:28 NewOwnerCache
pub fn new_owner_cache<K, V, LoadArgs>(
    parse: impl Fn(&K, LoadArgs) -> V + 'static,
    is_expired: Option<Box<dyn Fn(&K, &V, &LoadArgs) -> bool>>,
) -> Rc<OwnerCache<K, V, LoadArgs>> {
    Rc::new(OwnerCache {
        entries: RefCell::new(FxHashMap::default()),
        is_expired,
        parse: Box::new(parse),
    })
}

impl<K: Eq + Hash + Clone, V: Clone, LoadArgs> OwnerCache<K, V, LoadArgs> {
    // Go: project/ownercache.go:38 LoadAndAcquire
    pub fn load_and_acquire(&self, identity: K, owner: u64, load_args: LoadArgs) -> V {
        let (entry, loaded) = self.load_or_store_locked_entry(identity.clone());
        let expired = loaded && {
            match &self.is_expired {
                Some(is_expired) => {
                    // PORT: a loaded entry always has its value on one thread.
                    let value = entry
                        .value
                        .borrow()
                        .clone()
                        .expect("OwnerCache: entry value not set");
                    is_expired(&identity, &value, &load_args)
                }
                None => false,
            }
        };
        if !loaded || expired {
            let value = (self.parse)(&identity, load_args);
            *entry.value.borrow_mut() = Some(value);
        }
        entry.owners.borrow_mut().insert(owner);
        entry
            .value
            .borrow()
            .clone()
            .expect("OwnerCache: entry value not set")
    }

    // Go: project/ownercache.go:48 Acquire
    pub fn acquire(&self, identity: K, owner: u64, value: V) {
        let (entry, loaded) = self.load_or_store_locked_entry(identity);
        if !loaded {
            *entry.value.borrow_mut() = Some(value);
        }
        entry.owners.borrow_mut().insert(owner);
    }

    // Go: project/ownercache.go:60 AddOwner
    // AddOwner adds an owner to an existing live entry. The entry must exist
    // and have at least one current owner; callers must ensure the entry is
    // kept alive (e.g. via snapshot ref counting).
    pub fn add_owner(&self, identity: &K, owner: u64) {
        let entry = self.entries.borrow().get(identity).cloned();
        let Some(entry) = entry else {
            panic!("OwnerCache.AddOwner: entry not found");
        };
        if entry.owners.borrow().is_empty() {
            panic!("OwnerCache.AddOwner: entry has no owners");
        }
        entry.owners.borrow_mut().insert(owner);
    }

    // Go: project/ownercache.go:73 Has
    pub fn has(&self, identity: &K) -> bool {
        self.entries.borrow().contains_key(identity)
    }

    // Go: project/ownercache.go:78 Release
    pub fn release(&self, identity: &K, owner: u64) {
        let entry = self.entries.borrow().get(identity).cloned();
        let Some(entry) = entry else {
            return;
        };
        entry.owners.borrow_mut().remove(&owner);
        if entry.owners.borrow().is_empty() {
            self.entries.borrow_mut().remove(identity);
        }
    }

    // Go: project/ownercache.go:91 loadOrStoreLockedEntry
    pub fn load_or_store_locked_entry(&self, key: K) -> (Rc<OwnerCacheEntry<V>>, bool) {
        let entry = Rc::new(OwnerCacheEntry {
            value: RefCell::new(None),
            owners: RefCell::new(FxHashSet::default()),
        });
        // Go: c.entries.LoadOrStore(key, entry)
        let existing = self.entries.borrow().get(&key).cloned();
        if let Some(existing) = existing {
            if existing.owners.borrow().is_empty() {
                return self.load_or_store_locked_entry(key);
            }
            return (existing, true);
        }
        self.entries.borrow_mut().insert(key, entry.clone());
        (entry, false)
    }
}
