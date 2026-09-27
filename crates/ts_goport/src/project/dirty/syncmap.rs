//! Go `internal/project/dirty/syncmap.go`.
//!
//! PORT: one thread (see interfaces.rs). The entry mutexes are dropped.
//! The `proxyFor` logic stays literal: it also runs without a race, when two
//! entries loaded for the same key are both changed.

use crate::project::dirty::prelude::*;
use std::hash::Hash;
use std::rc::Weak;

const SYNC_MAP_DROPPED: &str = "dirty: SyncMap dropped while one of its entries is in use";

// Go: project/dirty/syncmap.go:10 lockedEntry
pub struct LockedEntry<K, V> {
    pub e: Rc<SyncMapEntry<K, V>>,
}

impl<K: Eq + Hash + Clone, V: Cloneable + Clone> LockedEntry<K, V> {
    // Go: project/dirty/syncmap.go:14 Value
    pub fn value(&self) -> Option<V> {
        self.e.value_locked()
    }

    // Go: project/dirty/syncmap.go:18 Original
    pub fn original(&self) -> Option<V> {
        self.e.map_entry.borrow().original.clone()
    }

    // Go: project/dirty/syncmap.go:22 Dirty
    pub fn dirty(&self) -> bool {
        self.e.map_entry.borrow().dirty
    }

    // Go: project/dirty/syncmap.go:26 Change
    pub fn change(&self, apply: &mut dyn FnMut(&V)) {
        self.e.change_locked(apply);
    }

    // Go: project/dirty/syncmap.go:30 ChangeIf
    pub fn change_if(
        &self,
        cond: &mut dyn FnMut(Option<&V>) -> bool,
        apply: &mut dyn FnMut(&V),
    ) -> bool {
        if cond(self.e.value_locked().as_ref()) {
            self.e.change_locked(apply);
            return true;
        }
        false
    }

    // Go: project/dirty/syncmap.go:38 Delete
    pub fn delete(&self) {
        self.e.delete_locked();
    }

    // Go: project/dirty/syncmap.go:42 Locked
    pub fn locked(&self, fn_: &mut dyn FnMut(&dyn Value<V>)) {
        fn_(self);
    }
}

impl<K: Eq + Hash + Clone, V: Cloneable + Clone> Value<V> for LockedEntry<K, V> {
    fn value(&self) -> Option<V> {
        LockedEntry::value(self)
    }

    fn original(&self) -> Option<V> {
        LockedEntry::original(self)
    }

    fn dirty(&self) -> bool {
        LockedEntry::dirty(self)
    }

    fn change(&self, apply: &mut dyn FnMut(&V)) {
        LockedEntry::change(self, apply)
    }

    fn change_if(
        &self,
        cond: &mut dyn FnMut(Option<&V>) -> bool,
        apply: &mut dyn FnMut(&V),
    ) -> bool {
        LockedEntry::change_if(self, cond, apply)
    }

    fn delete(&self) {
        LockedEntry::delete(self)
    }

    fn locked(&self, fn_: &mut dyn FnMut(&dyn Value<V>)) {
        LockedEntry::locked(self, fn_)
    }
}

// Go: project/dirty/syncmap.go:46 SyncMapEntry
// PORT: Go `m *SyncMap` is a `Weak` (the map holds its dirty entries). Go
// stores the entry pointer itself in `m.dirty`, so the entry keeps a `Weak`
// to itself (`this`). `mu` is dropped (one thread). The embedded Go
// `mapEntry` is the `map_entry` field.
pub struct SyncMapEntry<K, V> {
    pub m: Weak<SyncMap<K, V>>,
    pub map_entry: RefCell<MapEntryImpl<K, V>>,
    // proxyFor is set when this entry loses a race to become the dirty entry
    // for a value. Since two goroutines hold a reference to two entries that
    // may try to mutate the same underlying value, all mutations are routed
    // through the one that actually exists in the dirty map.
    pub proxy_for: RefCell<Option<Rc<SyncMapEntry<K, V>>>>,
    this: Weak<SyncMapEntry<K, V>>,
}

// PORT: Go `&SyncMapEntry[K, V]{m: m, mapEntry: ...}`.
fn new_sync_map_entry<K, V>(
    m: &Weak<SyncMap<K, V>>,
    map_entry: MapEntryImpl<K, V>,
) -> Rc<SyncMapEntry<K, V>> {
    Rc::new_cyclic(|this| SyncMapEntry {
        m: m.clone(),
        map_entry: RefCell::new(map_entry),
        proxy_for: RefCell::new(None),
        this: this.clone(),
    })
}

impl<K: Eq + Hash + Clone, V: Cloneable + Clone> SyncMapEntry<K, V> {
    fn proxy(&self) -> Option<Rc<SyncMapEntry<K, V>>> {
        self.proxy_for.borrow().clone()
    }

    fn this_rc(&self) -> Rc<SyncMapEntry<K, V>> {
        self.this.upgrade().expect(SYNC_MAP_DROPPED)
    }

    // Go: project/dirty/entry.go:11 Key (promoted from mapEntry)
    pub fn key(&self) -> K {
        self.map_entry.borrow().key()
    }

    // Go: project/dirty/entry.go:15 Original (promoted from mapEntry)
    pub fn original(&self) -> Option<V> {
        self.map_entry.borrow().original()
    }

    // Go: project/dirty/syncmap.go:57 Value
    pub fn value(&self) -> Option<V> {
        if let Some(proxy_for) = self.proxy() {
            return proxy_for.value();
        }
        self.value_locked()
    }

    // Go: project/dirty/syncmap.go:66 valueLocked
    pub fn value_locked(&self) -> Option<V> {
        let e = self.map_entry.borrow();
        if e.delete {
            return None;
        }
        e.value.clone()
    }

    // Go: project/dirty/syncmap.go:74 Dirty
    pub fn dirty(&self) -> bool {
        if let Some(proxy_for) = self.proxy() {
            return proxy_for.dirty();
        }
        self.map_entry.borrow().dirty
    }

    // Go: project/dirty/syncmap.go:83 Locked
    pub fn locked(&self, fn_: &mut dyn FnMut(&dyn Value<V>)) {
        if let Some(proxy_for) = self.proxy() {
            proxy_for.locked(fn_);
            return;
        }
        fn_(&LockedEntry { e: self.this_rc() });
    }

    // Go: project/dirty/syncmap.go:93 Change
    pub fn change(&self, apply: &mut dyn FnMut(&V)) {
        if let Some(proxy_for) = self.proxy() {
            proxy_for.change(apply);
            return;
        }
        self.change_locked(apply);
    }

    // Go: project/dirty/syncmap.go:103 changeLocked
    pub fn change_locked(&self, apply: &mut dyn FnMut(&V)) {
        if self.map_entry.borrow().dirty {
            // PORT: no borrow is held while `apply` runs.
            let value = self.map_entry.borrow().value.clone();
            apply(
                value
                    .as_ref()
                    .expect("nil pointer dereference: SyncMapEntry.value"),
            );
            return;
        }

        let m = self.m.upgrade().expect(SYNC_MAP_DROPPED);
        let (entry, loaded) = m.dirty_load_or_store(self.key(), self.this_rc());
        // Go: `if loaded { entry.mu.Lock() }` (PORT: no lock).
        if !entry.map_entry.borrow().dirty {
            // PORT: Go calls Clone on a nil value; that dereferences nil.
            let value = entry.map_entry.borrow().value.clone();
            let cloned = value
                .as_ref()
                .expect("nil pointer dereference: SyncMapEntry.value")
                .clone_();
            let mut e = entry.map_entry.borrow_mut();
            e.value = Some(cloned);
            e.dirty = true;
        }
        if loaded {
            *self.proxy_for.borrow_mut() = Some(entry.clone());
            let (value, delete) = {
                let e = entry.map_entry.borrow();
                (e.value.clone(), e.delete)
            };
            let mut me = self.map_entry.borrow_mut();
            me.value = value;
            me.dirty = true;
            me.delete = delete;
        }
        let value = entry.map_entry.borrow().value.clone();
        apply(
            value
                .as_ref()
                .expect("nil pointer dereference: SyncMapEntry.value"),
        );
    }

    // Go: project/dirty/syncmap.go:127 ChangeIf
    pub fn change_if(
        &self,
        cond: &mut dyn FnMut(Option<&V>) -> bool,
        apply: &mut dyn FnMut(&V),
    ) -> bool {
        if let Some(proxy_for) = self.proxy() {
            return proxy_for.change_if(cond, apply);
        }

        // Go: cond(e.value) reads the field, not Value().
        let value = self.map_entry.borrow().value.clone();
        if cond(value.as_ref()) {
            self.change_locked(apply);
            return true;
        }
        false
    }

    // Go: project/dirty/syncmap.go:141 Delete
    pub fn delete(&self) {
        if let Some(proxy_for) = self.proxy() {
            proxy_for.delete();
            return;
        }

        if self.map_entry.borrow().dirty {
            self.map_entry.borrow_mut().delete = true;
            return;
        }
        let m = self.m.upgrade().expect(SYNC_MAP_DROPPED);
        let (entry, loaded) = m.dirty_load_or_store(self.key(), self.this_rc());
        if loaded {
            // Go: entry.mu.Lock() (PORT: no lock).
            self.map_entry.borrow_mut().delete = true;
        } else {
            entry.map_entry.borrow_mut().delete = true;
        }
    }

    // Go: project/dirty/syncmap.go:163 deleteLocked
    pub fn delete_locked(&self) {
        if self.map_entry.borrow().dirty {
            self.map_entry.borrow_mut().delete = true;
            return;
        }
        let m = self.m.upgrade().expect(SYNC_MAP_DROPPED);
        let (entry, loaded) = m.dirty_load_or_store(self.key(), self.this_rc());
        if loaded {
            // Go: entry.mu.Lock() (PORT: no lock).
            *self.proxy_for.borrow_mut() = Some(entry.clone());
            let (value, dirty) = {
                let e = entry.map_entry.borrow();
                (e.value.clone(), e.dirty)
            };
            let mut me = self.map_entry.borrow_mut();
            me.value = value;
            me.delete = true;
            me.dirty = dirty;
        }
        entry.map_entry.borrow_mut().delete = true;
    }

    // Go: project/dirty/syncmap.go:180 DeleteIf
    pub fn delete_if(&self, cond: &mut dyn FnMut(Option<&V>) -> bool) {
        if let Some(proxy_for) = self.proxy() {
            proxy_for.delete_if(cond);
            return;
        }
        // Go: cond(e.value) reads the field, not Value().
        let value = self.map_entry.borrow().value.clone();
        if cond(value.as_ref()) {
            self.delete_locked();
        }
    }
}

impl<K: Eq + Hash + Clone, V: Cloneable + Clone> Value<V> for SyncMapEntry<K, V> {
    fn value(&self) -> Option<V> {
        SyncMapEntry::value(self)
    }

    fn original(&self) -> Option<V> {
        SyncMapEntry::original(self)
    }

    fn dirty(&self) -> bool {
        SyncMapEntry::dirty(self)
    }

    fn change(&self, apply: &mut dyn FnMut(&V)) {
        SyncMapEntry::change(self, apply)
    }

    fn change_if(
        &self,
        cond: &mut dyn FnMut(Option<&V>) -> bool,
        apply: &mut dyn FnMut(&V),
    ) -> bool {
        SyncMapEntry::change_if(self, cond, apply)
    }

    fn delete(&self) {
        SyncMapEntry::delete(self)
    }

    fn locked(&self, fn_: &mut dyn FnMut(&dyn Value<V>)) {
        SyncMapEntry::locked(self, fn_)
    }
}

// Go: project/dirty/syncmap.go:192 SyncMap
// PORT: Go `dirty collections.SyncMap` is a `RefCell<IndexMap>` (insertion
// order; PORT: Go map order is random). `base` is never written. It is an
// `Rc` because a Go map is a reference: the base map is shared with the
// value it came from, and `finalize_shared` gives it back unchanged. `this`
// is the Go pointer that new entries point back to.
pub struct SyncMap<K, V> {
    pub base: Rc<FxHashMap<K, V>>,
    pub dirty: RefCell<IndexMap<K, Rc<SyncMapEntry<K, V>>>>,
    this: Weak<SyncMap<K, V>>,
}

// Go: project/dirty/syncmap.go:197 NewSyncMap
// PORT: takes an owned base map. `new_sync_map_shared` takes a shared one.
pub fn new_sync_map<K, V>(base: FxHashMap<K, V>) -> Rc<SyncMap<K, V>> {
    new_sync_map_shared(Rc::new(base))
}

// Go: project/dirty/syncmap.go:197 NewSyncMap
// PORT: Go keeps the caller's map without a copy. This form does the same
// with a shared `Rc` map.
pub fn new_sync_map_shared<K, V>(base: Rc<FxHashMap<K, V>>) -> Rc<SyncMap<K, V>> {
    Rc::new_cyclic(|this| SyncMap {
        base,
        dirty: RefCell::new(IndexMap::new()),
        this: this.clone(),
    })
}

impl<K: Eq + Hash + Clone, V: Cloneable + Clone> SyncMap<K, V> {
    // PORT: Go `m.dirty.LoadOrStore(key, value)` (collections.SyncMap).
    fn dirty_load_or_store(
        &self,
        key: K,
        value: Rc<SyncMapEntry<K, V>>,
    ) -> (Rc<SyncMapEntry<K, V>>, bool) {
        let mut dirty = self.dirty.borrow_mut();
        if let Some(existing) = dirty.get(&key) {
            return (existing.clone(), true);
        }
        dirty.insert(key, value.clone());
        (value, false)
    }

    // Go: project/dirty/syncmap.go:204 Load
    pub fn load(&self, key: &K) -> (Option<Rc<SyncMapEntry<K, V>>>, bool) {
        let entry = self.dirty.borrow().get(key).cloned();
        if let Some(entry) = entry {
            // Go: entry.mu.Lock() (PORT: no lock).
            if entry.map_entry.borrow().delete {
                return (None, false);
            }
            return (Some(entry), true);
        }
        if let Some(val) = self.base.get(key) {
            return (
                Some(new_sync_map_entry(
                    &self.this,
                    MapEntryImpl {
                        key: key.clone(),
                        original: Some(val.clone()),
                        value: Some(val.clone()),
                        dirty: false,
                        delete: false,
                    },
                )),
                true,
            );
        }
        (None, false)
    }

    // Go: project/dirty/syncmap.go:228 LoadOrStore
    pub fn load_or_store(&self, key: K, value: V) -> (Option<Rc<SyncMapEntry<K, V>>>, bool) {
        // Check for existence in the base map first so the sync map access is atomic.
        if let Some(base_value) = self.base.get(&key) {
            let dirty = self.dirty.borrow().get(&key).cloned();
            if let Some(dirty) = dirty {
                // Go: dirty.mu.Lock() (PORT: no lock).
                if dirty.map_entry.borrow().delete {
                    return (None, false);
                }
                return (Some(dirty), true);
            }
            return (
                Some(new_sync_map_entry(
                    &self.this,
                    MapEntryImpl {
                        key,
                        original: Some(base_value.clone()),
                        value: Some(base_value.clone()),
                        dirty: false,
                        delete: false,
                    },
                )),
                true,
            );
        }
        let new_entry = new_sync_map_entry(
            &self.this,
            MapEntryImpl {
                key: key.clone(),
                original: None,
                value: Some(value),
                dirty: true,
                delete: false,
            },
        );
        let (entry, loaded) = self.dirty_load_or_store(key, new_entry);
        if loaded {
            // Go: entry.mu.Lock() (PORT: no lock).
            if entry.map_entry.borrow().delete {
                return (None, false);
            }
        }
        (Some(entry), loaded)
    }

    // Go: project/dirty/syncmap.go:268 Delete
    pub fn delete(&self, key: &K) {
        let new_entry = new_sync_map_entry(
            &self.this,
            MapEntryImpl {
                key: key.clone(),
                original: self.base.get(key).cloned(),
                value: None,
                dirty: false,
                delete: true,
            },
        );
        let (entry, loaded) = self.dirty_load_or_store(key.clone(), new_entry);
        if loaded {
            entry.delete();
        }
    }

    // Go: project/dirty/syncmap.go:282 Range
    // PORT: the entries are copied out first so `fn_` can change the map
    // (Go sync.Map.Range may or may not see entries stored meanwhile). Go
    // keeps going with the base map after `fn_` stops the dirty Range; the
    // port does the same.
    pub fn range(&self, fn_: &mut dyn FnMut(&Rc<SyncMapEntry<K, V>>) -> bool) {
        let mut seen_in_dirty: FxHashSet<K> = FxHashSet::default();
        let dirty: Vec<(K, Rc<SyncMapEntry<K, V>>)> = self
            .dirty
            .borrow()
            .iter()
            .map(|(k, e)| (k.clone(), e.clone()))
            .collect();
        for (key, entry) in &dirty {
            seen_in_dirty.insert(key.clone());
            let deleted = entry.map_entry.borrow().delete;
            if !deleted && !fn_(entry) {
                break;
            }
        }
        for (key, value) in self.base.iter() {
            if seen_in_dirty.contains(key) {
                continue; // already processed in dirty entries
            }
            let entry = new_sync_map_entry(
                &self.this,
                MapEntryImpl {
                    key: key.clone(),
                    original: Some(value.clone()),
                    value: Some(value.clone()),
                    dirty: false,
                    delete: false,
                },
            );
            if !fn_(&entry) {
                break;
            }
        }
    }

    // Go: project/dirty/syncmap.go:315 finalize
    // PORT: returns an owned map for callers that keep a plain `FxHashMap`.
    // When nothing changed, that is a copy of the base map.
    // `finalize_shared` returns the base map itself, as Go does.
    pub fn finalize(&self, hooks: FinalizationHooks<'_, K, V>) -> (FxHashMap<K, V>, bool) {
        let (result, changed) = self.finalize_shared(hooks);
        (Rc::unwrap_or_clone(result), changed)
    }

    // Go: project/dirty/syncmap.go:315 finalize
    // PORT: when nothing changed, the result is the base map (an `Rc` clone),
    // as in Go. When an entry changed, it is a new map. No borrow is held
    // while a hook runs.
    pub fn finalize_shared(
        &self,
        mut hooks: FinalizationHooks<'_, K, V>,
    ) -> (Rc<FxHashMap<K, V>>, bool) {
        let mut changed = false;
        let mut result: Option<FxHashMap<K, V>> = None;

        let dirty: Vec<(K, Rc<SyncMapEntry<K, V>>)> = self
            .dirty
            .borrow()
            .iter()
            .map(|(k, e)| (k.clone(), e.clone()))
            .collect();
        for (key, entry) in dirty {
            // Go: entry.mu.Lock() (PORT: no lock).
            let (delete, dirty, original, value) = {
                let e = entry.map_entry.borrow();
                (e.delete, e.dirty, e.original.clone(), e.value.clone())
            };
            if delete {
                // Go: ensureCloned()
                if !changed {
                    result = Some((*self.base).clone());
                    changed = true;
                }
                if let Some(on_delete) = hooks.on_delete.as_mut() {
                    on_delete(&key, value.as_ref());
                }
                result.as_mut().expect("cloned above").remove(&key);
            } else if dirty {
                // Go: ensureCloned()
                if !changed {
                    result = Some((*self.base).clone());
                    changed = true;
                }
                if hooks.on_change.is_some() || hooks.on_add.is_some() {
                    if self.base.contains_key(&key) {
                        if let Some(on_change) = hooks.on_change.as_mut() {
                            on_change(&key, original.as_ref(), value.as_ref());
                        }
                    } else if let Some(on_add) = hooks.on_add.as_mut() {
                        on_add(&key, value.as_ref());
                    }
                }
                // PORT: a dirty entry that is not deleted holds a value; Go
                // would store nil.
                result.as_mut().expect("cloned above").insert(
                    key,
                    value.expect("nil pointer dereference: SyncMapEntry.value"),
                );
            }
        }
        match result {
            Some(result) => (Rc::new(result), changed),
            None => (self.base.clone(), changed), // no changes, return base map
        }
    }

    // Go: project/dirty/syncmap.go:356 Finalize
    // PORT: `_exported`, because Go also has the unexported `finalize`.
    pub fn finalize_exported(&self) -> (FxHashMap<K, V>, bool) {
        self.finalize(FinalizationHooks::default())
    }

    // Go: project/dirty/syncmap.go:360 FinalizeWith
    pub fn finalize_with(&self, hooks: FinalizationHooks<'_, K, V>) -> (FxHashMap<K, V>, bool) {
        self.finalize(hooks)
    }
}

// Go: project/dirty/syncmap.go:309 FinalizationHooks
// PORT: Go func fields; nil is `None`. Values are `Option<&V>` because Go can
// pass the zero value (nil).
pub struct FinalizationHooks<'a, K, V> {
    pub on_delete: Option<&'a mut dyn FnMut(&K, Option<&V>)>,
    pub on_change: Option<&'a mut dyn FnMut(&K, Option<&V>, Option<&V>)>,
    pub on_add: Option<&'a mut dyn FnMut(&K, Option<&V>)>,
}

impl<K, V> Default for FinalizationHooks<'_, K, V> {
    fn default() -> Self {
        FinalizationHooks {
            on_delete: None,
            on_change: None,
            on_add: None,
        }
    }
}
