//! Go `internal/project/dirty/map.go`.

use crate::project::dirty::prelude::*;
use std::hash::Hash;
use std::rc::Weak;

const MAP_DROPPED: &str = "dirty: Map dropped while one of its entries is in use";

// Go: project/dirty/map.go:5 MapEntry
// PORT: Go `m *Map` is a `Weak` (the map holds its dirty entries, so a
// strong pointer would be a cycle). Go stores the entry pointer itself in
// `m.dirty`, so the entry keeps a `Weak` to itself (`this`). The embedded Go
// `mapEntry` is the `map_entry` field.
pub struct MapEntry<K, V> {
    pub m: Weak<Map<K, V>>,
    pub map_entry: RefCell<MapEntryImpl<K, V>>,
    this: Weak<MapEntry<K, V>>,
}

// PORT: Go `&MapEntry[K, V]{m: m, mapEntry: ...}`.
fn new_map_entry<K, V>(m: &Weak<Map<K, V>>, map_entry: MapEntryImpl<K, V>) -> Rc<MapEntry<K, V>> {
    Rc::new_cyclic(|this| MapEntry {
        m: m.clone(),
        map_entry: RefCell::new(map_entry),
        this: this.clone(),
    })
}

impl<K: Eq + Hash + Clone, V: Cloneable + Clone> MapEntry<K, V> {
    // Go: project/dirty/entry.go:11 Key (promoted from mapEntry)
    pub fn key(&self) -> K {
        self.map_entry.borrow().key()
    }

    // Go: project/dirty/entry.go:15 Original (promoted from mapEntry)
    pub fn original(&self) -> Option<V> {
        self.map_entry.borrow().original()
    }

    // Go: project/dirty/entry.go:19 Value (promoted from mapEntry)
    pub fn value(&self) -> Option<V> {
        self.map_entry.borrow().value()
    }

    // Go: project/dirty/entry.go:27 Dirty (promoted from mapEntry)
    pub fn dirty(&self) -> bool {
        self.map_entry.borrow().dirty()
    }

    // Go: project/dirty/map.go:10 Change
    pub fn change(&self, apply: &mut dyn FnMut(&V)) {
        if self.map_entry.borrow().delete {
            panic!("tried to change a deleted entry");
        }
        if !self.map_entry.borrow().dirty {
            // PORT: Go calls Clone on a nil value; that dereferences nil.
            let value = self.map_entry.borrow().value.clone();
            let cloned = value
                .as_ref()
                .expect("nil pointer dereference: MapEntry.value")
                .clone_();
            {
                let mut e = self.map_entry.borrow_mut();
                e.value = Some(cloned);
                e.dirty = true;
            }
            let m = self.m.upgrade().expect(MAP_DROPPED);
            m.dirty
                .borrow_mut()
                .insert(self.key(), self.this.upgrade().expect(MAP_DROPPED));
        }
        // PORT: no borrow is held while `apply` runs.
        let value = self.map_entry.borrow().value.clone();
        apply(
            value
                .as_ref()
                .expect("nil pointer dereference: MapEntry.value"),
        );
    }

    // Go: project/dirty/map.go:22 Replace
    pub fn replace(&self, new_value: V) {
        if self.map_entry.borrow().delete {
            panic!("tried to change a deleted entry");
        }
        if !self.map_entry.borrow().dirty {
            self.map_entry.borrow_mut().dirty = true;
            let m = self.m.upgrade().expect(MAP_DROPPED);
            m.dirty
                .borrow_mut()
                .insert(self.key(), self.this.upgrade().expect(MAP_DROPPED));
        }
        self.map_entry.borrow_mut().value = Some(new_value);
    }

    // Go: project/dirty/map.go:33 ChangeIf
    pub fn change_if(
        &self,
        cond: &mut dyn FnMut(Option<&V>) -> bool,
        apply: &mut dyn FnMut(&V),
    ) -> bool {
        if cond(self.value().as_ref()) {
            self.change(apply);
            return true;
        }
        false
    }

    // Go: project/dirty/map.go:41 Delete
    pub fn delete(&self) {
        if !self.map_entry.borrow().dirty {
            let m = self.m.upgrade().expect(MAP_DROPPED);
            m.dirty
                .borrow_mut()
                .insert(self.key(), self.this.upgrade().expect(MAP_DROPPED));
        }
        self.map_entry.borrow_mut().delete = true;
    }

    // Go: project/dirty/map.go:48 Locked
    pub fn locked(&self, fn_: &mut dyn FnMut(&dyn Value<V>)) {
        fn_(self);
    }
}

impl<K: Eq + Hash + Clone, V: Cloneable + Clone> Value<V> for MapEntry<K, V> {
    fn value(&self) -> Option<V> {
        MapEntry::value(self)
    }

    fn original(&self) -> Option<V> {
        MapEntry::original(self)
    }

    fn dirty(&self) -> bool {
        MapEntry::dirty(self)
    }

    fn change(&self, apply: &mut dyn FnMut(&V)) {
        MapEntry::change(self, apply)
    }

    fn change_if(
        &self,
        cond: &mut dyn FnMut(Option<&V>) -> bool,
        apply: &mut dyn FnMut(&V),
    ) -> bool {
        MapEntry::change_if(self, cond, apply)
    }

    fn delete(&self) {
        MapEntry::delete(self)
    }

    fn locked(&self, fn_: &mut dyn FnMut(&dyn Value<V>)) {
        MapEntry::locked(self, fn_)
    }
}

// Go: project/dirty/map.go:52 Map
// PORT: Go `*Map` is shared and mutated, so the maps use `RefCell`. `dirty`
// keeps insertion order (PORT: Go map order is random). The base map is an
// `Rc` because a Go map is a reference: it is shared with the value it came
// from, and `finalize_shared` gives it back unchanged. Only `clear`
// replaces it. `this` is the Go pointer that new entries point back to.
pub struct Map<K, V> {
    pub base: RefCell<Rc<FxHashMap<K, V>>>,
    pub dirty: RefCell<IndexMap<K, Rc<MapEntry<K, V>>>>,
    this: Weak<Map<K, V>>,
}

// Go: project/dirty/map.go:57 NewMap
// PORT: takes an owned base map. `new_map_shared` takes a shared one.
pub fn new_map<K, V>(base: FxHashMap<K, V>) -> Rc<Map<K, V>> {
    new_map_shared(Rc::new(base))
}

// Go: project/dirty/map.go:57 NewMap
// PORT: Go keeps the caller's map without a copy. This form does the same
// with a shared `Rc` map.
pub fn new_map_shared<K, V>(base: Rc<FxHashMap<K, V>>) -> Rc<Map<K, V>> {
    Rc::new_cyclic(|this| Map {
        base: RefCell::new(base),
        dirty: RefCell::new(IndexMap::new()),
        this: this.clone(),
    })
}

impl<K: Eq + Hash + Clone, V: Cloneable + Clone> Map<K, V> {
    // Go: project/dirty/map.go:64 Get
    pub fn get(&self, key: &K) -> (Option<Rc<MapEntry<K, V>>>, bool) {
        let entry = self.dirty.borrow().get(key).cloned();
        if let Some(entry) = entry {
            if entry.map_entry.borrow().delete {
                return (None, false);
            }
            return (Some(entry), true);
        }
        let value = self.base.borrow().get(key).cloned();
        let Some(value) = value else {
            return (None, false);
        };
        (
            Some(new_map_entry(
                &self.this,
                MapEntryImpl {
                    key: key.clone(),
                    original: Some(value.clone()),
                    value: Some(value),
                    dirty: false,
                    delete: false,
                },
            )),
            true,
        )
    }

    // Go: project/dirty/map.go:86 Add
    // Add sets a new entry in the dirty map without checking if it exists
    // in the base map. The entry added is considered dirty, so it should
    // be a fresh value, mutable until finalized (i.e., it will not be cloned
    // before changing if a change is made). If modifying an entry that may
    // exist in the base map, use `Change` instead.
    pub fn add(&self, key: K, value: V) {
        let entry = new_map_entry(
            &self.this,
            MapEntryImpl {
                key: key.clone(),
                original: None,
                value: Some(value),
                dirty: true,
                delete: false,
            },
        );
        self.dirty.borrow_mut().insert(key, entry);
    }

    // Go: project/dirty/map.go:102 Change
    pub fn change(&self, key: &K, apply: &mut dyn FnMut(&V)) {
        if let (Some(entry), true) = self.get(key) {
            entry.change(apply);
        } else {
            panic!("tried to change a non-existent entry");
        }
    }

    // Go: project/dirty/map.go:110 TryDelete
    pub fn try_delete(&self, key: &K) -> bool {
        if let (Some(entry), true) = self.get(key) {
            entry.delete();
            return true;
        }
        false
    }

    // Go: project/dirty/map.go:118 Delete
    pub fn delete(&self, key: &K) {
        if !self.try_delete(key) {
            panic!("tried to delete a non-existent entry");
        }
    }

    // Go: project/dirty/map.go:124 Range
    // PORT: the dirty entries are copied out first so `fn_` can change the
    // map. The base loop holds its own `Rc` of the base map, as Go ranges
    // over the map value it read (a `clear` in `fn_` does not change it).
    // Go keeps going with the base map after `fn_` stops the dirty loop;
    // the port does the same.
    pub fn range(&self, fn_: &mut dyn FnMut(&Rc<MapEntry<K, V>>) -> bool) {
        let mut seen_in_dirty: FxHashSet<K> = FxHashSet::default();
        let dirty: Vec<Rc<MapEntry<K, V>>> = self.dirty.borrow().values().cloned().collect();
        for entry in &dirty {
            seen_in_dirty.insert(entry.map_entry.borrow().key.clone());
            let deleted = entry.map_entry.borrow().delete;
            if !deleted && !fn_(entry) {
                break;
            }
        }
        let base: Rc<FxHashMap<K, V>> = self.base.borrow().clone();
        for (key, value) in base.iter() {
            if seen_in_dirty.contains(key) {
                continue; // already processed in dirty entries
            }
            let entry = new_map_entry(
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

    // Go: project/dirty/map.go:147 Clear
    pub fn clear(&self) {
        *self.dirty.borrow_mut() = IndexMap::new();
        *self.base.borrow_mut() = Rc::new(FxHashMap::default());
    }

    // Go: project/dirty/map.go:152 Finalize
    // PORT: returns an owned map for callers that keep a plain `FxHashMap`.
    // When nothing changed, that is a copy of the base map.
    // `finalize_shared` returns the base map itself, as Go does.
    pub fn finalize(&self) -> (FxHashMap<K, V>, bool) {
        let (result, changed) = self.finalize_shared();
        (Rc::unwrap_or_clone(result), changed)
    }

    // Go: project/dirty/map.go:152 Finalize
    // PORT: when nothing changed, the result is the base map (an `Rc` clone),
    // as in Go. Otherwise it is a new map.
    pub fn finalize_shared(&self) -> (Rc<FxHashMap<K, V>>, bool) {
        if self.dirty.borrow().is_empty() {
            return (self.base.borrow().clone(), false); // no changes, return base map
        }
        // Go: a nil base map gives make(map[K]V, len(m.dirty)); else maps.Clone.
        let mut result: FxHashMap<K, V> = (**self.base.borrow()).clone();
        let dirty: Vec<(K, Rc<MapEntry<K, V>>)> = self
            .dirty
            .borrow()
            .iter()
            .map(|(k, e)| (k.clone(), e.clone()))
            .collect();
        for (key, entry) in dirty {
            let e = entry.map_entry.borrow();
            if e.delete {
                result.remove(&key);
            } else {
                // PORT: a dirty entry that is not deleted always holds a
                // value (Add, Change and Replace set one); Go would store nil.
                result.insert(
                    key,
                    e.value
                        .clone()
                        .expect("nil pointer dereference: MapEntry.value"),
                );
            }
        }
        (Rc::new(result), true)
    }
}
