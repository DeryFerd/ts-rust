//! Go `internal/project/dirty/mapbuilder.go`.

use crate::project::dirty::prelude::*;
use std::hash::Hash;

// Go: project/dirty/mapbuilder.go:5 MapBuilder
// PORT: Go `*MapBuilder` is shared and mutated, so the maps use `RefCell`
// and the methods take `&self`. A Go nil `deleted` map is an empty set.
// `dirty` keeps insertion order (PORT: Go map order is random).
pub struct MapBuilder<K, VBase, VBuilder> {
    pub base: FxHashMap<K, VBase>,
    pub dirty: RefCell<IndexMap<K, VBuilder>>,
    pub deleted: RefCell<FxHashSet<K>>,

    pub to_builder: Rc<dyn Fn(VBase) -> VBuilder>,
    pub build: Rc<dyn Fn(VBuilder) -> VBase>,
}

// Go: project/dirty/mapbuilder.go:14 NewMapBuilder
pub fn new_map_builder<K, VBase, VBuilder>(
    base: FxHashMap<K, VBase>,
    to_builder: impl Fn(VBase) -> VBuilder + 'static,
    build: impl Fn(VBuilder) -> VBase + 'static,
) -> Rc<MapBuilder<K, VBase, VBuilder>> {
    Rc::new(MapBuilder {
        base,
        dirty: RefCell::new(IndexMap::new()),
        deleted: RefCell::new(FxHashSet::default()),
        to_builder: Rc::new(to_builder),
        build: Rc::new(build),
    })
}

impl<K: Eq + Hash + Clone, VBase: Clone, VBuilder: Clone> MapBuilder<K, VBase, VBuilder> {
    // Go: project/dirty/mapbuilder.go:27 Set
    pub fn set(&self, key: K, value: VBuilder) {
        self.dirty.borrow_mut().insert(key.clone(), value);
        self.deleted.borrow_mut().remove(&key);
    }

    // Go: project/dirty/mapbuilder.go:32 Delete
    pub fn delete(&self, key: &K) {
        // Go: `if mb.deleted == nil { mb.deleted = make(...) }` (the port
        // set always exists).
        self.deleted.borrow_mut().insert(key.clone());
        // PORT: Go `delete` on a map; `shift_remove` keeps the order.
        self.dirty.borrow_mut().shift_remove(key);
    }

    // Go: project/dirty/mapbuilder.go:40 Clear
    pub fn clear(&self) {
        *self.dirty.borrow_mut() = IndexMap::new();
        let mut deleted = FxHashSet::default();
        deleted.reserve(self.base.len());
        for key in self.base.keys() {
            deleted.insert(key.clone());
        }
        *self.deleted.borrow_mut() = deleted;
    }

    // Go: project/dirty/mapbuilder.go:48 Has
    pub fn has(&self, key: &K) -> bool {
        if self.deleted.borrow().contains(key) {
            return false;
        }
        if self.dirty.borrow().contains_key(key) {
            return true;
        }
        self.base.contains_key(key)
    }

    // Go: project/dirty/mapbuilder.go:59 Build
    // PORT: Go returns the shared base map when nothing changed; the port
    // returns a copy.
    pub fn build(&self) -> FxHashMap<K, VBase> {
        if self.dirty.borrow().is_empty() && self.deleted.borrow().is_empty() {
            return self.base.clone();
        }
        // Go: maps.Clone(mb.base); a nil result becomes an empty map.
        let mut result = self.base.clone();
        let deleted: Vec<K> = self.deleted.borrow().iter().cloned().collect();
        for key in &deleted {
            result.remove(key);
        }
        let dirty: Vec<(K, VBuilder)> = self
            .dirty
            .borrow()
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        for (key, value) in dirty {
            result.insert(key, (self.build)(value));
        }
        result
    }
}
