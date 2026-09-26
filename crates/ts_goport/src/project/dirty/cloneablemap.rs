//! Go `internal/project/dirty/cloneablemap.go`.

use crate::project::dirty::prelude::*;
use std::hash::Hash;
use std::ops::Deref;

// Go: project/dirty/cloneablemap.go:5 CloneableMap
// PORT: a Go map is a reference, so `Change` mutates it in place. The port
// shares the map through `Rc<RefCell<..>>`: `Clone` copies the handle and
// `clone_` (Go `Clone`) copies the map. Go `make(CloneableMap[K, V])` is
// `CloneableMap::default()`. A Go nil map has no port value; the dirty zero
// value is `None` (see interfaces.rs).
pub struct CloneableMap<K, V>(pub Rc<RefCell<FxHashMap<K, V>>>);

impl<K: Eq + Hash + Clone, V: Clone> CloneableMap<K, V> {
    // Go: project/dirty/cloneablemap.go:7 Clone
    pub fn clone_(&self) -> CloneableMap<K, V> {
        // Go: maps.Clone(m)
        CloneableMap(Rc::new(RefCell::new(self.0.borrow().clone())))
    }
}

impl<K: Eq + Hash + Clone, V: Clone> Cloneable for CloneableMap<K, V> {
    fn clone_(&self) -> Self {
        CloneableMap::clone_(self)
    }
}

impl<K, V> Clone for CloneableMap<K, V> {
    fn clone(&self) -> Self {
        CloneableMap(Rc::clone(&self.0))
    }
}

impl<K, V> Default for CloneableMap<K, V> {
    fn default() -> Self {
        CloneableMap(Rc::new(RefCell::new(FxHashMap::default())))
    }
}

impl<K, V> Deref for CloneableMap<K, V> {
    type Target = RefCell<FxHashMap<K, V>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
