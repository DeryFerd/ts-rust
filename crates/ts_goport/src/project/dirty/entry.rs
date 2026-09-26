//! Go `internal/project/dirty/entry.go`.

use crate::project::dirty::prelude::*;

// Go: project/dirty/entry.go:3 mapEntry
// PORT: Go `mapEntry` (unexported) and `MapEntry` (map.go) would share one
// Rust type namespace, so the unexported base is `MapEntryImpl`. Go embeds
// it in `MapEntry` and `SyncMapEntry`; Rust holds it in their `map_entry`
// field. `original` and `value` are `None` where Go holds the zero value
// (nil).
pub struct MapEntryImpl<K, V> {
    pub key: K,
    pub original: Option<V>,
    pub value: Option<V>,
    pub dirty: bool,
    pub delete: bool,
}

impl<K: Clone, V: Clone> MapEntryImpl<K, V> {
    // Go: project/dirty/entry.go:11 Key
    pub fn key(&self) -> K {
        self.key.clone()
    }

    // Go: project/dirty/entry.go:15 Original
    pub fn original(&self) -> Option<V> {
        self.original.clone()
    }

    // Go: project/dirty/entry.go:19 Value
    pub fn value(&self) -> Option<V> {
        if self.delete {
            return None;
        }
        self.value.clone()
    }

    // Go: project/dirty/entry.go:27 Dirty
    pub fn dirty(&self) -> bool {
        self.dirty
    }
}
