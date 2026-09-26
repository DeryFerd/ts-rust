//! Go `internal/project/dirty/util.go`.

use crate::project::dirty::prelude::*;
use std::hash::Hash;

// Go: project/dirty/util.go:5 CloneMapIfNil
// PORT: Go returns the dirty map itself, a shared reference. The port
// returns an owned map: a copy of the dirty map, or of the original map.
// `get_map` returns `None` for a Go nil map. Go calls `getMap(dirty)` with a
// pointer that its callers never pass as nil, so `dirty` is `&T`. No Go
// code outside tests calls this function.
pub fn clone_map_if_nil<K: Eq + Hash + Clone, V: Clone, T>(
    dirty: &T,
    original: Option<&T>,
    get_map: impl Fn(&T) -> Option<&FxHashMap<K, V>>,
) -> FxHashMap<K, V> {
    let dirty_map = get_map(dirty);
    let Some(dirty_map) = dirty_map else {
        let Some(original) = original else {
            return FxHashMap::default();
        };
        let original_map = get_map(original);
        let Some(original_map) = original_map else {
            return FxHashMap::default();
        };
        // Go: maps.Clone(originalMap)
        return original_map.clone();
    };
    dirty_map.clone()
}
