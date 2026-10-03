//! Port of execute/incremental/referencemap.go.
//!
//! PORT: Go `collections.SyncMap` and `collections.Set` are `FxIndexMap`
//! and `FxIndexSet`. Go iterates these maps in random order; the port
//! iterates in insertion order so that runs are repeatable. Every Go caller
//! either sorts the result or does not depend on the order.
//!
//! PERF: the keys are long paths, so the maps and sets use the Fx hasher
//! instead of SipHash. The hasher does not change the order.

use crate::frontend::prelude::*;
use std::cell::OnceCell;
use std::sync::Arc;

// Go: incremental/referencemap.go:13 referenceMap
// PORT: Go stores `*collections.Set` pointers, and several files can share
// one set (`buildInfoToSnapshot` stores one set for each file id list). The
// port shares a set with `Arc`, so storing it does not copy its paths.
#[derive(Debug, Default)]
pub struct ReferenceMap {
    references: FxIndexMap<Path, Arc<FxIndexSet<Path>>>,
    // PORT: Go `referencedBy` plus the `referenceBy` sync.Once.
    referenced_by: OnceCell<FxHashMap<Path, FxIndexSet<Path>>>,
}

impl ReferenceMap {
    // Go: incremental/referencemap.go:19 storeReferences
    pub fn store_references(&mut self, path: Path, refs: Arc<FxIndexSet<Path>>) {
        self.references.insert(path, refs);
    }

    // Go: incremental/referencemap.go:23 getReferences
    // PORT: Go returns `(*Set, bool)`; a missing entry is `None`.
    #[must_use]
    pub fn get_references(&self, path: &Path) -> Option<&FxIndexSet<Path>> {
        self.references.get(path).map(|refs| &**refs)
    }

    /// `get_references` that shares the stored set.
    #[must_use]
    pub fn get_references_arc(&self, path: &str) -> Option<Arc<FxIndexSet<Path>>> {
        self.references.get(path).cloned()
    }

    // Go: incremental/referencemap.go:28 getPathsWithReferences
    #[must_use]
    pub fn get_paths_with_references(&self) -> Vec<Path> {
        self.references.keys().cloned().collect()
    }

    // Go: incremental/referencemap.go:32 getReferencedBy
    // PORT: Go returns an iterator over the set keys; this returns a copy.
    #[must_use]
    pub fn get_referenced_by(&self, path: &Path) -> Vec<Path> {
        let referenced_by = self.referenced_by.get_or_init(|| {
            let mut referenced_by: FxHashMap<Path, FxIndexSet<Path>> = FxHashMap::default();
            for (key, value) in &self.references {
                for ref_ in value.iter() {
                    referenced_by
                        .entry(ref_.clone())
                        .or_default()
                        .insert(key.clone());
                }
            }
            referenced_by
        });
        match referenced_by.get(path) {
            Some(refs) => refs.iter().cloned().collect(),
            None => Vec::new(),
        }
    }
}
