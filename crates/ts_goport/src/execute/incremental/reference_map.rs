//! Port of execute/incremental/referencemap.go.
//!
//! PORT: Go `collections.SyncMap` and `collections.Set` are `IndexMap` and
//! `IndexSet`. Go iterates these maps in random order; the port iterates in
//! insertion order so that runs are repeatable. Every Go caller either sorts
//! the result or does not depend on the order.

use crate::frontend::prelude::*;
use std::cell::OnceCell;

// Go: incremental/referencemap.go:12 referenceMap
#[derive(Debug, Default)]
pub struct ReferenceMap {
    references: IndexMap<Path, IndexSet<Path>>,
    // PORT: Go `referencedBy` plus the `referenceBy` sync.Once.
    referenced_by: OnceCell<FxHashMap<Path, IndexSet<Path>>>,
}

impl ReferenceMap {
    // Go: incremental/referencemap.go:18 storeReferences
    pub fn store_references(&mut self, path: Path, refs: IndexSet<Path>) {
        self.references.insert(path, refs);
    }

    // Go: incremental/referencemap.go:22 getReferences
    // PORT: Go returns `(*Set, bool)`; a missing entry is `None`.
    #[must_use]
    pub fn get_references(&self, path: &Path) -> Option<&IndexSet<Path>> {
        self.references.get(path)
    }

    // Go: incremental/referencemap.go:27 getPathsWithReferences
    #[must_use]
    pub fn get_paths_with_references(&self) -> Vec<Path> {
        self.references.keys().cloned().collect()
    }

    // Go: incremental/referencemap.go:31 getReferencedBy
    // PORT: Go returns an iterator over the set keys; this returns a copy.
    #[must_use]
    pub fn get_referenced_by(&self, path: &Path) -> Vec<Path> {
        let referenced_by = self.referenced_by.get_or_init(|| {
            let mut referenced_by: FxHashMap<Path, IndexSet<Path>> = FxHashMap::default();
            for (key, value) in &self.references {
                for ref_ in value {
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
