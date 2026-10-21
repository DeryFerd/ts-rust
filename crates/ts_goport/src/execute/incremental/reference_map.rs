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

/// Go `referencedBy`: the files that reference each path.
type ReferencedBy = FxHashMap<Path, Arc<[Path]>>;

// Go: incremental/referencemap.go:13 referenceMap
// PORT: Go stores `*collections.Set` pointers, and several files can share
// one set (`buildInfoToSnapshot` stores one set for each file id list). The
// port shares a set with `Arc`, so storing it does not copy its paths.
#[derive(Debug, Default)]
pub struct ReferenceMap {
    references: FxIndexMap<Path, Arc<FxIndexSet<Path>>>,
    // PORT: Go `referencedBy` plus the `referenceBy` sync.Once. Each set is
    // a shared list (in the set's order), so `get_referenced_by` does not
    // copy it.
    referenced_by: OnceCell<ReferencedBy>,
    /// The result of `get_referenced_by` for a path that no file references.
    no_referencers: Arc<[Path]>,
    /// PORT: not in Go. The program's `--singleThreaded`: the
    /// `referenced_by` lists are then made on this thread only.
    pub single_threaded: bool,
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
    // PORT: Go returns an iterator over the set keys; this returns the shared
    // list in the set's order (perf: a call copies no path; t3inc1).
    #[must_use]
    pub fn get_referenced_by(&self, path: &Path) -> Arc<[Path]> {
        let referenced_by = self
            .referenced_by
            .get_or_init(|| referenced_by_of(&self.references, self.single_threaded));
        referenced_by
            .get(path)
            .map_or_else(|| Arc::clone(&self.no_referencers), Arc::clone)
    }
}

/// The parts of `referenced_by_of` that run on threads have at least this
/// many references each.
const REFERENCES_PER_THREAD: usize = 16_384;

/// At most this many threads make the `referenced_by_of` parts.
const MAX_REFERENCED_BY_THREADS: usize = 8;

/// The referencers of a path in `referenced_by_of`: indexes of the entries
/// of `references`, in order.
type Referencers<'a> = (&'a Path, Vec<u32>);

/// Go `referencedBy`: for each path that `references` names, the files that
/// reference it, in the order of `references`.
// PORT: perf (t3inc1). Go adds each file to a set per referenced path. A
// file references a path at most once, so a list in the same order holds
// the same files, and the referenced paths are cloned once each, not once
// per reference.
// PORT: perf (t3inc2). The lists hold entry indexes until each is made into
// one list of paths. With many references, threads make the lists of
// consecutive parts of `references`. Each part cuts its lists into buckets
// by the hash of the referenced path, and a thread per bucket joins the
// lists of each path in the order of the parts. So each list has the same
// files in the same order as one pass over `references`. T3 Code apps/web
// has 327,661 references: 15 to 21 ms in one pass on a boat sandbox, all of
// it before the check starts.
fn referenced_by_of(
    references: &FxIndexMap<Path, Arc<FxIndexSet<Path>>>,
    single_threaded: bool,
) -> ReferencedBy {
    let entries: Vec<(&Path, &FxIndexSet<Path>)> = references
        .iter()
        .map(|(key, value)| (key, &**value))
        .collect();
    let total: usize = entries.iter().map(|(_, value)| value.len()).sum();
    let threads = referenced_by_threads(total, single_threaded);
    let paths = |indexes: &[u32]| -> Arc<[Path]> {
        indexes
            .iter()
            .map(|&index| entries[index as usize].0.clone())
            .collect()
    };
    if threads == 1 {
        return referenced_by_of_part(&entries, 0)
            .into_iter()
            .map(|(path, indexes)| (path.clone(), paths(&indexes)))
            .collect();
    }
    let parts = split_by_references(&entries, total.div_ceil(threads));
    let buckets = parts.len();
    std::thread::scope(|scope| {
        // The lists of each part, cut into buckets.
        let mut first = 0;
        let cut: Vec<Vec<Vec<Referencers<'_>>>> = join_all(
            parts
                .into_iter()
                .map(|part| {
                    let part_first = first;
                    first += part.len();
                    scope.spawn(move || {
                        let mut cut: Vec<Vec<Referencers<'_>>> =
                            (0..buckets).map(|_| Vec::new()).collect();
                        for (path, indexes) in referenced_by_of_part(part, part_first) {
                            cut[bucket_of(path, buckets)].push((path, indexes));
                        }
                        cut
                    })
                })
                .collect(),
        );
        // Each bucket gets its piece of each part, in the order of the parts.
        let mut pieces: Vec<Vec<Vec<Referencers<'_>>>> =
            (0..buckets).map(|_| Vec::with_capacity(buckets)).collect();
        for part in cut {
            for (bucket, piece) in part.into_iter().enumerate() {
                pieces[bucket].push(piece);
            }
        }
        let paths = &paths;
        let joined: Vec<Vec<(Path, Arc<[Path]>)>> = join_all(
            pieces
                .into_iter()
                .map(|bucket| {
                    scope.spawn(move || {
                        let mut lists: FxHashMap<&Path, Vec<u32>> = FxHashMap::default();
                        for piece in bucket {
                            for (path, indexes) in piece {
                                match lists.entry(path) {
                                    std::collections::hash_map::Entry::Vacant(entry) => {
                                        entry.insert(indexes);
                                    }
                                    std::collections::hash_map::Entry::Occupied(mut entry) => {
                                        entry.get_mut().extend(indexes);
                                    }
                                }
                            }
                        }
                        lists
                            .into_iter()
                            .map(|(path, indexes)| (path.clone(), paths(&indexes)))
                            .collect()
                    })
                })
                .collect(),
        );
        let mut referenced_by = FxHashMap::with_capacity_and_hasher(
            joined.iter().map(Vec::len).sum(),
            rustc_hash::FxBuildHasher,
        );
        for bucket in joined {
            referenced_by.extend(bucket);
        }
        referenced_by
    })
}

/// The threads of `referenced_by_of` for `total` references: 1 (this
/// thread) with `--singleThreaded`, on wasm or with few references.
fn referenced_by_threads(total: usize, single_threaded: bool) -> usize {
    if single_threaded || cfg!(target_family = "wasm") {
        return 1;
    }
    std::thread::available_parallelism()
        .map_or(1, std::num::NonZero::get)
        .min(MAX_REFERENCED_BY_THREADS)
        .min(total / REFERENCES_PER_THREAD)
        .max(1)
}

/// The results of `handles`, in order. A panic of a thread continues here.
fn join_all<T>(handles: Vec<std::thread::ScopedJoinHandle<'_, T>>) -> Vec<T> {
    handles
        .into_iter()
        .map(|handle| {
            handle
                .join()
                .unwrap_or_else(|payload| std::panic::resume_unwind(payload))
        })
        .collect()
}

/// The bucket of `path` among `buckets` (from the high bits of its hash).
fn bucket_of(path: &Path, buckets: usize) -> usize {
    use std::hash::BuildHasher;
    let hash = rustc_hash::FxBuildHasher.hash_one(path);
    ((u128::from(hash) * buckets as u128) >> 64) as usize
}

/// The `referenced_by_of` lists of `entries` alone, as indexes from
/// `first` (the index of the first entry).
fn referenced_by_of_part<'a>(
    entries: &[(&Path, &'a FxIndexSet<Path>)],
    first: usize,
) -> FxHashMap<&'a Path, Vec<u32>> {
    let mut referenced_by: FxHashMap<&Path, Vec<u32>> = FxHashMap::default();
    for (index, (_, value)) in entries.iter().enumerate() {
        let index = u32::try_from(first + index).expect("fewer than 2^32 files");
        for ref_ in value.iter() {
            referenced_by.entry(ref_).or_default().push(index);
        }
    }
    referenced_by
}

/// `entries` cut into consecutive parts, each with at least `per_part`
/// references (the last can have fewer).
fn split_by_references<'e, 'a>(
    entries: &'e [(&'a Path, &'a FxIndexSet<Path>)],
    per_part: usize,
) -> Vec<&'e [(&'a Path, &'a FxIndexSet<Path>)]> {
    let mut parts = Vec::new();
    let mut start = 0;
    let mut count = 0;
    for (index, (_, value)) in entries.iter().enumerate() {
        count += value.len();
        if count >= per_part {
            parts.push(&entries[start..=index]);
            start = index + 1;
            count = 0;
        }
    }
    if start < entries.len() {
        parts.push(&entries[start..]);
    }
    parts
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `files` files, each referencing `per_file` of `targets` paths in an
    /// order that differs per file. The keys are some of the targets too.
    fn references(
        files: usize,
        targets: usize,
        per_file: usize,
    ) -> FxIndexMap<Path, Arc<FxIndexSet<Path>>> {
        let target = |i: usize| Path(format!("/p/t{i}.ts"));
        (0..files)
            .map(|file| {
                let refs: FxIndexSet<Path> = (0..per_file)
                    .map(|k| target((file * 7 + k * 13) % targets))
                    .collect();
                (target(targets / 2 + file), Arc::new(refs))
            })
            .collect()
    }

    /// Go `referencedBy`: a set per referenced path, in the order of the
    /// references (`collections.Set` iterates in insertion order here).
    fn go_referenced_by(
        references: &FxIndexMap<Path, Arc<FxIndexSet<Path>>>,
    ) -> FxHashMap<Path, Vec<Path>> {
        let mut sets: FxHashMap<Path, FxIndexSet<Path>> = FxHashMap::default();
        for (key, value) in references {
            for ref_ in value.iter() {
                sets.entry(ref_.clone()).or_default().insert(key.clone());
            }
        }
        sets.into_iter()
            .map(|(path, set)| (path, set.into_iter().collect()))
            .collect()
    }

    fn as_lists(referenced_by: FxHashMap<Path, Arc<[Path]>>) -> FxHashMap<Path, Vec<Path>> {
        referenced_by
            .into_iter()
            .map(|(path, refs)| (path, refs.to_vec()))
            .collect()
    }

    // t3inc2: the lists made on threads are Go's lists, in Go's order.
    #[test]
    fn referenced_by_on_threads_keeps_the_order() {
        let references = references(400, 1_000, 200);
        let total = 400 * 200;
        if std::thread::available_parallelism().map_or(1, std::num::NonZero::get) > 1 {
            assert!(referenced_by_threads(total, false) > 1);
        }
        assert_eq!(referenced_by_threads(total, true), 1);
        let go = go_referenced_by(&references);
        assert_eq!(as_lists(referenced_by_of(&references, false)), go);
        assert_eq!(as_lists(referenced_by_of(&references, true)), go);
    }

    // t3inc2: one pass for few references.
    #[test]
    fn referenced_by_of_few_references() {
        let references = references(30, 50, 10);
        assert_eq!(referenced_by_threads(300, false), 1);
        assert_eq!(
            as_lists(referenced_by_of(&references, false)),
            go_referenced_by(&references)
        );
        let map = ReferenceMap {
            references,
            ..ReferenceMap::default()
        };
        assert!(map.get_referenced_by(&Path("/p/none.ts".into())).is_empty());
    }

    // t3inc2: the parts are consecutive, cover every entry, and each part
    // but the last has at least `per_part` references.
    #[test]
    fn split_by_references_covers_the_entries() {
        let references = references(100, 300, 40);
        let entries: Vec<(&Path, &FxIndexSet<Path>)> = references
            .iter()
            .map(|(key, value)| (key, &**value))
            .collect();
        for per_part in [1, 39, 40, 41, 1_000, 4_000, 10_000] {
            let parts = split_by_references(&entries, per_part);
            let joined: Vec<&Path> = parts
                .iter()
                .flat_map(|part| part.iter().map(|e| e.0))
                .collect();
            assert_eq!(joined, entries.iter().map(|e| e.0).collect::<Vec<_>>());
            for part in &parts[..parts.len() - 1] {
                assert!(part.iter().map(|e| e.1.len()).sum::<usize>() >= per_part);
            }
        }
    }
}
