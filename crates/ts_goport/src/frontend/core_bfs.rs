//! Go `internal/core/bfs.go`.
//!
//! PORT: the language service runs on one dispatch thread
//! (`project/dirty/interfaces.rs`, decision 1). Go runs each level's jobs in
//! goroutines; the port runs them serially in queue order. Go starts every
//! goroutine of a level before a slow `visit` returns, so in Go's common
//! schedule each job passes its start check (`core/bfs.go:102`) and is
//! visited. The port follows that schedule: it visits every job of the
//! level and keeps only the check after the visit (`core/bfs.go:128`), so
//! the result and the next level are Go's deterministic ones. The side
//! effects of `visit` (the project search creates and loads each project of
//! the level) are those of Go's common schedule.
//!
//! Go's other schedule has no condition that the port can read: a later
//! job skips its visit only when its goroutine runs the start check after
//! an earlier job's `visit` has stored `lowestGoal`. That can happen only
//! when the earlier visit is fast (a project that is already loaded and up
//! to date, as at a hono reopen), and then it depends on the scheduler and
//! the CPU: Go N skipped hono's spec project in 5 of 7 reopens on
//! mini-743d, took the common schedule in both runs on alvin
//! (projsearch1b), and skipped it in about 4 of 15 reopens for the R170
//! reviewer. Both answers are Go's. The port keeps the
//! common one, so its answers (willRenameFiles: 11 files, 2 tests) do not
//! change from run to run or host to host.

use crate::frontend::prelude::*;
use std::hash::Hash;

// Go: core/bfs.go:11 BreadthFirstSearchResult
pub struct BreadthFirstSearchResult<N> {
    pub stopped: bool,
    pub path: Vec<N>,
}

// Go: core/bfs.go:16 breadthFirstSearchJob
pub struct BreadthFirstSearchJob<N> {
    pub node: N,
    pub parent: Option<Rc<BreadthFirstSearchJob<N>>>,
}

// Go: core/bfs.go:21 BreadthFirstSearchLevel
// PORT: Go holds a pointer to the level's `OrderedMap`. The port moves the
// map in for the `PreprocessLevel` call and back out after it. `RefCell`
// lets a `Range` callback call `Delete` on the same level, as Go does.
pub struct BreadthFirstSearchLevel<K, N> {
    pub jobs: RefCell<IndexMap<K, Rc<BreadthFirstSearchJob<N>>>>,
}

impl<K: Eq + Hash, N: Clone> BreadthFirstSearchLevel<K, N> {
    // Go: core/bfs.go:25 Has
    pub fn has(&self, key: &K) -> bool {
        self.jobs.borrow().contains_key(key)
    }

    // Go: core/bfs.go:29 Delete
    pub fn delete(&self, key: &K) {
        // PORT: Go OrderedMap.Delete keeps the order of the other keys.
        self.jobs.borrow_mut().shift_remove(key);
    }

    // Go: core/bfs.go:33 Range
    pub fn range(&self, f: &mut dyn FnMut(&N) -> bool) {
        // Go: OrderedMap.Values reads the key slice by index on every step,
        // so a Delete during the loop shifts the later jobs down.
        let mut i = 0;
        loop {
            let node = {
                let jobs = self.jobs.borrow();
                if i >= jobs.len() {
                    break;
                }
                jobs.get_index(i)
                    .expect("index checked above")
                    .1
                    .node
                    .clone()
            };
            if !f(&node) {
                return;
            }
            i += 1;
        }
    }
}

// Go: core/bfs.go:41 BreadthFirstSearchOptions
pub struct BreadthFirstSearchOptions<'a, K, N> {
    // Visited is a set of nodes that have already been visited.
    // If nil, a new set will be created.
    // PORT: Go `*collections.SyncSet[K]`.
    pub visited: Option<&'a RefCell<FxHashSet<K>>>,
    // PreprocessLevel is a function that, if provided, will be called
    // before each level, giving the caller an opportunity to remove nodes.
    pub preprocess_level: Option<&'a mut dyn FnMut(&BreadthFirstSearchLevel<K, N>)>,
}

impl<K, N> Default for BreadthFirstSearchOptions<'_, K, N> {
    fn default() -> Self {
        BreadthFirstSearchOptions {
            visited: None,
            preprocess_level: None,
        }
    }
}

// Go: core/bfs.go:53 BreadthFirstSearchParallel
// BreadthFirstSearchParallel performs a breadth-first search on a graph
// starting from the given node. It processes nodes in parallel and returns the path
// from the first node that satisfies the `visit` function back to the start node.
pub fn breadth_first_search_parallel<N: Clone + Eq + Hash>(
    start: N,
    neighbors: &mut dyn FnMut(&N) -> Vec<N>,
    visit: &mut dyn FnMut(&N) -> (bool, bool),
) -> BreadthFirstSearchResult<N> {
    // Go: core.Identity
    breadth_first_search_parallel_ex(
        start,
        neighbors,
        visit,
        BreadthFirstSearchOptions::default(),
        &mut |node: &N| node.clone(),
    )
}

// Go: core/bfs.go:76 result (local type of BreadthFirstSearchParallelEx)
struct ProcessLevelResult<K, N> {
    stop: bool,
    job: Option<Rc<BreadthFirstSearchJob<N>>>,
    next: Option<IndexMap<K, Rc<BreadthFirstSearchJob<N>>>>,
}

// Go: core/bfs.go:64 BreadthFirstSearchParallelEx
// BreadthFirstSearchParallelEx is an extension of BreadthFirstSearchParallel that allows
// the caller to pass a pre-seeded set of already-visited nodes and a preprocessing function
// that can be used to remove nodes from each level before parallel processing.
pub fn breadth_first_search_parallel_ex<K: Eq + Hash, N: Clone>(
    start: N,
    neighbors: &mut dyn FnMut(&N) -> Vec<N>,
    visit: &mut dyn FnMut(&N) -> (bool, bool),
    mut options: BreadthFirstSearchOptions<'_, K, N>,
    get_key: &mut dyn FnMut(&N) -> K,
) -> BreadthFirstSearchResult<N> {
    let new_visited = RefCell::new(FxHashSet::default());
    let visited = match options.visited {
        Some(visited) => visited,
        None => &new_visited,
    };

    let mut fallback: Option<Rc<BreadthFirstSearchJob<N>>> = None;

    let mut level_index: i32 = 0;
    // Go: collections.NewOrderedMapFromList([]collections.MapEntry{{Key: getKey(start), Value: &job{node: start}}})
    let mut level: IndexMap<K, Rc<BreadthFirstSearchJob<N>>> = IndexMap::with_capacity(1);
    let start_key = get_key(&start);
    level.insert(
        start_key,
        Rc::new(BreadthFirstSearchJob {
            node: start,
            parent: None,
        }),
    );
    while !level.is_empty() {
        let result = process_level(
            level_index,
            level,
            &mut fallback,
            visited,
            neighbors,
            visit,
            &mut options.preprocess_level,
            get_key,
        );
        if result.stop {
            return BreadthFirstSearchResult {
                stopped: true,
                path: create_path(result.job),
            };
        } else if result.job.is_some() && fallback.is_none() {
            fallback = result.job;
        }
        // Go: a nil `next` has Size() 0.
        level = result.next.unwrap_or_default();
        level_index += 1;
    }
    BreadthFirstSearchResult {
        stopped: false,
        path: create_path(fallback),
    }
}

// Go: core/bfs.go:86 processLevel (closure in BreadthFirstSearchParallelEx)
// processLevel processes each node at the current level in parallel.
// It produces either a list of jobs to be processed in the next level,
// or a result if the visit function returns true for any node.
// PORT: a function with the closure's captures as parameters. The job
// goroutines run serially in queue order.
fn process_level<'o, K: Eq + Hash, N: Clone>(
    _index: i32,
    jobs: IndexMap<K, Rc<BreadthFirstSearchJob<N>>>,
    fallback: &mut Option<Rc<BreadthFirstSearchJob<N>>>,
    visited: &RefCell<FxHashSet<K>>,
    neighbors: &mut dyn FnMut(&N) -> Vec<N>,
    visit: &mut dyn FnMut(&N) -> (bool, bool),
    preprocess_level: &mut Option<&'o mut dyn FnMut(&BreadthFirstSearchLevel<K, N>)>,
    get_key: &mut dyn FnMut(&N) -> K,
) -> ProcessLevelResult<K, N> {
    let mut lowest_fallback: i64 = i64::MAX;
    let mut lowest_goal: i64 = i64::MAX;
    let mut next_job_count: i64 = 0;
    let mut jobs = jobs;
    if let Some(preprocess_level) = preprocess_level.as_mut() {
        let level = BreadthFirstSearchLevel {
            jobs: RefCell::new(jobs),
        };
        preprocess_level(&level);
        jobs = level.jobs.into_inner();
    }
    let mut next: Vec<Vec<Rc<BreadthFirstSearchJob<N>>>> =
        (0..jobs.len()).map(|_| Vec::new()).collect();
    // Go: one goroutine per job, started in order with its index `i`.
    for (i, j) in jobs.values().enumerate() {
        let i = i as i64;
        // Go: core/bfs.go:102 `if int64(i) >= lowestGoal.Load() { return }`.
        // PORT: Go's common schedule starts every goroutine of the level
        // before an earlier job's `visit` sets `lowestGoal`, so every job
        // passes this check. The port has no check here (module comment).

        // If we have already visited this node, skip it.
        if !visited.borrow_mut().insert(get_key(&j.node)) {
            // Note that if we are here, we already visited this node at a
            // previous *level*, which means `visit` must have returned false,
            // so we don't need to update our result indices. This holds true
            // because we deduplicated jobs before queuing the level.
            continue;
        }

        let (is_result, stop) = visit(&j.node);
        if is_result {
            // We found a result, so we will stop at this level, but an
            // earlier job may still find a true result at a lower index.
            if stop {
                update_min(&mut lowest_goal, i);
                continue;
            }
            if fallback.is_none() {
                update_min(&mut lowest_fallback, i);
            }
        }

        if i >= lowest_goal {
            // If `visit` is expensive, it's likely that by the time we get here,
            // a different job has already found a lower index result, so we
            // don't even need to collect the next jobs.
            continue;
        }
        // Add the next level jobs
        let neighbor_nodes = neighbors(&j.node);
        if !neighbor_nodes.is_empty() {
            next_job_count += neighbor_nodes.len() as i64;
            next[i as usize] = neighbor_nodes
                .into_iter()
                .map(|child| {
                    Rc::new(BreadthFirstSearchJob {
                        node: child,
                        parent: Some(j.clone()),
                    })
                })
                .collect();
        }
    }
    if lowest_goal != i64::MAX {
        // If we found a result, return it immediately.
        let job = jobs
            .get_index(lowest_goal as usize)
            .map(|(_, job)| job.clone());
        return ProcessLevelResult {
            stop: true,
            job,
            next: None,
        };
    }
    if fallback.is_none() && lowest_fallback != i64::MAX {
        *fallback = jobs
            .get_index(lowest_fallback as usize)
            .map(|(_, job)| job.clone());
    }
    let mut next_jobs: IndexMap<K, Rc<BreadthFirstSearchJob<N>>> =
        IndexMap::with_capacity(next_job_count as usize);
    for jobs in next {
        for j in jobs {
            if !next_jobs.contains_key(&get_key(&j.node)) {
                // Deduplicate synchronously to avoid messy locks and spawning
                // unnecessary goroutines.
                next_jobs.insert(get_key(&j.node), j);
            }
        }
    }
    ProcessLevelResult {
        stop: false,
        job: None,
        next: Some(next_jobs),
    }
}

// Go: core/bfs.go:169 createPath (closure in BreadthFirstSearchParallelEx)
fn create_path<N: Clone>(job: Option<Rc<BreadthFirstSearchJob<N>>>) -> Vec<N> {
    let mut path = Vec::new();
    let mut job = job;
    while let Some(j) = job {
        path.push(j.node.clone());
        job = j.parent.clone();
    }
    path
}

// Go: core/bfs.go:196 updateMin
// updateMin updates the atomic integer `a` to the candidate value if it is less than the current value.
// PORT: one thread, so the compare-and-swap loop is a plain compare.
pub fn update_min(a: &mut i64, candidate: i64) -> bool {
    let current = *a;
    if current < candidate {
        return false;
    }
    *a = candidate;
    true
}
