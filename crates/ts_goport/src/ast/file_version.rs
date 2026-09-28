//! Rust-only: the owner and liveness of freeable file versions (lsshells
//! M3a).
//!
//! Go frees an `*ast.SourceFile` when no program and no parse cache entry
//! holds it (project/snapshot.go:537 `dispose`: `parseCache.Deref` for each
//! file of a released program). Here a published file store is leaked
//! (`ast/store.rs`), so every file id stays readable. A `FileVersion` gives
//! a file version the Go lifetime:
//! - its parse holds it (`ParsedSourceFile::version`), so each frontend
//!   program (`NewProgram`) and each parse cache entry that has the parse
//!   holds it;
//! - the tables of each program version that has the file hold it
//!   (`program::VersionTables`), so a checker, bind, emit or search thread
//!   that was seeded from that version holds it too (`WorkerSeed`);
//! - the registry here keeps only a `Weak`.
//!
//! When the last holder lets go, the version is dead: its id goes to
//! `DEAD_FILES`, and each per-file thread-local map (`PerFileMap`) forgets
//! the entries of that id when it is next written. The store, the node data
//! and the `GoFile` stay leaked in this step.
//!
//! Freeable rule (`free_file_versions`, `freeable_path`): only a parse of
//! the language server parse cache (project/parsecache.rs), in a language
//! server or API process, of a path that a publish on this thread published
//! before. So tier 0, the first version of each file and every CLI publish
//! never get a `FileVersion`. `GOPORT_FREE_FILE_VERSIONS=0` turns it off
//! (the behavior before M3a); `=1` turns it on in any process.

use crate::prelude::*;
use std::ops::Deref;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, OnceLock, PoisonError, Weak};

/// The owner of one freeable file version. It is `Send + Sync`: a program
/// version's tables carry it to worker threads.
#[derive(Debug)]
pub struct FileVersion {
    /// The file id (the store id).
    file: usize,
}

impl FileVersion {
    /// The owner of file version `file`, registered in the registry. The
    /// language server parse cache makes it (`freeable_path`).
    pub(crate) fn new(file: usize) -> Arc<Self> {
        let version = Arc::new(FileVersion { file });
        lock(&VERSIONS).insert(file, Arc::downgrade(&version));
        MADE.fetch_add(1, Ordering::Relaxed);
        version
    }
}

impl Drop for FileVersion {
    fn drop(&mut self) {
        // File ids are never reused, so the entry is this version's.
        lock(&VERSIONS).remove(&self.file);
        let mut dead = lock(&DEAD_FILES);
        dead.push(self.file);
        DEAD_COUNT.store(dead.len(), Ordering::Release);
    }
}

/// The live file versions by file id. A `Weak`, so the registry does not
/// keep a version alive.
static VERSIONS: Mutex<FxHashMap<usize, Weak<FileVersion>>> =
    Mutex::new(FxHashMap::with_hasher(rustc_hash::FxBuildHasher));

/// The ids of the dead file versions, in the order they died. `PerFileMap`
/// reads the ids after the length it saw last.
// PERF: one id per edit, so it grows by 8 bytes per edit.
static DEAD_FILES: Mutex<Vec<usize>> = Mutex::new(Vec::new());

/// The length of `DEAD_FILES` (the dead-file epoch). A map that saw this
/// length has nothing to forget.
static DEAD_COUNT: AtomicUsize = AtomicUsize::new(0);

/// The number of file versions made in this process.
static MADE: AtomicUsize = AtomicUsize::new(0);

/// Set by `project::new_session`: this process runs the language server or
/// the API.
static EDITOR_PROCESS: AtomicBool = AtomicBool::new(false);

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Marks this process as a language server or API process, where
/// `free_file_versions` is on by default. `project::new_session` calls it.
pub fn set_editor_process() {
    EDITOR_PROCESS.store(true, Ordering::Relaxed);
}

/// True when this process frees the file versions that the language server
/// publishes again. `GOPORT_FREE_FILE_VERSIONS` is read once: `0` is off,
/// `1` is on; else it is on in a language server or API process only.
pub fn free_file_versions() -> bool {
    static FLAG: OnceLock<Option<bool>> = OnceLock::new();
    let flag = *FLAG.get_or_init(
        || match std::env::var("GOPORT_FREE_FILE_VERSIONS").as_deref() {
            Ok("0") => Some(false),
            Ok("1") => Some(true),
            _ => None,
        },
    );
    flag.unwrap_or_else(|| EDITOR_PROCESS.load(Ordering::Relaxed))
}

thread_local! {
    /// The paths that a publish on this thread published, while
    /// `free_file_versions` is on (`note_published_path`).
    static PUBLISHED_PATHS: RefCell<FxHashSet<String>> = RefCell::new(FxHashSet::default());
}

/// Records that a publish on this thread published a file at `path`. Does
/// nothing while `free_file_versions` is off.
pub(crate) fn note_published_path(path: &str) {
    if !free_file_versions() {
        return;
    }
    PUBLISHED_PATHS.with(|paths| {
        let mut paths = paths.borrow_mut();
        if !paths.contains(path) {
            paths.insert(path.to_string());
        }
    });
}

/// The freeable rule: true when a new parse of `path` gets a
/// `FileVersion`, because `free_file_versions` is on and a publish on this
/// thread published `path` before.
pub(crate) fn freeable_path(path: &str) -> bool {
    free_file_versions() && PUBLISHED_PATHS.with(|paths| paths.borrow().contains(path))
}

/// The live versions of `files` (file ids). Static files and dead versions
/// have none.
pub(crate) fn live_file_versions(files: impl Iterator<Item = usize>) -> Vec<Arc<FileVersion>> {
    let weak: Vec<Weak<FileVersion>> = {
        let versions = lock(&VERSIONS);
        if versions.is_empty() {
            return Vec::new();
        }
        files
            .filter_map(|file| versions.get(&file).cloned())
            .collect()
    };
    // Upgraded after the lock ends: the last drop of a version locks it.
    weak.iter().filter_map(Weak::upgrade).collect()
}

/// A weak handle to a file version. Tests use it to see when the version
/// dies.
pub struct FileVersionProbe(Weak<FileVersion>);

impl FileVersionProbe {
    /// True once no holder has the version.
    #[must_use]
    pub fn is_freed(&self) -> bool {
        self.0.strong_count() == 0
    }
}

/// A probe of the version of the file of `node`. None for a static file
/// (tier 0, a first version, a CLI publish) or a dead version.
#[must_use]
pub fn file_version_probe(node: Node) -> Option<FileVersionProbe> {
    let weak = lock(&VERSIONS).get(&node.file_index()).cloned()?;
    (weak.strong_count() > 0).then_some(FileVersionProbe(weak))
}

/// The number of file versions made in this process.
#[must_use]
pub fn file_versions_made() -> usize {
    MADE.load(Ordering::Relaxed)
}

/// The number of dead file versions in this process.
#[must_use]
pub fn dead_file_versions() -> usize {
    DEAD_COUNT.load(Ordering::Acquire)
}

/// A thread-local map with per-file entries: each key is a node, and the
/// entry belongs to the file of that node. It forgets the entries of dead
/// file versions when it is next written (`write`). A read (`Deref`) can
/// still find such an entry before that. The store of a dead version is
/// still leaked, so the entry is still valid.
#[derive(Clone, Debug)]
pub(crate) struct PerFileMap<V> {
    /// `DEAD_COUNT` when the map last forgot dead entries.
    seen: usize,
    map: FxHashMap<Node, V>,
}

impl<V> PerFileMap<V> {
    pub(crate) const fn new() -> Self {
        Self {
            seen: 0,
            map: FxHashMap::with_hasher(rustc_hash::FxBuildHasher),
        }
    }

    /// The map for a write, after it forgets the entries of the file
    /// versions that died since its last write.
    // PERF: one atomic load. A process that frees no file version never
    // takes the cold path.
    #[inline]
    pub(crate) fn write(&mut self) -> &mut FxHashMap<Node, V> {
        if self.seen != DEAD_COUNT.load(Ordering::Acquire) {
            self.forget_dead();
        }
        &mut self.map
    }

    #[cold]
    #[inline(never)]
    fn forget_dead(&mut self) {
        if self.map.is_empty() {
            self.seen = DEAD_COUNT.load(Ordering::Acquire);
            return;
        }
        let dead: FxHashSet<usize> = {
            let dead = lock(&DEAD_FILES);
            let new = dead[self.seen..].iter().copied().collect();
            self.seen = dead.len();
            new
        };
        // After the lock ends: a dropped entry can hold a file version.
        self.map
            .retain(|node, _| !dead.contains(&node.file_index()));
    }
}

impl<V> Default for PerFileMap<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<V> Deref for PerFileMap<V> {
    type Target = FxHashMap<Node, V>;

    fn deref(&self) -> &FxHashMap<Node, V> {
        &self.map
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A node of file `file`. No test publishes the ids used here.
    fn node(file: usize) -> Node {
        Node(((file as u64) << 32) | 1)
    }

    // A map keeps the entries of a dead version until its next write, then
    // forgets them and keeps the entries of other files.
    #[test]
    fn per_file_map_forgets_dead_file_versions() {
        const DYING: usize = (1 << 22) - 1;
        const OTHER: usize = DYING - 1;
        let mut map = PerFileMap::new();
        map.write().insert(node(DYING), 1);
        map.write().insert(node(OTHER), 2);
        let version = FileVersion::new(DYING);
        let probe = file_version_probe(node(DYING)).expect("the registry has the version");

        drop(version);
        assert!(probe.is_freed());
        assert!(file_version_probe(node(DYING)).is_none());
        assert_eq!(map.get(&node(DYING)), Some(&1));
        map.write();
        assert_eq!(map.get(&node(DYING)), None);
        assert_eq!(map.get(&node(OTHER)), Some(&2));
    }
}
