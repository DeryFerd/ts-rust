//! Rust-only: the owner and liveness of freeable file versions (lsshells
//! M3a, M3b, M3c).
//!
//! Go frees an `*ast.SourceFile` when no program and no parse cache entry
//! holds it (project/snapshot.go:537 `dispose`: `parseCache.Deref` for each
//! file of a released program). Here a static published file store is
//! leaked (`ast/store.rs`), so its id stays readable. A `FileVersion` gives
//! a file version the Go lifetime:
//! - its parse holds it (`ParsedSourceFile::version`), so each frontend
//!   program (`NewProgram`) and each parse cache entry that has the parse
//!   holds it;
//! - the tables of each program version that has the file hold it
//!   (`program::VersionTables`), so a checker, bind, emit or search thread
//!   that was seeded from that version holds it too (`WorkerSeed`);
//! - a thread that reads it pins it (`with_file_version`, `PINS`) until the
//!   next program release (`release_file_version_pins`) or its end;
//! - a `FileRef` guard holds it while the guard lives;
//! - the registry here keeps only a `Weak`.
//!
//! M3b: at publish the version takes its `FileStore` and its `GoFile`
//! (info, `node_bind`, `file_bind`, `flow_nodes`)
//! (`ast::store::VersionStore`). Its header columns (headers, kinds, names,
//! modifier bits, children, resolved) are leaked in its node shell, the
//! tier 1 publish of its id, so the header and child reads stay inline
//! (`ast::store::node_shell`); the child link column is dropped.
//! M3c (with `GOPORT_OWNED_NODES=1`; off by default, see
//! `owned_nodes_enabled`): its parse was a freeable parse
//! (`ast::enter_freeable_parse`), so its store owns its astdata nodes (node
//! structs and data boxes), its
//! pending lists and its parse lists (`ast::store::OwnedAst`), and they go
//! with the version. The node shell has no node column: a node data read
//! of the file is a scoped read of the pinned version
//! (`ast::with_scoped_store_node`), and a list of its node data is a handle
//! (`ast::StoreList`) that is read at each use.
//! M3d: the binder lineage binds the version into symbol and table chunks
//! of its own. After the version dies, the next bind frees them
//! (`program::Lineage`), and each program copy of the lineage lets go of
//! them when its release frees its tables (M2c, `program::bound_symbols`).
//! When the last holder lets go, the version is dead: its store and
//! `GoFile` are freed, its id goes to `DEAD_FILES`, and each per-file
//! thread-local map (`PerFileMap`) forgets the entries of that id when it
//! is next written. A later read of the id panics with "file version N is
//! released": ids are never reused, so a missed holder panics and never
//! reads another file.
//!
//! Freeable rule (`free_file_versions`, `freeable_path`): only a parse of
//! the language server parse cache (project/parsecache.rs), in a language
//! server or API process, of a path that a publish on this thread published
//! before. So tier 0, the first version of each file and every CLI publish
//! never get a `FileVersion`. `GOPORT_FREE_FILE_VERSIONS=0` turns it off
//! (the behavior before M3a); `=1` turns it on in any process, and then
//! `program::update_program_version` (`goport_multiprog`) applies the same
//! rule to its new parses (the compiler host opens the freeable parse scope
//! for them, M3c). A parse that a parse worker made (prefetch) keeps its
//! nodes in the leaked AST arena; its version still frees its store and
//! `GoFile`.

use super::store::VersionStore;
use crate::prelude::*;
use std::cell::Cell;
use std::ops::Deref;
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, OnceLock, PoisonError, Weak};

/// The owner of one freeable file version. It is `Send + Sync`: a program
/// version's tables carry it to worker threads.
pub struct FileVersion {
    /// The file id (the store id).
    file: usize,
    /// The store and `GoFile` of the version, set by the publish (M3b).
    published: OnceLock<VersionStore>,
    /// Go `SourceFile.nameTable` of this version (ast.go:2532 to 2543;
    /// `ast::source_file_get_name_table`). A static file keeps it in the
    /// thread-local `NAME_TABLES` (node.rs).
    pub(crate) name_table: OnceLock<FxHashMap<String, i32>>,
    /// Go `SourceFile.positionMap` (`ast::source_file_get_position_map`).
    pub(crate) position_map: OnceLock<PositionMap>,
    /// Go `SourceFile.declarationMap`
    /// (`ast::source_file_get_declaration_map`).
    pub(crate) declaration_map: OnceLock<FxHashMap<String, Vec<Node>>>,
}

impl std::fmt::Debug for FileVersion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FileVersion")
            .field("file", &self.file)
            .field("published", &self.published.get().is_some())
            .finish()
    }
}

impl FileVersion {
    /// The owner of file version `file`, registered in the registry. The
    /// language server parse cache makes it (`freeable_path`).
    pub(crate) fn new(file: usize) -> Arc<Self> {
        let version = Arc::new(FileVersion {
            file,
            published: OnceLock::new(),
            name_table: OnceLock::new(),
            position_map: OnceLock::new(),
            declaration_map: OnceLock::new(),
        });
        lock(&VERSIONS).insert(file, Arc::downgrade(&version));
        MADE.fetch_add(1, Ordering::Relaxed);
        version
    }

    /// The file id (the store id) of this version.
    #[must_use]
    pub fn file(&self) -> usize {
        self.file
    }

    /// Gives the version its published store and `GoFile`
    /// (`publish_file_stores`). Panics when it has them already.
    pub(crate) fn set_published(&self, store: VersionStore) {
        FREEABLE_PUBLISHED.store(true, Ordering::Release);
        assert!(
            self.published.set(store).is_ok(),
            "file version {} is already published",
            self.file
        );
    }

    /// The published store and `GoFile`, or `None` before the publish.
    #[inline]
    pub(crate) fn published(&self) -> Option<&VersionStore> {
        self.published.get()
    }

    /// The `GoFile` of this version. Panics before the publish. A
    /// `FileRef::Pinned` getter starts here.
    #[inline]
    #[must_use]
    pub fn go_file(&self) -> &GoFile {
        match self.published.get() {
            Some(store) => store.go_file(),
            None => panic!("file version {} is not published", self.file),
        }
    }
}

impl Drop for FileVersion {
    // The store and `GoFile` (`published`) are freed after this, with the
    // fields.
    fn drop(&mut self) {
        // The id is dead before the registry entry goes, so a reader that
        // still finds the entry and cannot upgrade it panics (`released`).
        {
            let mut dead = lock(&DEAD_FILES);
            dead.push(self.file);
            DEAD_COUNT.store(dead.len(), Ordering::Release);
        }
        // File ids are never reused, so the entry is this version's.
        lock(&VERSIONS).remove(&self.file);
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

/// Set when the first freeable version is published. Until then a registry
/// read (`frozen!` in `ast/store.rs`) never looks for a version.
static FREEABLE_PUBLISHED: AtomicBool = AtomicBool::new(false);

/// Raised by each program release (`release_file_version_pins`). A thread
/// whose pins are from an older epoch drops them at its next pinned read.
static PIN_EPOCH: AtomicUsize = AtomicUsize::new(0);

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

/// True once a freeable version is published in this process. A CLI
/// process never sets it, so its registry reads never look for a version.
#[inline]
pub(crate) fn any_freeable_published() -> bool {
    FREEABLE_PUBLISHED.load(Ordering::Acquire)
}

/// True when `file` was a freeable version that died.
// PERF: a scan, on the path of a read that found no live version only.
fn is_dead_file(file: usize) -> bool {
    lock(&DEAD_FILES).contains(&file)
}

/// Panics for a read of dead file version `file`.
#[cold]
#[inline(never)]
fn released(file: usize) -> ! {
    panic!("file version {file} is released")
}

/// A pin of a file version on one thread: the `Arc` in a thread-local
/// `Rc`. The pins of a thread (`PINS`) and the `FileRef` guards that it
/// made share it.
// PERF: lsshells M3 repair. A guard clones and drops the `Rc` (no atomic
// write); a flow walk of the edited file makes one guard per flow node, and
// an `Arc` clone per guard made query-core edits about 0.3 ms slower.
pub type VersionPin = Rc<Arc<FileVersion>>;

/// The pins of one thread: the versions it read since the last program
/// release (`PIN_EPOCH`), by file id.
struct Pins {
    epoch: usize,
    // PERF: a thread reads few freeable versions (the edited files), so a
    // scan is faster than a map.
    list: Vec<(usize, VersionPin)>,
    /// The index in `list` of the last hit, tested before the scan.
    // PERF: lsshells M3 repair. Most pinned reads in a row are of one file
    // (the edited file).
    last: Cell<usize>,
}

impl Pins {
    /// The pinned version `file` of the current epoch.
    #[inline]
    fn find(&self, file: usize) -> Option<&VersionPin> {
        if self.epoch != PIN_EPOCH.load(Ordering::Acquire) {
            return None;
        }
        match self.list.get(self.last.get()) {
            Some((id, version)) if *id == file => Some(version),
            _ => self.find_scan(file),
        }
    }

    /// `find` after a miss of the last hit.
    #[inline(never)]
    fn find_scan(&self, file: usize) -> Option<&VersionPin> {
        let index = self.list.iter().position(|(id, _)| *id == file)?;
        self.last.set(index);
        Some(&self.list[index].1)
    }
}

thread_local! {
    /// The file versions this thread pinned (`with_file_version`).
    static PINS: RefCell<Pins> = const {
        RefCell::new(Pins {
            epoch: 0,
            list: Vec::new(),
            last: Cell::new(0),
        })
    };
}

/// Runs `read` on the live version `file`, pinned on this thread. `None`
/// when `file` is no live version (a static, synthetic or unknown id).
/// Panics when `file` was a freeable version that died: a stale read never
/// reads other data. `ast::store` calls it only after the static tiers
/// missed.
// PERF: a hit is a thread-local borrow, an epoch compare and a short scan,
// with no atomic write. `read` runs while the pins are borrowed, so a read
// inside `read` that misses runs with its own `Arc` and pins nothing.
#[inline]
pub(crate) fn with_file_version<R>(file: usize, read: impl FnOnce(&FileVersion) -> R) -> Option<R> {
    let mut read = Some(read);
    let hit = PINS
        .try_with(|pins| {
            let pins = pins.try_borrow().ok()?;
            let version = pins.find(file)?;
            let read = read.take()?;
            Some(read(&**version))
        })
        .ok()
        .flatten();
    if hit.is_some() {
        return hit;
    }
    // The closure took `read` only on a hit.
    let read = read.take()?;
    let version = pin_file_version(file)?;
    Some(read(&**version))
}

/// The live version `file`, pinned on this thread, as a pin that a
/// `FileRef` guard keeps. `None` and panics as `with_file_version`.
pub(crate) fn pinned_file_version(file: usize) -> Option<VersionPin> {
    let hit = PINS
        .try_with(|pins| {
            let pins = pins.try_borrow().ok()?;
            pins.find(file).map(Rc::clone)
        })
        .ok()
        .flatten();
    match hit {
        Some(version) => Some(version),
        None => pin_file_version(file),
    }
}

/// The pin miss: the version from the registry, added to this thread's
/// pins (after the pins of an older epoch are dropped).
#[cold]
#[inline(never)]
fn pin_file_version(file: usize) -> Option<VersionPin> {
    let weak = lock(&VERSIONS).get(&file).cloned();
    // Upgraded after the lock ends: the last drop of a version locks it.
    let Some(version) = weak.and_then(|weak| weak.upgrade()) else {
        if is_dead_file(file) {
            released(file);
        }
        return None;
    };
    let version = Rc::new(version);
    let expired = PINS
        .try_with(|pins| {
            let mut pins = pins.try_borrow_mut().ok()?;
            let epoch = PIN_EPOCH.load(Ordering::Acquire);
            let expired = if pins.epoch == epoch {
                Vec::new()
            } else {
                pins.epoch = epoch;
                std::mem::take(&mut pins.list)
            };
            pins.list.push((file, Rc::clone(&version)));
            pins.last.set(pins.list.len() - 1);
            Some(expired)
        })
        .ok()
        .flatten();
    // Dropped after the borrow ends: the last pin of a version frees it.
    drop(expired);
    Some(version)
}

/// Drops the pins of this thread and makes every other thread drop its
/// pins at its next pinned read. A program release calls it
/// (`program::ReleasedProgram`), so a version that only the released
/// program read dies with its other holders. The versions that the live
/// programs read are pinned again on their next read.
pub fn release_file_version_pins() {
    PIN_EPOCH.fetch_add(1, Ordering::AcqRel);
    let pins = PINS
        .try_with(|pins| {
            let mut pins = pins.try_borrow_mut().ok()?;
            Some(std::mem::take(&mut pins.list))
        })
        .ok()
        .flatten();
    // Dropped after the borrow ends.
    drop(pins);
}

/// A borrow of per-file data (lsshells M3b), the return type of the file
/// data accessors (`ast::go_file`, `ast::source_file_info`,
/// `FlowNodeId::get_flow`, ...). It derefs to the data.
/// - `Static`: a file that is never freed (tier 0, tier 1, synthetic or
///   leaked data). `as_static` gives the `'static` borrow.
/// - `Pinned`: a freeable file version. The guard holds the version (a
///   thread-local pin, `VersionPin`, so a guard stays on its thread), and
///   the data lives while the guard does. `get(version, key)` finds the
///   data; it is a plain function (no captures), `key` is its argument (a
///   slot or flow index, or 0).
///
/// Keep a guard only as long as the data is needed: a kept guard keeps its
/// file version alive. To keep a value past the guard, copy or clone it.
pub enum FileRef<T: ?Sized + 'static> {
    Static(&'static T),
    Pinned {
        version: VersionPin,
        key: usize,
        get: fn(&FileVersion, usize) -> &T,
    },
}

impl<T: ?Sized + 'static> FileRef<T> {
    /// The `'static` borrow of a static file, or `None` for a pinned
    /// version.
    #[inline]
    #[must_use]
    pub fn as_static(&self) -> Option<&'static T> {
        match self {
            FileRef::Static(value) => Some(value),
            FileRef::Pinned { .. } => None,
        }
    }

    /// The file version that a pinned guard holds, or `None` for a static
    /// file.
    #[must_use]
    pub fn version(&self) -> Option<&VersionPin> {
        match self {
            FileRef::Static(_) => None,
            FileRef::Pinned { version, .. } => Some(version),
        }
    }
}

impl<T: ?Sized + 'static> Deref for FileRef<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        match self {
            FileRef::Static(value) => value,
            FileRef::Pinned { version, key, get } => get(&**version, *key),
        }
    }
}

impl<T: ?Sized + 'static> Clone for FileRef<T> {
    fn clone(&self) -> Self {
        match self {
            FileRef::Static(value) => FileRef::Static(value),
            FileRef::Pinned { version, key, get } => FileRef::Pinned {
                version: Rc::clone(version),
                key: *key,
                get: *get,
            },
        }
    }
}

impl<T: 'static> Default for FileRef<[T]> {
    /// An empty static list.
    fn default() -> Self {
        FileRef::Static(&[])
    }
}

impl<T: ?Sized + std::fmt::Debug + 'static> std::fmt::Debug for FileRef<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (**self).fmt(f)
    }
}

/// `FileRef` to `$part` of the `GoFile` of published file `$file` (a file
/// id). `$part` is a place expression of `$g` (the `GoFile`) and `$k` (the
/// value of `$key`; name it `_key` when `$part` does not use it). It is
/// written once and used for both variants, so it must not capture anything
/// else. Panics when `$file` is not published.
// PORT: a `FileRef::Pinned` getter must be a plain function, so the part is
// repeated in a non-capturing closure.
macro_rules! go_file_ref {
    ($file:expr, $key:expr, |$g:ident, $k:ident| $part:expr) => {{
        let key: usize = $key;
        match $crate::ast::go_file($file) {
            $crate::ast::FileRef::Static($g) => {
                let $k = key;
                $crate::ast::FileRef::Static(&$part)
            }
            $crate::ast::FileRef::Pinned { version, .. } => $crate::ast::FileRef::Pinned {
                version,
                key,
                get: |version, $k| {
                    let $g = version.go_file();
                    &$part
                },
            },
        }
    }};
}
pub(crate) use go_file_ref;

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

/// The ids of the file versions that died after the first `seen` dead ones,
/// in the order they died, and the number of dead versions now. The binder
/// lineage frees their symbol chunks (`program::Lineage`, lsshells M3d).
pub(crate) fn dead_files_since(seen: usize) -> (Vec<usize>, usize) {
    let dead = lock(&DEAD_FILES);
    (dead[seen.min(dead.len())..].to_vec(), dead.len())
}

/// A thread-local map with per-file entries: each key is a node, and the
/// entry belongs to the file of that node. It forgets the entries of dead
/// file versions when it is next written (`write`). A read (`Deref`) can
/// still find such an entry before that; its value is owned by the map, so
/// it is still valid, but a key of a dead version is never read again.
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
