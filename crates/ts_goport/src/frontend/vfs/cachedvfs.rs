//! Go: internal/vfs/cachedvfs/cachedvfs.go

use crate::frontend::prelude::*;
use std::cell::Cell;
use std::time::SystemTime;

// Go: cachedvfs.go:11 FS
// PORT: the Go type `cachedvfs.FS` is `CachedFs`. `atomic.Bool` and
// `collections.SyncMap` become `Cell` and `RefCell<FxHashMap>` (the port is
// single-threaded). The stat cache stores Go nil results as `None`.
pub struct CachedFs {
    fs: Rc<dyn Fs>,
    enabled: Cell<bool>,

    directory_exists_cache: RefCell<FxHashMap<String, bool>>,
    file_exists_cache: RefCell<FxHashMap<String, bool>>,
    get_accessible_entries_cache: RefCell<FxHashMap<String, Entries>>,
    realpath_cache: RefCell<FxHashMap<String, String>>,
    stat_cache: RefCell<FxHashMap<String, Option<FileInfo>>>,
}

// Go: cachedvfs.go:24 From
// PORT: the Go package function `cachedvfs.From` is `cachedvfs_from`.
pub fn cachedvfs_from(fs: Rc<dyn Fs>) -> Rc<CachedFs> {
    let fsys = CachedFs {
        fs,
        enabled: Cell::new(false),
        directory_exists_cache: RefCell::default(),
        file_exists_cache: RefCell::default(),
        get_accessible_entries_cache: RefCell::default(),
        realpath_cache: RefCell::default(),
        stat_cache: RefCell::default(),
    };
    fsys.enabled.set(true);
    Rc::new(fsys)
}

// PORT: the Go `SyncMap.Load`. The value is cloned so no borrow is held
// while the wrapped file system runs.
fn cache_load<V: Clone>(cache: &RefCell<FxHashMap<String, V>>, key: &str) -> Option<V> {
    cache.borrow().get(key).cloned()
}

impl CachedFs {
    // Go: cachedvfs.go:30 DisableAndClearCache
    pub fn disable_and_clear_cache(&self) {
        if self.enabled.get() {
            self.enabled.set(false);
            self.clear_cache();
        }
    }

    // Go: cachedvfs.go:36 Enable
    pub fn enable(&self) {
        self.enabled.set(true);
    }

    // Go: cachedvfs.go:40 ClearCache
    pub fn clear_cache(&self) {
        self.directory_exists_cache.borrow_mut().clear();
        self.file_exists_cache.borrow_mut().clear();
        self.get_accessible_entries_cache.borrow_mut().clear();
        self.realpath_cache.borrow_mut().clear();
        self.stat_cache.borrow_mut().clear();
    }
}

// PORT: not in Go. Go `tsc -b` runs every project of a build cycle on one
// cached file system (build/orchestrator.go:618). goport_build compiles
// each project in its own worker process (build-mode plan D1), so the
// orchestrator hands its cache to each worker and merges back what the
// worker added. `CachedFsState` is the content of the five caches.
#[derive(Clone, Debug, Default)]
pub struct CachedFsState {
    pub directory_exists: FxHashMap<String, bool>,
    pub file_exists: FxHashMap<String, bool>,
    pub get_accessible_entries: FxHashMap<String, Entries>,
    pub realpath: FxHashMap<String, String>,
    pub stat: FxHashMap<String, Option<FileInfo>>,
}

impl CachedFsState {
    pub fn is_empty(&self) -> bool {
        self.directory_exists.is_empty()
            && self.file_exists.is_empty()
            && self.get_accessible_entries.is_empty()
            && self.realpath.is_empty()
            && self.stat.is_empty()
    }
}

// The entries of `cache` whose key is in none of `excluded`.
fn entries_excluding<V: Clone>(
    cache: &RefCell<FxHashMap<String, V>>,
    excluded: &[&FxHashMap<String, V>],
) -> FxHashMap<String, V> {
    cache
        .borrow()
        .iter()
        .filter(|(key, _)| !excluded.iter().any(|map| map.contains_key(*key)))
        .map(|(key, value)| (key.clone(), value.clone()))
        .collect()
}

// Adds the entries of `state` that `cache` does not have. A lookup that is
// already cached is not replaced: it was made first.
fn load_entries<V: Clone>(cache: &RefCell<FxHashMap<String, V>>, state: &FxHashMap<String, V>) {
    let mut cache = cache.borrow_mut();
    for (key, value) in state {
        if !cache.contains_key(key) {
            cache.insert(key.clone(), value.clone());
        }
    }
}

impl CachedFs {
    // PORT: not in Go (see `CachedFsState`). The cached entries whose key is
    // in none of `excluded`: after `load_state(base)`, `state_excluding(&[base])`
    // is what this cache added.
    pub fn state_excluding(&self, excluded: &[&CachedFsState]) -> CachedFsState {
        CachedFsState {
            directory_exists: entries_excluding(
                &self.directory_exists_cache,
                &excluded
                    .iter()
                    .map(|state| &state.directory_exists)
                    .collect::<Vec<_>>(),
            ),
            file_exists: entries_excluding(
                &self.file_exists_cache,
                &excluded
                    .iter()
                    .map(|state| &state.file_exists)
                    .collect::<Vec<_>>(),
            ),
            get_accessible_entries: entries_excluding(
                &self.get_accessible_entries_cache,
                &excluded
                    .iter()
                    .map(|state| &state.get_accessible_entries)
                    .collect::<Vec<_>>(),
            ),
            realpath: entries_excluding(
                &self.realpath_cache,
                &excluded.iter().map(|state| &state.realpath).collect::<Vec<_>>(),
            ),
            stat: entries_excluding(
                &self.stat_cache,
                &excluded.iter().map(|state| &state.stat).collect::<Vec<_>>(),
            ),
        }
    }

    // PORT: not in Go (see `CachedFsState`). All cached entries.
    pub fn state(&self) -> CachedFsState {
        self.state_excluding(&[])
    }

    // PORT: not in Go (see `CachedFsState`). Adds the entries of `state`
    // that are not cached yet. Does nothing when the cache is disabled.
    pub fn load_state(&self, state: &CachedFsState) {
        if !self.enabled.get() {
            return;
        }
        load_entries(&self.directory_exists_cache, &state.directory_exists);
        load_entries(&self.file_exists_cache, &state.file_exists);
        load_entries(
            &self.get_accessible_entries_cache,
            &state.get_accessible_entries,
        );
        load_entries(&self.realpath_cache, &state.realpath);
        load_entries(&self.stat_cache, &state.stat);
    }
}

impl Fs for CachedFs {
    // Go: cachedvfs.go:48 DirectoryExists
    fn directory_exists(&self, path: &str) -> bool {
        if self.enabled.get() {
            if let Some(ret) = cache_load(&self.directory_exists_cache, path) {
                return ret;
            }
        }

        let ret = self.fs.directory_exists(path);

        if self.enabled.get() {
            self.directory_exists_cache
                .borrow_mut()
                .insert(path.to_string(), ret);
        }

        ret
    }

    // Go: cachedvfs.go:64 FileExists
    fn file_exists(&self, path: &str) -> bool {
        if self.enabled.get() {
            if let Some(ret) = cache_load(&self.file_exists_cache, path) {
                return ret;
            }
        }

        let ret = self.fs.file_exists(path);

        if self.enabled.get() {
            self.file_exists_cache
                .borrow_mut()
                .insert(path.to_string(), ret);
        }

        ret
    }

    // Go: cachedvfs.go:80 GetAccessibleEntries
    fn get_accessible_entries(&self, path: &str) -> Entries {
        if self.enabled.get() {
            if let Some(ret) = cache_load(&self.get_accessible_entries_cache, path) {
                return ret;
            }
        }

        let ret = self.fs.get_accessible_entries(path);

        if self.enabled.get() {
            self.get_accessible_entries_cache
                .borrow_mut()
                .insert(path.to_string(), ret.clone());
        }

        ret
    }

    // Go: cachedvfs.go:96 ReadFile
    fn read_file(&self, path: &str) -> (String, bool) {
        self.fs.read_file(path)
    }

    // Go: cachedvfs.go:100 Realpath
    fn realpath(&self, path: &str) -> String {
        if self.enabled.get() {
            if let Some(ret) = cache_load(&self.realpath_cache, path) {
                return ret;
            }
        }

        let ret = self.fs.realpath(path);

        if self.enabled.get() {
            self.realpath_cache
                .borrow_mut()
                .insert(path.to_string(), ret.clone());
        }

        ret
    }

    // Go: cachedvfs.go:116 Remove
    fn remove(&self, path: &str) -> Result<(), FsError> {
        self.fs.remove(path)
    }

    // Go: cachedvfs.go:120 Chtimes
    fn chtimes(
        &self,
        path: &str,
        a_time: Option<SystemTime>,
        m_time: Option<SystemTime>,
    ) -> Result<(), FsError> {
        self.fs.chtimes(path, a_time, m_time)
    }

    // Go: cachedvfs.go:124 Stat
    fn stat(&self, path: &str) -> Option<FileInfo> {
        if self.enabled.get() {
            if let Some(ret) = cache_load(&self.stat_cache, path) {
                return ret;
            }
        }

        let ret = self.fs.stat(path);

        if self.enabled.get() {
            self.stat_cache
                .borrow_mut()
                .insert(path.to_string(), ret.clone());
        }

        ret
    }

    // Go: cachedvfs.go:140 UseCaseSensitiveFileNames
    fn use_case_sensitive_file_names(&self) -> bool {
        self.fs.use_case_sensitive_file_names()
    }

    // Go: cachedvfs.go:144 WalkDir
    fn walk_dir(&self, root: &str, walk_fn: &mut WalkDirFunc<'_>) -> Result<(), FsError> {
        self.fs.walk_dir(root, walk_fn)
    }

    // Go: cachedvfs.go:148 WriteFile
    fn write_file(&self, path: &str, data: &str) -> Result<(), FsError> {
        self.fs.write_file(path, data)
    }

    // Go: cachedvfs.go:152 AppendFile
    fn append_file(&self, path: &str, data: &str) -> Result<(), FsError> {
        self.fs.append_file(path, data)
    }
}
