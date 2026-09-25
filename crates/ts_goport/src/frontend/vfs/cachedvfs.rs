//! Go: internal/vfs/cachedvfs/cachedvfs.go

use crate::prelude::*;
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
