//! Go `internal/project/snapshotfs.go`.
//!
//! PORT: one thread (project/dirty/interfaces.rs). Go mutexes are dropped.
//! `collections.SyncMap` / `SyncSet` are `RefCell<FxHashMap>` /
//! `RefCell<FxHashSet>`; `collections.Set` is `FxHashSet`. A shared Go
//! `*collections.SyncSet` is `Rc<RefCell<FxHashSet>>` (nil is `None`). Go
//! `func(fileName string) tspath.Path` is `Rc<dyn Fn(&str) -> tspath::Path>`.
//! Overlay maps are `IndexMap` (see overlayfs.rs). Go `xxh3.Uint128` is
//! `u128`.

use crate::project::prelude::*;

use std::cell::{Cell, OnceCell};
use std::time::SystemTime;
use xxhash_rust::xxh3::xxh3_128;

// Go: project/snapshotfs.go:19 FileSource
pub trait FileSource {
    fn fs(&self) -> Rc<dyn vfs::Fs>;
    fn get_file(&self, file_name: &str) -> Option<Rc<dyn FileHandle>>;
    fn get_file_by_path(&self, file_name: &str, path: &tspath::Path) -> Option<Rc<dyn FileHandle>>;
    fn file_exists(&self, file_name: &str, path: &tspath::Path) -> bool;
    fn get_accessible_entries(&self, path: &str) -> vfs::Entries;

    /// Go `source.FS().UseCaseSensitiveFileNames()`. A released source
    /// (`SourceFS::release`) answers it with no file system.
    // PORT: not in Go.
    fn use_case_sensitive_file_names(&self) -> bool {
        self.fs().use_case_sensitive_file_names()
    }
}

// Go: project/snapshotfs.go:34 realpathAliasSet
// realpathAliasSet is a thread-safe set of symlink paths that alias a single realpath.
// It implements dirty.Cloneable so it can be used as a value in dirty.SyncMap.
// PORT: `mu` is dropped. Go `*realpathAliasSet` is `Rc<RefCell<..>>`.
#[derive(Debug, Default)]
pub struct RealpathAliasSet {
    pub paths: FxHashSet<tspath::Path>,
}

impl RealpathAliasSet {
    // Go: project/snapshotfs.go:39 realpathAliasSet.Add
    pub fn add(&mut self, path: tspath::Path) {
        self.paths.insert(path);
    }

    // Go: project/snapshotfs.go:45 realpathAliasSet.Clone
    // PORT: Go `Clone`; `clone_` keeps it apart from `std::clone::Clone`.
    pub fn clone_(&self) -> Rc<RefCell<RealpathAliasSet>> {
        let mut clone = RealpathAliasSet::default();
        if !self.paths.is_empty() {
            clone.paths = self.paths.clone();
        }
        Rc::new(RefCell::new(clone))
    }
}

impl dirty::Cloneable for Rc<RefCell<RealpathAliasSet>> {
    fn clone_(&self) -> Self {
        self.borrow().clone_()
    }
}

// Go: project/snapshotfs.go:55 SnapshotFS
// PORT: Go shares `diskFiles`, `diskDirectories` and
// `nodeModulesRealpathAliases` between snapshots until one of them changes
// (a Go map is a reference). They are `Rc` maps here, so a snapshot clone
// with no disk change copies no map, and dropping an old snapshot frees
// nothing that the next one still uses.
pub struct SnapshotFS {
    pub to_path: Rc<dyn Fn(&str) -> tspath::Path>,
    pub fs: Rc<dyn vfs::Fs>,
    pub overlays: IndexMap<tspath::Path, Rc<Overlay>>,
    pub overlay_directories: FxHashMap<tspath::Path, FxHashMap<tspath::Path, String>>,
    pub disk_files: Rc<FxHashMap<tspath::Path, Rc<RefCell<DiskFile>>>>,
    pub disk_directories: Rc<FxHashMap<tspath::Path, dirty::CloneableMap<tspath::Path, String>>>,
    pub read_files: RefCell<FxHashMap<tspath::Path, MemoizedDiskFile>>,
    // nodeModulesRealpathAliases maps realpath-based keys to sets of symlink-based keys,
    // for files inside node_modules that are accessed through directory symlinks.
    // This allows watch events (which use realpaths) to invalidate files cached under symlink paths.
    pub node_modules_realpath_aliases: Rc<FxHashMap<tspath::Path, Rc<RefCell<RealpathAliasSet>>>>,
}

// Go: project/snapshotfs.go:69 memoizedDiskFile
// PORT: Go `func() FileHandle` made by `sync.OnceValue`; the closure keeps
// its value in a `OnceCell`.
pub type MemoizedDiskFile = Rc<dyn Fn() -> Option<Rc<dyn FileHandle>>>;

impl SnapshotFS {
    // Go: project/snapshotfs.go:118 SnapshotFS.isOpenFile
    pub fn is_open_file(&self, file_name: &str) -> bool {
        let path = (self.to_path)(file_name);
        self.overlays.contains_key(&path)
    }

    // Go: project/snapshotfs.go:124 SnapshotFS.isFile
    pub fn is_file(&self, path: &tspath::Path) -> bool {
        if self.disk_files.contains_key(path) {
            return true;
        }
        if self.overlays.contains_key(path) {
            return true;
        }
        false
    }

    // Go: project/snapshotfs.go:489 SnapshotFS.expandRealpathAliases
    // expandRealpathAliases adds synthetic URIs to the Changed and Deleted sets for
    // files that were accessed through node_modules symlinks. When a watch event arrives
    // using a realpath, this expands it to include the symlink-based path so that
    // downstream consumers (markDirtyFiles, markFilesChanged) can find cached entries.
    pub fn expand_realpath_aliases(&self, mut change: FileChangeSummary) -> FileChangeSummary {
        if self.node_modules_realpath_aliases.is_empty() {
            return change;
        }

        let mut additional_changed: FxHashSet<lsproto::DocumentUri> = FxHashSet::default();
        for uri in &change.changed {
            let path = (self.to_path)(&uri.file_name());
            if let Some(aliases) = self.node_modules_realpath_aliases.get(&path) {
                for alias_path in &aliases.borrow().paths {
                    additional_changed.insert(lsconv::file_name_to_document_uri(alias_path));
                }
            }
        }
        for uri in additional_changed {
            change.changed.insert(uri);
        }

        let mut additional_deleted: FxHashSet<lsproto::DocumentUri> = FxHashSet::default();
        for uri in &change.deleted {
            let path = (self.to_path)(&uri.file_name());
            if let Some(aliases) = self.node_modules_realpath_aliases.get(&path) {
                for alias_path in &aliases.borrow().paths {
                    additional_deleted.insert(lsconv::file_name_to_document_uri(alias_path));
                }
            }
        }
        for uri in additional_deleted {
            change.deleted.insert(uri);
        }

        change
    }
}

// Go: project/snapshotfs.go:29 `_ FileSource = (*SnapshotFS)(nil)`
impl FileSource for SnapshotFS {
    // Go: project/snapshotfs.go:71 SnapshotFS.FS
    fn fs(&self) -> Rc<dyn vfs::Fs> {
        self.fs.clone()
    }

    // Go: project/snapshotfs.go:75 SnapshotFS.GetFile
    fn get_file(&self, file_name: &str) -> Option<Rc<dyn FileHandle>> {
        self.get_file_by_path(file_name, &(self.to_path)(file_name))
    }

    // Go: project/snapshotfs.go:89 SnapshotFS.GetFileByPath
    fn get_file_by_path(&self, file_name: &str, path: &tspath::Path) -> Option<Rc<dyn FileHandle>> {
        if let Some(file) = self.overlays.get(path) {
            return Some(file.clone());
        }
        if let Some(file) = self.disk_files.get(path) {
            return Some(file.clone());
        }
        let fs = self.fs.clone();
        let file_name = file_name.to_string();
        let value: OnceCell<Option<Rc<dyn FileHandle>>> = OnceCell::new();
        let new_entry: MemoizedDiskFile = Rc::new(move || {
            value
                .get_or_init(|| -> Option<Rc<dyn FileHandle>> {
                    let (contents, ok) = fs.read_file(&file_name);
                    if ok {
                        return Some(new_disk_file(&file_name, contents));
                    }
                    None
                })
                .clone()
        });
        // Go: s.readFiles.LoadOrStore(path, newEntry)
        let entry = self
            .read_files
            .borrow_mut()
            .entry(path.clone())
            .or_insert(new_entry)
            .clone();
        entry()
    }

    // Go: project/snapshotfs.go:79 SnapshotFS.FileExists
    fn file_exists(&self, file_name: &str, path: &tspath::Path) -> bool {
        if self.overlays.contains_key(path) {
            return true;
        }
        if self.disk_files.contains_key(path) {
            return true;
        }
        self.fs.file_exists(file_name)
    }

    // Go: project/snapshotfs.go:106 SnapshotFS.GetAccessibleEntries
    fn get_accessible_entries(&self, directory_name: &str) -> vfs::Entries {
        let mut entries = vfs::Entries::default();
        let path = (self.to_path)(directory_name);
        if let Some(disk_directories) = self.disk_directories.get(&path) {
            read_directory_into_entries(
                &disk_directories.borrow(),
                &|p: &tspath::Path| self.is_file(p),
                &mut entries,
            );
        }
        if let Some(overlay_directories) = self.overlay_directories.get(&path) {
            read_directory_into_entries(
                overlay_directories,
                &|p: &tspath::Path| self.is_file(p),
                &mut entries,
            );
        }
        entries
    }
}

// Go: project/snapshotfs.go:134 snapshotFSBuilder
pub struct SnapshotFSBuilder {
    pub fs: Rc<dyn vfs::Fs>,
    pub prev_overlays: IndexMap<tspath::Path, Rc<Overlay>>,
    pub overlays: IndexMap<tspath::Path, Rc<Overlay>>,
    pub overlay_directories: FxHashMap<tspath::Path, FxHashMap<tspath::Path, String>>,
    pub disk_files: Rc<dirty::SyncMap<tspath::Path, Rc<RefCell<DiskFile>>>>,
    pub disk_directories: Rc<dirty::Map<tspath::Path, dirty::CloneableMap<tspath::Path, String>>>,
    pub node_modules_realpath_aliases:
        Rc<dirty::SyncMap<tspath::Path, Rc<RefCell<RealpathAliasSet>>>>,
    pub to_path: Rc<dyn Fn(&str) -> tspath::Path>,
    pub accessible_entries: RefCell<FxHashMap<tspath::Path, vfs::Entries>>,
}

// Go: project/snapshotfs.go:145 newSnapshotFSBuilder
// PORT: the base maps are shared `Rc` maps, as Go shares its maps (no
// copy). `position_encoding` is unused, as in Go.
#[allow(clippy::too_many_arguments)]
pub fn new_snapshot_fs_builder(
    fs: Rc<dyn vfs::Fs>,
    prev_overlays: IndexMap<tspath::Path, Rc<Overlay>>,
    overlays: IndexMap<tspath::Path, Rc<Overlay>>,
    disk_files: Rc<FxHashMap<tspath::Path, Rc<RefCell<DiskFile>>>>,
    disk_directories: Rc<FxHashMap<tspath::Path, dirty::CloneableMap<tspath::Path, String>>>,
    node_modules_realpath_aliases: Rc<FxHashMap<tspath::Path, Rc<RefCell<RealpathAliasSet>>>>,
    _position_encoding: lsproto::PositionEncodingKind,
    to_path: Rc<dyn Fn(&str) -> tspath::Path>,
) -> Rc<SnapshotFSBuilder> {
    let cached_fs = vfs::cachedvfs_from(fs);
    cached_fs.enable();

    let mut overlay_directories: FxHashMap<tspath::Path, FxHashMap<tspath::Path, String>> =
        FxHashMap::default();
    for (path, overlay) in &overlays {
        let mut child_path = path.clone();
        let mut child = overlay.file_base.file_name.clone();
        loop {
            let parent_path = child_path.get_directory_path();
            let parent = tspath::get_directory_path(&child);
            if child_path == parent_path {
                break; // reached root
            }
            let base_name = tspath::get_base_file_name(&child);
            if let Some(dir) = overlay_directories.get_mut(&parent_path) {
                dir.insert(child_path.clone(), base_name);
            } else {
                let mut dir: FxHashMap<tspath::Path, String> = FxHashMap::default();
                dir.insert(child_path.clone(), base_name);
                overlay_directories.insert(parent_path.clone(), dir);
            }
            child_path = parent_path;
            child = parent;
        }
    }

    Rc::new(SnapshotFSBuilder {
        fs: cached_fs,
        prev_overlays,
        overlays,
        overlay_directories,
        disk_files: dirty::new_sync_map_shared(disk_files),
        disk_directories: dirty::new_map_shared(disk_directories),
        node_modules_realpath_aliases: dirty::new_sync_map_shared(node_modules_realpath_aliases),
        to_path,
        accessible_entries: RefCell::default(),
    })
}

// Go: project/snapshotfs.go:227 onDeletedFileOrDirectory (a closure in Finalize)
// PORT: the recursive Go closure is a nested function over the map it reads.
fn on_deleted_file_or_directory(
    disk_directories: &dirty::Map<tspath::Path, dirty::CloneableMap<tspath::Path, String>>,
    path: &tspath::Path,
) {
    let (dir_entry, ok) = disk_directories.get(&path.get_directory_path());
    if !ok {
        return;
    }
    let dir_entry = dir_entry.expect("dirty.Map.Get: ok implies an entry");
    let entry = dir_entry.clone();
    dir_entry.change(&mut |dir: &dirty::CloneableMap<tspath::Path, String>| {
        dir.borrow_mut().remove(path);
        if dir.borrow().is_empty() {
            entry.delete();
            on_deleted_file_or_directory(disk_directories, &entry.key());
        }
    });
}

impl SnapshotFSBuilder {
    // Go: project/snapshotfs.go:197 snapshotFSBuilder.Finalize
    pub fn finalize(&self) -> (Rc<SnapshotFS>, bool) {
        // Synchronize directory structure based on added and deleted files (including overlays)
        let mut deleted: Option<FxHashMap<tspath::Path, Option<Rc<RefCell<DiskFile>>>>> = None;

        let on_added_file = |path: &tspath::Path, file_name: &str| {
            let mut child_path = path.clone();
            let mut child = file_name.to_string();
            loop {
                let parent_path = child_path.get_directory_path();
                let parent = tspath::get_directory_path(&child);
                if child_path == parent_path {
                    break; // reached root
                }
                let base_name = tspath::get_base_file_name(&child);
                if let (Some(dir_entry), true) = self.disk_directories.get(&parent_path) {
                    dir_entry.change(&mut |dir: &dirty::CloneableMap<tspath::Path, String>| {
                        dir.borrow_mut()
                            .insert(child_path.clone(), base_name.clone());
                    });
                    break;
                } else {
                    let dir: dirty::CloneableMap<tspath::Path, String> =
                        dirty::CloneableMap::default();
                    dir.borrow_mut().insert(child_path.clone(), base_name);
                    self.disk_directories.add(parent_path.clone(), dir);
                }
                child_path = parent_path;
                child = parent;
            }
        };

        let mut on_delete = |key: &tspath::Path, value: Option<&Rc<RefCell<DiskFile>>>| {
            deleted
                .get_or_insert_with(FxHashMap::default)
                .insert(key.clone(), value.cloned());
        };
        let mut on_add = |key: &tspath::Path, value: Option<&Rc<RefCell<DiskFile>>>| {
            let file_name = value
                .expect("invalid memory address or nil pointer dereference")
                .borrow()
                .file_base
                .file_name();
            on_added_file(key, &file_name);
        };
        // Go: s.diskFiles.FinalizeWith(...) (PORT: the shared form)
        let (disk_files, changed) = self.disk_files.finalize_shared(dirty::FinalizationHooks {
            on_delete: Some(&mut on_delete),
            on_change: None,
            on_add: Some(&mut on_add),
        });

        // PORT: Go ranges over the `deleted` map (random order); the result
        // does not depend on the order.
        for path in deleted.iter().flat_map(|d| d.keys()) {
            on_deleted_file_or_directory(&self.disk_directories, path);
        }

        // Prune deleted symlink paths from realpath alias sets before finalizing,
        // so that empty sets are dropped during finalization.
        for (deleted_path, deleted_file) in deleted.iter().flatten() {
            let realpath_path = deleted_file
                .as_ref()
                .expect("invalid memory address or nil pointer dereference")
                .borrow()
                .realpath_path
                .clone();
            if realpath_path.0.is_empty() {
                continue;
            }
            if let (Some(entry), true) = self.node_modules_realpath_aliases.load(&realpath_path) {
                entry.locked(&mut |e: &dyn dirty::Value<Rc<RefCell<RealpathAliasSet>>>| {
                    e.change(&mut |alias_set: &Rc<RefCell<RealpathAliasSet>>| {
                        alias_set.borrow_mut().paths.remove(deleted_path);
                    });
                    let is_empty = e
                        .value()
                        .expect("invalid memory address or nil pointer dereference")
                        .borrow()
                        .paths
                        .is_empty();
                    if is_empty {
                        e.delete();
                    }
                });
            }
        }

        // Go: s.nodeModulesRealpathAliases.Finalize() (PORT: the shared form)
        let (node_modules_realpath_aliases, aliases_changed) = self
            .node_modules_realpath_aliases
            .finalize_shared(dirty::FinalizationHooks::default());

        (
            Rc::new(SnapshotFS {
                fs: self.fs.clone(),
                overlays: self.overlays.clone(),
                overlay_directories: self.overlay_directories.clone(),
                disk_files,
                // Go: core.FirstResult(s.diskDirectories.Finalize())
                disk_directories: self.disk_directories.finalize_shared().0,
                read_files: RefCell::new(FxHashMap::default()),
                node_modules_realpath_aliases,
                to_path: self.to_path.clone(),
            }),
            changed || aliases_changed,
        )
    }

    // Go: project/snapshotfs.go:288 snapshotFSBuilder.isOpenFile
    pub fn is_open_file(&self, path: &tspath::Path) -> bool {
        self.overlays.contains_key(path)
    }

    // Go: project/snapshotfs.go:332 snapshotFSBuilder.getDiskFile
    pub fn get_disk_file(
        &self,
        file_name: &str,
        path: &tspath::Path,
        force_reload: bool,
    ) -> Option<Rc<dyn FileHandle>> {
        let (entry, loaded) = self.disk_files.load_or_store(
            path.clone(),
            Rc::new(RefCell::new(DiskFile {
                file_base: FileBase {
                    file_name: file_name.to_string(),
                    ..FileBase::default()
                },
                needs_reload: true,
                ..DiskFile::default()
            })),
        );
        if let Some(entry) = entry {
            if !loaded && path.0.contains("/node_modules/") {
                self.record_realpath_alias(&entry, file_name, path);
            }
            if force_reload {
                return self.reload_entry(&entry);
            }
            return self.reload_entry_if_needed(&entry);
        }
        None
    }

    // Go: project/snapshotfs.go:349 snapshotFSBuilder.recordRealpathAlias
    // recordRealpathAlias checks if fileName is accessed through a symlink and, if so,
    // records a mapping from the realpath-based key to the symlink-based key.
    // This is only called for files inside node_modules where symlinks are common.
    pub fn record_realpath_alias(
        &self,
        disk_file_entry: &Rc<dirty::SyncMapEntry<tspath::Path, Rc<RefCell<DiskFile>>>>,
        symlink_file_name: &str,
        symlink_path: &tspath::Path,
    ) {
        let realpath = self.fs.realpath(symlink_file_name);
        let realpath_path = (self.to_path)(&realpath);
        if realpath_path != *symlink_path {
            disk_file_entry.change(&mut |file: &Rc<RefCell<DiskFile>>| {
                file.borrow_mut().realpath_path = realpath_path.clone();
            });
            let (entry, _) = self.node_modules_realpath_aliases.load_or_store(
                realpath_path.clone(),
                Rc::new(RefCell::new(RealpathAliasSet::default())),
            );
            entry
                .expect("invalid memory address or nil pointer dereference")
                .change(&mut |alias_set: &Rc<RefCell<RealpathAliasSet>>| {
                    alias_set.borrow_mut().add(symlink_path.clone());
                });
        }
    }

    // Go: project/snapshotfs.go:363 snapshotFSBuilder.reloadEntry
    pub fn reload_entry(
        &self,
        entry: &Rc<dirty::SyncMapEntry<tspath::Path, Rc<RefCell<DiskFile>>>>,
    ) -> Option<Rc<dyn FileHandle>> {
        let mut file_name = String::new();
        entry.locked(&mut |e: &dyn dirty::Value<Rc<RefCell<DiskFile>>>| {
            if let Some(value) = e.value() {
                file_name = value.borrow().file_base.file_name.clone();
            }
        });
        if file_name.is_empty() {
            return None;
        }
        // Read file outside the lock to avoid blocking other goroutines.
        let (content, ok) = self.fs.read_file(&file_name);
        entry.locked(&mut |e: &dyn dirty::Value<Rc<RefCell<DiskFile>>>| {
            if e.value().is_none() {
                return;
            }
            if ok {
                e.change(&mut |file: &Rc<RefCell<DiskFile>>| {
                    let mut file = file.borrow_mut();
                    file.file_base.content = content.clone();
                    file.file_base.hash.set(xxh3_128(content.as_bytes()));
                    file.needs_reload = false;
                });
            } else {
                e.delete();
            }
        });
        let value = entry.value()?;
        Some(value)
    }

    // Go: project/snapshotfs.go:395 snapshotFSBuilder.reloadEntryIfNeeded
    pub fn reload_entry_if_needed(
        &self,
        entry: &Rc<dirty::SyncMapEntry<tspath::Path, Rc<RefCell<DiskFile>>>>,
    ) -> Option<Rc<dyn FileHandle>> {
        let mut file_name = String::new();
        entry.locked(&mut |e: &dyn dirty::Value<Rc<RefCell<DiskFile>>>| {
            if let Some(value) = e.value() {
                let value = value.borrow();
                if !value.matches_disk_text() {
                    file_name = value.file_base.file_name.clone();
                }
            }
        });
        if !file_name.is_empty() {
            // Read file outside the lock to avoid blocking other goroutines.
            let (content, ok) = self.fs.read_file(&file_name);
            entry.locked(&mut |e: &dyn dirty::Value<Rc<RefCell<DiskFile>>>| {
                match e.value() {
                    None => return, // another goroutine already reloaded it
                    Some(value) if value.borrow().matches_disk_text() => return,
                    Some(_) => {}
                }
                if ok {
                    e.change(&mut |file: &Rc<RefCell<DiskFile>>| {
                        let mut file = file.borrow_mut();
                        file.file_base.content = content.clone();
                        file.file_base.hash.set(xxh3_128(content.as_bytes()));
                        file.needs_reload = false;
                    });
                } else {
                    e.delete();
                }
            });
        }
        let value = entry.value()?;
        Some(value)
    }

    // Go: project/snapshotfs.go:426 snapshotFSBuilder.watchChangesOverlapCache
    // PORT: Go passes the summary by value; here by reference.
    pub fn watch_changes_overlap_cache(&self, change: &FileChangeSummary) -> bool {
        for uri in &change.changed {
            let path = (self.to_path)(&uri.file_name());
            if let (_, true) = self.disk_files.load(&path) {
                return true;
            }
            if let (_, true) = self.node_modules_realpath_aliases.load(&path) {
                return true;
            }
        }
        for uri in &change.deleted {
            let path = (self.to_path)(&uri.file_name());
            if let (_, true) = self.disk_files.load(&path) {
                return true;
            }
            if let (_, true) = self.node_modules_realpath_aliases.load(&path) {
                return true;
            }
        }
        false
    }

    // Go: project/snapshotfs.go:448 snapshotFSBuilder.invalidateCache
    pub fn invalidate_cache(&self) {
        self.disk_files.range(&mut |entry: &Rc<
            dirty::SyncMapEntry<tspath::Path, Rc<RefCell<DiskFile>>>,
        >| {
            entry.change(&mut |file: &Rc<RefCell<DiskFile>>| {
                file.borrow_mut().needs_reload = true;
            });
            true
        });
    }

    // Go: project/snapshotfs.go:457 snapshotFSBuilder.invalidateNodeModulesCache
    pub fn invalidate_node_modules_cache(&self) {
        self.disk_files.range(&mut |entry: &Rc<
            dirty::SyncMapEntry<tspath::Path, Rc<RefCell<DiskFile>>>,
        >| {
            if entry.key().0.contains("/node_modules/") {
                entry.change(&mut |file: &Rc<RefCell<DiskFile>>| {
                    file.borrow_mut().needs_reload = true;
                });
            }
            true
        });
    }

    // Go: project/snapshotfs.go:480 snapshotFSBuilder.markDirtyFiles
    // PORT: Go reloads the changed disk files in a work group; the port
    // reloads them one after another (one thread). The result is a set, so
    // the order does not matter.
    pub fn mark_dirty_files(&self, mut change: FileChangeSummary) -> FileChangeSummary {
        if !change.changed.is_empty() {
            let mut filtered_changed: FxHashSet<lsproto::DocumentUri> = FxHashSet::default();
            for uri in &change.changed {
                let path = (self.to_path)(&uri.file_name());
                if self.overlays.contains_key(&path) {
                    filtered_changed.insert(uri.clone());
                    continue;
                }
                let (Some(entry), true) = self.disk_files.load(&path) else {
                    filtered_changed.insert(uri.clone());
                    continue;
                };
                if self.reload_entry_if_content_changed(&entry) {
                    filtered_changed.insert(uri.clone());
                }
            }
            change.changed = filtered_changed;
        }
        for uri in &change.deleted {
            let path = (self.to_path)(&uri.file_name());
            if let (Some(entry), true) = self.disk_files.load(&path) {
                entry.delete();
            }
        }
        change
    }

    // Go: project/snapshotfs.go:517 snapshotFSBuilder.reloadEntryIfContentChanged
    // PORT: Go named result `(changed bool)`.
    pub fn reload_entry_if_content_changed(
        &self,
        entry: &Rc<dirty::SyncMapEntry<tspath::Path, Rc<RefCell<DiskFile>>>>,
    ) -> bool {
        let Some(file) = entry.value() else {
            return true;
        };
        let file_name = file.borrow().file_base.file_name.clone();
        let (content, ok) = self.fs.read_file(&file_name);
        let mut changed = true;
        entry.locked(&mut |e: &dyn dirty::Value<Rc<RefCell<DiskFile>>>| {
            let Some(cur) = e.value() else {
                return;
            };
            if !ok {
                e.delete();
                return;
            }
            if content == cur.borrow().file_base.content {
                changed = false;
                if !cur.borrow().matches_disk_text() {
                    e.change(&mut |file: &Rc<RefCell<DiskFile>>| {
                        file.borrow_mut().needs_reload = false;
                    });
                }
                return;
            }
            e.change(&mut |file: &Rc<RefCell<DiskFile>>| {
                let mut file = file.borrow_mut();
                file.file_base.content = content.clone();
                file.file_base.hash.set(xxh3_128(content.as_bytes()));
                file.needs_reload = false;
            });
        });
        changed
    }

    // Go: project/snapshotfs.go:592 snapshotFSBuilder.isRelevantFileName
    // isRelevantFileName returns true if the given URI refers to a file that
    // could affect the project: it has a TypeScript-relevant extension, is a
    // dynamic (e.g. untitled) file, or is currently open as an overlay.
    pub fn is_relevant_file_name(&self, uri: &lsproto::DocumentUri) -> bool {
        let file_name = uri.file_name();
        if tspath::is_dynamic_file_name(&file_name) {
            return true;
        }
        let path = (self.to_path)(&file_name);
        if self.overlays.contains_key(&path) {
            return true;
        }
        let Some(i) = path.0.rfind('.') else {
            return false;
        };
        is_relevant_extension(&path.0[i..])
    }

    // Go: project/snapshotfs.go:550 snapshotFSBuilder.expandAndFilterWatchEvents
    // expandAndFilterWatchEvents expands directory deletion URIs into individual
    // file deletion URIs using the cached directory structure, and filters out
    // watch events for paths that are neither known directories nor have relevant
    // file extensions.
    pub fn expand_and_filter_watch_events(
        &self,
        mut change: FileChangeSummary,
    ) -> FileChangeSummary {
        if !change.deleted.is_empty() {
            let mut filtered_deleted: FxHashSet<lsproto::DocumentUri> = FxHashSet::default();
            for uri in &change.deleted {
                let path = (self.to_path)(&uri.file_name());
                if let (_, true) = self.disk_directories.get(&path) {
                    self.collect_files_recursive(&path, &mut filtered_deleted);
                } else if self.is_relevant_file_name(uri) || is_node_modules_path(&path) {
                    // node_modules deletions must always be preserved for auto-import registry change handlers.
                    // They won't be in diskDirectories since the registry doesn't use the snapshotFSBuilder for
                    // its file system, since we don't want to retain files read there.
                    filtered_deleted.insert(uri.clone());
                }
            }
            change.deleted = filtered_deleted;
        }

        if !change.changed.is_empty() {
            let mut filtered_changed: FxHashSet<lsproto::DocumentUri> = FxHashSet::default();
            for uri in &change.changed {
                if self.is_relevant_file_name(uri) {
                    filtered_changed.insert(uri.clone());
                }
            }
            change.changed = filtered_changed;
        }

        // We can't filter created events because any created path could be a directory symlink
        // that includes relevant files. configFileRegistryBuilder will do check if these paths
        // are directories if they fall within a config's wildcard directories.

        change
    }

    // Go: project/snapshotfs.go:594 snapshotFSBuilder.collectFilesRecursive
    // collectFilesRecursive recursively collects all cached file URIs under the
    // given directory path using the diskDirectories and diskFiles maps.
    pub fn collect_files_recursive(
        &self,
        dir_path: &tspath::Path,
        files: &mut FxHashSet<lsproto::DocumentUri>,
    ) {
        let (dir_entry, ok) = self.disk_directories.get(dir_path);
        if !ok {
            return;
        }
        // PORT: the child paths are copied out before the recursion. Go
        // ranges over a nil map when the entry has no value.
        let child_paths: Vec<tspath::Path> = match dir_entry.and_then(|dir_entry| dir_entry.value())
        {
            Some(dir) => dir.borrow().keys().cloned().collect(),
            None => Vec::new(),
        };
        for child_path in &child_paths {
            if let (Some(entry), true) = self.disk_files.load(child_path) {
                if let Some(file) = entry.value() {
                    files.insert(lsconv::file_name_to_document_uri(
                        &file.borrow().file_base.file_name(),
                    ));
                }
            }
            self.collect_files_recursive(child_path, files);
        }
    }

    // Go: project/snapshotfs.go:609 snapshotFSBuilder.convertOpenAndCloseToChanges
    pub fn convert_open_and_close_to_changes(
        &self,
        mut change: FileChangeSummary,
    ) -> FileChangeSummary {
        if !change.opened.0.is_empty() && !tspath::is_dynamic_file_name(&change.opened.file_name())
        {
            let path = (self.to_path)(&change.opened.file_name());
            let (entry, ok) = self.disk_files.load(&path);
            let original = entry.as_ref().and_then(|entry| entry.original());
            if !ok || original.is_none() {
                change.created.insert(change.opened.clone());
            } else if let Some(overlay) = self.overlays.get(&path) {
                // The file already exists in the program, but the overlay content from
                // didOpen may differ from what was originally read from disk (e.g. the
                // editor normalizes line endings, or the file changed on disk since the
                // project was loaded). Mark it as Changed so the project rebuilds.
                if let Some(disk_file) = original {
                    if overlay.file_base.hash() != disk_file.borrow().file_base.hash() {
                        change.changed.insert(change.opened.clone());
                    }
                }
            }
        }
        for uri in &change.closed {
            let file_name = uri.file_name();
            if tspath::is_dynamic_file_name(&file_name) {
                continue;
            }
            let path = (self.to_path)(&file_name);
            // We may have ignored watcher events while the file was open, so force a reload.
            if let Some(fh) = self.get_disk_file(&file_name, &path, true /*forceReload*/) {
                let prev_hash = self
                    .prev_overlays
                    .get(&path)
                    .expect("invalid memory address or nil pointer dereference")
                    .file_base
                    .hash();
                if fh.hash() != prev_hash {
                    change.changed.insert(uri.clone());
                }
                continue;
            }
            change.deleted.insert(uri.clone());
        }
        change
    }
}

// Go: project/snapshotfs.go:28 `_ FileSource = (*snapshotFSBuilder)(nil)`
impl FileSource for SnapshotFSBuilder {
    // Go: project/snapshotfs.go:193 snapshotFSBuilder.FS
    fn fs(&self) -> Rc<dyn vfs::Fs> {
        self.fs.clone()
    }

    // Go: project/snapshotfs.go:293 snapshotFSBuilder.GetFile
    fn get_file(&self, file_name: &str) -> Option<Rc<dyn FileHandle>> {
        let path = (self.to_path)(file_name);
        self.get_file_by_path(file_name, &path)
    }

    // Go: project/snapshotfs.go:314 snapshotFSBuilder.GetFileByPath
    fn get_file_by_path(&self, file_name: &str, path: &tspath::Path) -> Option<Rc<dyn FileHandle>> {
        if let Some(file) = self.overlays.get(path) {
            return Some(file.clone());
        }
        self.get_disk_file(file_name, path, false)
    }

    // Go: project/snapshotfs.go:298 snapshotFSBuilder.FileExists
    fn file_exists(&self, file_name: &str, path: &tspath::Path) -> bool {
        if self.overlays.contains_key(path) {
            return true;
        }
        if let (Some(entry), true) = self.disk_files.load(path) {
            let val = entry.value();
            if val.is_none() {
                return false;
            }
            // Entry may be dirty - reload to check current state on disk.
            return self.reload_entry_if_needed(&entry).is_some();
        }
        // Path never loaded into diskFiles - use cached stat (no file read).
        self.fs.file_exists(file_name)
    }

    // Go: project/snapshotfs.go:321 snapshotFSBuilder.GetAccessibleEntries
    fn get_accessible_entries(&self, path: &str) -> vfs::Entries {
        let entries = self.fs.get_accessible_entries(path);
        let p = (self.to_path)(path);
        let Some(overlay_directories) = self.overlay_directories.get(&p) else {
            return entries;
        };

        if let Some(merged) = self.accessible_entries.borrow().get(&p) {
            return merged.clone();
        }
        let mut merged = entries;
        read_directory_into_entries(
            overlay_directories,
            &|p: &tspath::Path| self.is_open_file(p),
            &mut merged,
        );
        // Go: LoadOrStore
        self.accessible_entries
            .borrow_mut()
            .entry(p)
            .or_insert(merged)
            .clone()
    }
}

// Go: project/snapshotfs.go:616 isRelevantExtension
// isRelevantExtension returns true if the given extension is a known TypeScript
// or JavaScript extension that can affect the project.
pub fn is_relevant_extension(ext: &str) -> bool {
    matches!(
        ext,
        ".js" | ".jsx" | ".mjs" | ".cjs" | ".ts" | ".tsx" | ".mts" | ".cts" | ".json"
    )
}

// Go: project/snapshotfs.go:665 isNodeModulesPath
// isNodeModulesPath reports whether path is a node_modules directory itself or
// lives inside one. Used to preserve node_modules watch deletions, whose package
// files are read transiently and therefore never tracked in diskDirectories.
pub fn is_node_modules_path(path: &tspath::Path) -> bool {
    let s = path.as_str();
    s.ends_with("/node_modules") || s.contains("/node_modules/")
}

// Go: project/snapshotfs.go:643 sourceFS
// sourceFS is a vfs.FS that sources files from a FileSource and tracks seen files.
// PORT: Go `*sourceFS` is shared (`Rc<SourceFS>`, also as `Rc<dyn vfs::Fs>`).
// Go writes `tracking`, `seenFiles` and `source` after sharing, so they are
// `Cell` / `RefCell`.
pub struct SourceFS {
    pub tracking: Cell<bool>,
    pub to_path: Rc<dyn Fn(&str) -> tspath::Path>,
    pub missing_directories: Option<Rc<RefCell<FxHashSet<tspath::Path>>>>,
    pub seen_files: RefCell<Option<Rc<RefCell<FxHashSet<tspath::Path>>>>>,
    pub source: RefCell<Rc<dyn FileSource>>,
}

// Go: project/snapshotfs.go:651 newSourceFS
pub fn new_source_fs(
    tracking: bool,
    source: Rc<dyn FileSource>,
    to_path: Rc<dyn Fn(&str) -> tspath::Path>,
) -> Rc<SourceFS> {
    let mut fs = SourceFS {
        tracking: Cell::new(tracking),
        to_path,
        missing_directories: None,
        seen_files: RefCell::new(None),
        source: RefCell::new(source),
    };
    if tracking {
        fs.seen_files = RefCell::new(Some(Rc::new(RefCell::new(FxHashSet::default()))));
        fs.missing_directories = Some(Rc::new(RefCell::new(FxHashSet::default())));
    }
    Rc::new(fs)
}

impl SourceFS {
    /// Go `fs.source` (read). The handle is copied so no borrow is held
    /// while the source runs.
    fn source(&self) -> Rc<dyn FileSource> {
        self.source.borrow().clone()
    }

    // Go: project/snapshotfs.go:666 sourceFS.DisableTracking
    pub fn disable_tracking(&self) {
        self.tracking.set(false);
    }

    // Go: project/snapshotfs.go:670 sourceFS.Track
    pub fn track(&self, file_name: &str) {
        if !self.tracking.get() {
            return;
        }
        let path = (self.to_path)(file_name);
        self.seen_files
            .borrow()
            .as_ref()
            .expect("invalid memory address or nil pointer dereference")
            .borrow_mut()
            .insert(path);
    }

    // Go: project/snapshotfs.go:677 sourceFS.SeenFile
    pub fn seen_file(&self, path: &tspath::Path) -> bool {
        let seen_files = self.seen_files.borrow();
        let Some(seen_files) = seen_files.as_ref() else {
            return false;
        };
        let seen = seen_files.borrow().contains(path);
        seen
    }

    // Go: project/snapshotfs.go:684 sourceFS.SeenFileOrMissingParentDirectory
    pub fn seen_file_or_missing_parent_directory(&self, path: &tspath::Path) -> bool {
        if let Some(seen_files) = self.seen_files.borrow().as_ref() {
            if seen_files.borrow().contains(path) {
                return true;
            }
        }
        if let Some(missing_directories) = &self.missing_directories {
            let missing_directories = missing_directories.borrow();
            if !missing_directories.is_empty() {
                let mut path = path.clone();
                loop {
                    if missing_directories.contains(&path) {
                        return true;
                    }

                    let parent = path.get_directory_path();
                    if parent == path {
                        break;
                    }
                    path = parent;
                }
            }
        }
        false
    }

    // Go: project/snapshotfs.go:704 sourceFS.GetFile
    pub fn get_file(&self, file_name: &str) -> Option<Rc<dyn FileHandle>> {
        self.track(file_name);
        self.source().get_file(file_name)
    }

    // Go: project/snapshotfs.go:709 sourceFS.GetFileByPath
    pub fn get_file_by_path(
        &self,
        file_name: &str,
        path: &tspath::Path,
    ) -> Option<Rc<dyn FileHandle>> {
        self.track(file_name);
        self.source().get_file_by_path(file_name, path)
    }

    /// Drops the file source and the tracked sets when the host of this file
    /// system is released (`compiler::CompilerHost::release`). Only the case
    /// sensitivity stays, so a file name lookup on a released program still
    /// works (Go `Program.GetSourceFile` makes a path first). Any file
    /// access panics after this. `seen_files` can be shared with the host of
    /// a program cloned from this host's program; only this reference goes.
    // PORT: not in Go. Go's GC frees the `sourceFS` with its host.
    pub fn release(&self) {
        self.tracking.set(false);
        let released: Rc<dyn FileSource> = Rc::new(ReleasedFileSource {
            use_case_sensitive_file_names: self.source().use_case_sensitive_file_names(),
        });
        // PORT: the old values drop after the borrows end.
        let source = std::mem::replace(&mut *self.source.borrow_mut(), released);
        let seen_files = self.seen_files.borrow_mut().take();
        let missing_directories = self
            .missing_directories
            .as_ref()
            .map(|missing| std::mem::take(&mut *missing.borrow_mut()));
        drop(source);
        drop(seen_files);
        drop(missing_directories);
    }
}

/// The file source of a released `SourceFS` (`SourceFS::release`). It keeps
/// only the case sensitivity; every file access panics.
// PORT: not in Go.
struct ReleasedFileSource {
    use_case_sensitive_file_names: bool,
}

fn released_file_source_used() -> ! {
    panic!("the file system of a released program's compiler host was used");
}

impl FileSource for ReleasedFileSource {
    fn fs(&self) -> Rc<dyn vfs::Fs> {
        released_file_source_used()
    }

    fn get_file(&self, _file_name: &str) -> Option<Rc<dyn FileHandle>> {
        released_file_source_used()
    }

    fn get_file_by_path(
        &self,
        _file_name: &str,
        _path: &tspath::Path,
    ) -> Option<Rc<dyn FileHandle>> {
        released_file_source_used()
    }

    fn file_exists(&self, _file_name: &str, _path: &tspath::Path) -> bool {
        released_file_source_used()
    }

    fn get_accessible_entries(&self, _path: &str) -> vfs::Entries {
        released_file_source_used()
    }

    fn use_case_sensitive_file_names(&self) -> bool {
        self.use_case_sensitive_file_names
    }
}

// Go: project/snapshotfs.go:664 `var _ vfs.FS = (*sourceFS)(nil)`
impl vfs::Fs for SourceFS {
    // Go: project/snapshotfs.go:753 sourceFS.UseCaseSensitiveFileNames
    // UseCaseSensitiveFileNames implements vfs.FS.
    fn use_case_sensitive_file_names(&self) -> bool {
        // PORT: through the source, so a released source can answer it
        // (`SourceFS::release`).
        self.source().use_case_sensitive_file_names()
    }

    // Go: project/snapshotfs.go:724 sourceFS.FileExists
    // FileExists implements vfs.FS.
    fn file_exists(&self, path: &str) -> bool {
        self.track(path);
        self.source().file_exists(path, &(self.to_path)(path))
    }

    // Go: project/snapshotfs.go:735 sourceFS.ReadFile
    // ReadFile implements vfs.FS.
    fn read_file(&self, path: &str) -> (String, bool) {
        if let Some(fh) = self.get_file(path) {
            return (fh.content(), true);
        }
        (String::new(), false)
    }

    // Go: project/snapshotfs.go:763 sourceFS.WriteFile
    // WriteFile implements vfs.FS.
    fn write_file(&self, _path: &str, _data: &str) -> Result<(), vfs::FsError> {
        panic!("unimplemented");
    }

    // Go: project/snapshotfs.go:768 sourceFS.AppendFile
    // AppendFile implements vfs.FS.
    fn append_file(&self, _path: &str, _data: &str) -> Result<(), vfs::FsError> {
        panic!("unimplemented");
    }

    // Go: project/snapshotfs.go:773 sourceFS.Remove
    // Remove implements vfs.FS.
    fn remove(&self, _path: &str) -> Result<(), vfs::FsError> {
        panic!("unimplemented");
    }

    // Go: project/snapshotfs.go:778 sourceFS.Chtimes
    // Chtimes implements vfs.FS.
    fn chtimes(
        &self,
        _path: &str,
        _a_time: Option<SystemTime>,
        _m_time: Option<SystemTime>,
    ) -> Result<(), vfs::FsError> {
        panic!("unimplemented");
    }

    // Go: project/snapshotfs.go:715 sourceFS.DirectoryExists
    // DirectoryExists implements vfs.FS.
    fn directory_exists(&self, path: &str) -> bool {
        let exists = self.source().fs().directory_exists(path);
        if !exists && self.tracking.get() {
            self.missing_directories
                .as_ref()
                .expect("invalid memory address or nil pointer dereference")
                .borrow_mut()
                .insert((self.to_path)(path));
        }
        exists
    }

    // Go: project/snapshotfs.go:730 sourceFS.GetAccessibleEntries
    // GetAccessibleEntries implements vfs.FS.
    fn get_accessible_entries(&self, path: &str) -> vfs::Entries {
        self.source().get_accessible_entries(path)
    }

    // Go: project/snapshotfs.go:748 sourceFS.Stat
    // Stat implements vfs.FS.
    fn stat(&self, path: &str) -> Option<vfs::FileInfo> {
        self.source().fs().stat(path)
    }

    // Go: project/snapshotfs.go:758 sourceFS.WalkDir
    // WalkDir implements vfs.FS.
    fn walk_dir(&self, root: &str, walk_fn: &mut vfs::WalkDirFunc<'_>) -> Result<(), vfs::FsError> {
        self.source().fs().walk_dir(root, walk_fn)
    }

    // Go: project/snapshotfs.go:743 sourceFS.Realpath
    // Realpath implements vfs.FS.
    fn realpath(&self, path: &str) -> String {
        self.source().fs().realpath(path)
    }
}

// Go: project/snapshotfs.go:782 readDirectoryIntoEntries
// PORT: Go is generic over `~map[tspath.Path]string`; both maps are
// `FxHashMap` here (a `dirty::CloneableMap` is borrowed). Go ranges over the
// map (random order).
pub fn read_directory_into_entries(
    directories: &FxHashMap<tspath::Path, String>,
    is_file: &dyn Fn(&tspath::Path) -> bool,
    entries: &mut vfs::Entries,
) {
    for (child_path, child_name) in directories {
        if is_file(child_path) {
            entries.files.push(child_name.clone());
        } else {
            entries.directories.push(child_name.clone());
        }
    }
}
