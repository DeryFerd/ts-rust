//! Go: internal/vfs/trackingvfs/trackingvfs.go
//!
//! Package trackingvfs provides a VFS wrapper that records every file path
//! accessed during compilation. This allows watch mode to know exactly which
//! files and directories the compiler depended on, including non-existent
//! paths from failed module resolution.

use crate::frontend::prelude::*;
use std::time::SystemTime;

// Go: trackingvfs.go:17 FS
/// FS wraps a vfs.FS and records every path accessed via read-like operations.
/// Write operations (WriteFile, Remove, Chtimes) are not tracked since they
/// represent outputs, not dependencies.
///
/// PORT: Go `collections.SyncSet[string]` is a `RefCell<IndexSet<String>>`
/// (one thread). Go `SyncSet.ToSlice` ranges a `sync.Map`, so its order is
/// random; the port keeps insertion order.
pub struct FS {
    pub inner: Rc<dyn Fs>,
    pub seen_files: RefCell<IndexSet<String>>,
}

// Go: trackingvfs.go:22 `var _ vfs.FS = (*FS)(nil)`
impl Fs for FS {
    // Go: trackingvfs.go:34 (*FS).UseCaseSensitiveFileNames
    fn use_case_sensitive_file_names(&self) -> bool {
        self.inner.use_case_sensitive_file_names()
    }

    // Go: trackingvfs.go:29 (*FS).FileExists
    fn file_exists(&self, path: &str) -> bool {
        self.seen_files.borrow_mut().insert(path.to_string());
        self.inner.file_exists(path)
    }

    // Go: trackingvfs.go:24 (*FS).ReadFile
    fn read_file(&self, path: &str) -> (String, bool) {
        self.seen_files.borrow_mut().insert(path.to_string());
        self.inner.read_file(path)
    }

    // Go: trackingvfs.go:36 (*FS).WriteFile
    fn write_file(&self, path: &str, data: &str) -> Result<(), FsError> {
        self.inner.write_file(path, data)
    }

    // Go: trackingvfs.go:40 (*FS).AppendFile
    fn append_file(&self, path: &str, data: &str) -> Result<(), FsError> {
        self.inner.append_file(path, data)
    }

    // Go: trackingvfs.go:44 (*FS).Remove
    fn remove(&self, path: &str) -> Result<(), FsError> {
        self.inner.remove(path)
    }

    // Go: trackingvfs.go:46 (*FS).Chtimes
    fn chtimes(
        &self,
        path: &str,
        a_time: Option<SystemTime>,
        m_time: Option<SystemTime>,
    ) -> Result<(), FsError> {
        self.inner.chtimes(path, a_time, m_time)
    }

    // Go: trackingvfs.go:50 (*FS).DirectoryExists
    fn directory_exists(&self, path: &str) -> bool {
        self.seen_files.borrow_mut().insert(path.to_string());
        self.inner.directory_exists(path)
    }

    // Go: trackingvfs.go:55 (*FS).GetAccessibleEntries
    fn get_accessible_entries(&self, path: &str) -> Entries {
        self.seen_files.borrow_mut().insert(path.to_string());
        self.inner.get_accessible_entries(path)
    }

    // Go: trackingvfs.go:60 (*FS).Stat
    fn stat(&self, path: &str) -> Option<FileInfo> {
        self.seen_files.borrow_mut().insert(path.to_string());
        self.inner.stat(path)
    }

    // Go: trackingvfs.go:65 (*FS).WalkDir
    fn walk_dir(&self, root: &str, walk_fn: &mut WalkDirFunc<'_>) -> Result<(), FsError> {
        self.seen_files.borrow_mut().insert(root.to_string());
        self.inner.walk_dir(
            root,
            &mut |path: &str, d: Option<&DirEntry>, err: Option<FsError>| {
                self.seen_files.borrow_mut().insert(path.to_string());
                walk_fn(path, d, err)
            },
        )
    }

    // Go: trackingvfs.go:73 (*FS).Realpath
    fn realpath(&self, path: &str) -> String {
        self.seen_files.borrow_mut().insert(path.to_string());
        self.inner.realpath(path)
    }
}
