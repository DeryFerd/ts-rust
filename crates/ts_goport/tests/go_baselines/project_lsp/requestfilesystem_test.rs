//! Port of Go `internal/api/requestfilesystem/requestfilesystem_test.go`
//! (ts#64115, ts#64277, ts#64291, ts#64391), with the test helpers that
//! `pathtree_test.go` and `filechanges_test.go` also use.
//!
//! PORT: the Go tests are in package `requestfilesystem` and read its
//! unexported names. The port's names are public (`RequestFileSystemImpl`
//! is Go `requestFileSystem`), so the tests are here, next to
//! `projecttestutil` and `support::vfstest`.
//!
//! PORT: Go `newRequestFileSystem` returns the `*requestFileSystem` of
//! `NewForUpdate`. The port keeps the `vfs.FS` handle (a later layer takes it
//! as its base), and `imp` is the Go pointer. Go pointer compares of file
//! systems (`fs.baseFileSystem() == host`) are `Rc::ptr_eq`.
//!
//! PORT: Go `assert.DeepEqual` of a `vfs.Entries` tells a nil slice from an
//! empty one. A Rust `Vec` has no nil, so only the map of symlinks keeps that
//! difference (`Option`).

use std::cell::Cell;
use std::collections::BTreeSet;
use std::fmt::Debug;
use std::rc::Rc;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use rustc_hash::FxHashMap;
use ts_goport::api::requestfilesystem::{
    Kind, RequestDirectoryEntries, RequestFileSystem, RequestFileSystemImpl, RequestSymlink,
    get_request_file_system, new_for_update,
};
use ts_goport::frontend::tspath;
use ts_goport::frontend::vfs::{self, Fs, trackingvfs};
use ts_goport::gostd::GoError;
use ts_goport::project;

use super::projecttestutil::{self, files as project_files};
use super::util::*;
use crate::support::vfstest::{self, MapFile};

/// Go `assert.NilError(t, err)` on a result.
pub(crate) fn nil_error<T>(result: Result<T, GoError>) -> T {
    result.unwrap_or_else(|err| panic!("unexpected error: {}", err.error()))
}

/// Go `assert.ErrorContains(t, err, text)`.
fn error_contains<T>(result: Result<T, GoError>, text: &str) {
    match result {
        Ok(_) => panic!("expected an error containing {text:?}"),
        Err(err) => assert!(
            err.error().contains(text),
            "error {:?} does not contain {text:?}",
            err.error()
        ),
    }
}

/// Go `map[string]string{...}` of `RequestFileSystem.Files`.
pub(crate) fn files(entries: &[(&str, &str)]) -> FxHashMap<String, String> {
    entries
        .iter()
        .map(|(name, content)| (name.to_string(), content.to_string()))
        .collect()
}

/// Go `RequestDirectoryEntries{Files: files, Directories: directories}`.
pub(crate) fn listing(files: &[&str], directories: &[&str]) -> RequestDirectoryEntries {
    RequestDirectoryEntries {
        files: files.iter().map(|name| name.to_string()).collect(),
        directories: directories.iter().map(|name| name.to_string()).collect(),
    }
}

/// Go `map[string]RequestDirectoryEntries{...}`.
pub(crate) fn directories(
    entries: Vec<(&str, RequestDirectoryEntries)>,
) -> FxHashMap<String, RequestDirectoryEntries> {
    entries
        .into_iter()
        .map(|(name, entries)| (name.to_string(), entries))
        .collect()
}

/// Go `map[string]RequestSymlink{name: {Target: target, Host: host}}`.
pub(crate) fn symlinks(entries: &[(&str, &str, bool)]) -> FxHashMap<String, RequestSymlink> {
    entries
        .iter()
        .map(|(name, target, host)| {
            (
                name.to_string(),
                RequestSymlink {
                    target: target.to_string(),
                    host: *host,
                },
            )
        })
        .collect()
}

/// Go `[]string{...}` of `RequestFileSystem.RemovedPaths`.
pub(crate) fn removed(paths: &[&str]) -> Vec<String> {
    paths.iter().map(|path| path.to_string()).collect()
}

/// Go `&RequestFileSystem{Kind: kind}`.
pub(crate) fn request(kind: Kind) -> RequestFileSystem {
    RequestFileSystem {
        kind,
        ..Default::default()
    }
}

/// Go `vfstest.FromMap(map[string]string{...}, useCaseSensitiveFileNames)`.
pub(crate) fn from_map(
    entries: &[(&str, &str)],
    use_case_sensitive_file_names: bool,
) -> Rc<dyn Fs> {
    vfstest::from_map(entries.iter().copied(), use_case_sensitive_file_names)
}

/// Go `&trackingvfs.FS{Inner: inner}`.
pub(crate) fn tracking(inner: Rc<dyn Fs>) -> Rc<trackingvfs::FS> {
    Rc::new(trackingvfs::FS {
        inner,
        seen_files: Default::default(),
    })
}

/// Go `for seen := range host.SeenFiles.Keys() { host.SeenFiles.Delete(seen) }`.
pub(crate) fn clear_seen(host: &trackingvfs::FS) {
    host.seen_files.borrow_mut().clear();
}

/// Go `host.SeenFiles.Has(path)`.
pub(crate) fn seen(host: &trackingvfs::FS, path: &str) -> bool {
    host.seen_files.borrow().contains(path)
}

/// Go `host.SeenFiles.IsEmpty()`.
pub(crate) fn seen_is_empty(host: &trackingvfs::FS) -> bool {
    host.seen_files.borrow().is_empty()
}

/// Go `fileSystem.(*requestFileSystem)`: the file system behind a `vfs.FS`
/// handle of this package.
pub(crate) fn imp(file_system: &Rc<dyn Fs>) -> &RequestFileSystemImpl {
    file_system
        .as_any()
        .and_then(|fs| fs.downcast_ref::<RequestFileSystemImpl>())
        .expect("a request file system")
}

/// Go `_, isSymlink := entries.Symlinks[name]`.
pub(crate) fn is_symlink(entries: &vfs::Entries, name: &str) -> bool {
    entries
        .symlinks
        .as_ref()
        .is_some_and(|symlinks| symlinks.contains(name))
}

/// Go `assert.DeepEqual` of two `vfs.Entries` (see the file header).
fn comparable_entries(
    entries: &vfs::Entries,
) -> (Vec<String>, Vec<String>, Option<BTreeSet<String>>) {
    (
        entries.files.clone(),
        entries.directories.clone(),
        entries
            .symlinks
            .as_ref()
            .map(|symlinks| symlinks.iter().cloned().collect()),
    )
}

/// Go `vfs.Entries{Files: files, Directories: directories, Symlinks: symlinks}`
/// in the form of `comparable_entries`.
fn expected_entries(
    files: &[&str],
    directories: &[&str],
    symlinks: Option<&[&str]>,
) -> (Vec<String>, Vec<String>, Option<BTreeSet<String>>) {
    (
        files.iter().map(|name| name.to_string()).collect(),
        directories.iter().map(|name| name.to_string()).collect(),
        symlinks.map(|symlinks| symlinks.iter().map(|name| name.to_string()).collect()),
    )
}

/// Go `vfs.ErrInvalid` from `assert.ErrorIs`.
fn is_err_invalid(result: Result<(), vfs::FsError>) -> bool {
    matches!(result, Err(vfs::FsError::Invalid))
}

// Go: requestfilesystem_test.go:20 countingLayeredFileSystem
// PORT: the port knows the layered file systems by type
// (`project::as_fs_layer`), so a test type is not a `LayeredFileSystem` to
// `requestFileSystem.Overlays`. The counter is the `layered` side of a
// `project::CachedLayeredFileSystem`, which forwards `GetFile`,
// `GetFileByPath` and `Overlays` to it.
struct CountingLayeredFileSystem {
    inner: Rc<dyn Fs>,
    get_file_calls: Cell<usize>,
}

impl CountingLayeredFileSystem {
    fn layered(&self) -> &dyn project::LayeredFileSystem {
        project::as_layered_file_system(&*self.inner).expect("a layered file system")
    }
}

impl Fs for CountingLayeredFileSystem {
    fn use_case_sensitive_file_names(&self) -> bool {
        self.inner.use_case_sensitive_file_names()
    }
    fn file_exists(&self, path: &str) -> bool {
        self.inner.file_exists(path)
    }
    fn read_file(&self, path: &str) -> (String, bool) {
        self.inner.read_file(path)
    }
    fn write_file(&self, path: &str, data: &str) -> Result<(), vfs::FsError> {
        self.inner.write_file(path, data)
    }
    fn append_file(&self, path: &str, data: &str) -> Result<(), vfs::FsError> {
        self.inner.append_file(path, data)
    }
    fn remove(&self, path: &str) -> Result<(), vfs::FsError> {
        self.inner.remove(path)
    }
    fn chtimes(
        &self,
        path: &str,
        a_time: Option<SystemTime>,
        m_time: Option<SystemTime>,
    ) -> Result<(), vfs::FsError> {
        self.inner.chtimes(path, a_time, m_time)
    }
    fn directory_exists(&self, path: &str) -> bool {
        self.inner.directory_exists(path)
    }
    fn get_accessible_entries(&self, path: &str) -> vfs::Entries {
        self.inner.get_accessible_entries(path)
    }
    fn stat(&self, path: &str) -> Option<vfs::FileInfo> {
        self.inner.stat(path)
    }
    fn realpath(&self, path: &str) -> String {
        self.inner.realpath(path)
    }
}

impl project::FileHandleSource for CountingLayeredFileSystem {
    // Go: requestfilesystem_test.go:25 countingLayeredFileSystem.GetFile
    fn get_file(&self, file_name: &str) -> Option<Rc<dyn project::FileHandle>> {
        self.get_file_calls.set(self.get_file_calls.get() + 1);
        self.layered().get_file(file_name)
    }

    // Go: requestfilesystem_test.go:30 countingLayeredFileSystem.GetFileByPath
    fn get_file_by_path(
        &self,
        file_name: &str,
        path: &tspath::Path,
    ) -> Option<Rc<dyn project::FileHandle>> {
        self.get_file_calls.set(self.get_file_calls.get() + 1);
        self.layered().get_file_by_path(file_name, path)
    }
}

impl project::LayeredFileSystem for CountingLayeredFileSystem {
    fn overlays(&self) -> Rc<indexmap::IndexMap<tspath::Path, Rc<project::Overlay>>> {
        self.layered().overlays()
    }
}

// Go: requestfilesystem_test.go:35 newRequestFileSystem
pub(crate) fn new_request_file_system(
    params: &RequestFileSystem,
    base: &Rc<dyn Fs>,
    current_directory: &str,
) -> Result<Rc<dyn Fs>, GoError> {
    new_layered_request_file_system(params, base, current_directory)
}

// Go: requestfilesystem_test.go:39 newLayeredRequestFileSystem
pub(crate) fn new_layered_request_file_system(
    params: &RequestFileSystem,
    base: &Rc<dyn Fs>,
    current_directory: &str,
) -> Result<Rc<dyn Fs>, GoError> {
    let mut file_changes = project::FileChangeSummary::default();
    let file_system = new_for_update(
        Some(params),
        base.clone(),
        current_directory,
        &mut file_changes,
    )?;
    // Go: fileSystem.(*requestFileSystem) panics for another type.
    imp(&file_system);
    Ok(file_system)
}

/// One `verify` of `verifyCompactionWithoutHostReads`.
fn verify_compaction<T: PartialEq + Debug>(
    name: &str,
    layer: &Rc<dyn Fs>,
    compacted: &Rc<dyn Fs>,
    host: &trackingvfs::FS,
    paths: &[&str],
    run: &dyn Fn(&dyn Fs, &str) -> T,
) {
    for path in paths {
        clear_seen(host);
        let expected = run(&**layer, path);
        if !seen_is_empty(host) {
            continue;
        }
        let actual = run(&**compacted, path);
        assert!(seen_is_empty(host), "{name} {path}");
        eprintln!("Comparing {name}({path:?}) after compaction");
        assert_eq!(actual, expected, "{name}({path:?})");
    }
}

// Go: requestfilesystem_test.go:48 verifyCompactionWithoutHostReads
pub(crate) fn verify_compaction_without_host_reads(
    layer: &Rc<dyn Fs>,
    host: &trackingvfs::FS,
    paths: &[&str],
) {
    let compacted = nil_error(new_request_file_system(
        &request(Kind::LAYER),
        layer,
        &imp(layer).current_directory,
    ));
    verify_compaction("FileExists", layer, &compacted, host, paths, &|fs, path| {
        fs.file_exists(path)
    });
    verify_compaction(
        "DirectoryExists",
        layer,
        &compacted,
        host,
        paths,
        &|fs, path| fs.directory_exists(path),
    );
    verify_compaction("ReadFile", layer, &compacted, host, paths, &|fs, path| {
        fs.read_file(path)
    });
    verify_compaction("Realpath", layer, &compacted, host, paths, &|fs, path| {
        fs.realpath(path)
    });
    verify_compaction(
        "GetAccessibleEntries",
        layer,
        &compacted,
        host,
        paths,
        &|fs, path| comparable_entries(&fs.get_accessible_entries(path)),
    );
    // PORT: the Go struct of the `vfs.FileInfo` methods is the `FileInfo`
    // value (the port has no `Sys`).
    verify_compaction("Stat", layer, &compacted, host, paths, &|fs, path| {
        fs.stat(path)
    });
}

// Go: requestfilesystem_test.go:98 TestInitializeForUpdate/filesystem layers eagerly compact a request filesystem base
#[test]
fn filesystem_layers_eagerly_compact_a_request_filesystem_base() {
    let host = from_map(&[], true);
    let mut file_changes = project::FileChangeSummary::default();
    let base = nil_error(new_for_update(
        Some(&RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/base.ts", "base")]),
            ..Default::default()
        }),
        host.clone(),
        "/",
        &mut file_changes,
    ));

    let layered = nil_error(new_for_update(
        Some(&RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/layered.ts", "layered")]),
            ..Default::default()
        }),
        base,
        "/",
        &mut file_changes,
    ));
    let request_file_system = layered
        .as_any()
        .and_then(|fs| fs.downcast_ref::<RequestFileSystemImpl>());
    assert!(request_file_system.is_some());
    let request_file_system = request_file_system.unwrap();
    assert!(Rc::ptr_eq(&request_file_system.base, &host));
    assert_eq!(request_file_system.kind, Kind::FULL);
    assert!(layered.file_exists("/base.ts"));
    assert!(layered.file_exists("/layered.ts"));
}

// Go: requestfilesystem_test.go:121 TestInitializeForUpdate/filesystem layers over a host-backed snapshot
#[test]
fn filesystem_layers_over_a_host_backed_snapshot() {
    let host = tracking(from_map(&[("/dir/host.ts", "host")], true));
    let mut file_changes = project::FileChangeSummary::default();
    let file_system = nil_error(new_for_update(
        Some(&RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/dir/cached.ts", "cached")]),
            directories: directories(vec![("/dir", listing(&["cached.ts"], &[]))]),
            ..Default::default()
        }),
        host.clone(),
        "/",
        &mut file_changes,
    ));
    // Change generation may inspect the old directory; reading the supplied
    // complete listing itself must not fall back to the host.
    host.seen_files.borrow_mut().shift_remove("/dir");
    assert_eq!(
        file_system.get_accessible_entries("/dir").files,
        vec!["cached.ts"]
    );
    assert!(!seen(&host, "/dir"));
}

// Go: requestfilesystem_test.go:142 TestInitializeForUpdate/memory starts a new chain
#[test]
fn memory_starts_a_new_chain() {
    let host = from_map(&[("/host.ts", "host")], true);
    let base = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/base.ts", "base")]),
            ..Default::default()
        },
        &host,
        "/",
    ));

    let mut file_changes = project::FileChangeSummary::default();
    let file_system = nil_error(new_for_update(
        Some(&RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/replacement.ts", "replacement")]),
            ..Default::default()
        }),
        base,
        "/",
        &mut file_changes,
    ));
    let request_file_system = get_request_file_system(&*file_system).unwrap();
    assert!(Rc::ptr_eq(&request_file_system.base, &host));
    assert!(get_request_file_system(&*request_file_system.base).is_none());
}

// Go: requestfilesystem_test.go:165 TestRequestFileSystemCompleteDirectoryListingsFullExplicitReplacement
#[test]
fn request_file_system_complete_directory_listings_full_explicit_replacement() {
    test_complete_directory_listing(
        Kind::FULL,
        true,
        listing(&["replacement.ts"], &["replacement-dir"]),
    );
}

// Go: requestfilesystem_test.go:170 TestRequestFileSystemPreservesExplicitDirectoryOrder
#[test]
fn request_file_system_preserves_explicit_directory_order() {
    let host = from_map(&[], true);
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/src/index.ts", ""), ("/src/foo.ts", "")]),
            directories: directories(vec![("/src", listing(&["index.ts", "foo.ts"], &[]))]),
            ..Default::default()
        },
        &host,
        "/",
    ));
    assert_eq!(
        file_system.get_accessible_entries("/src").files,
        vec!["index.ts", "foo.ts"]
    );
}

// Go: requestfilesystem_test.go:187 TestRequestFileSystemDerivesDirectoryListingsWithHostCaseSensitivity
#[test]
fn request_file_system_derives_directory_listings_with_host_case_sensitivity() {
    let params = RequestFileSystem {
        kind: Kind::FULL,
        files: files(&[("C:/Repo/upper.ts", "upper"), ("c:/repo/lower.ts", "lower")]),
        ..Default::default()
    };

    let case_insensitive = from_map(&[], false);
    let file_system = nil_error(new_request_file_system(
        &params,
        &case_insensitive,
        "C:/Workspace",
    ));
    assert_eq!(
        file_system.get_accessible_entries("C:/REPO").files,
        vec!["lower.ts", "upper.ts"]
    );
    assert_eq!(
        file_system.get_accessible_entries("C:/").directories,
        vec!["Repo", "Workspace"]
    );

    let case_sensitive = from_map(&[], true);
    let file_system = nil_error(new_request_file_system(
        &params,
        &case_sensitive,
        "C:/Workspace",
    ));
    assert_eq!(
        file_system.get_accessible_entries("C:/Repo").files,
        vec!["upper.ts"]
    );
    assert_eq!(
        file_system.get_accessible_entries("c:/repo").files,
        vec!["lower.ts"]
    );
}

child_test! {
    // Go: requestfilesystem_test.go:211 TestRequestFileSystemOverlaysDoesNotReadFileHandles
    fn request_file_system_overlays_does_not_read_file_handles() {
        let (session, _) = projecttestutil::setup(project_files(&[("/index.ts", "host")]));
        session.did_open_file(
            &bg(),
            &uri("file:///index.ts"),
            1,
            "overlay",
            &ts_goport::lsp::lsproto::LanguageKind::TYPE_SCRIPT,
        );

        let counting = Rc::new(CountingLayeredFileSystem {
            inner: session.fs(),
            get_file_calls: Cell::new(0),
        });
        // PORT: see `CountingLayeredFileSystem`.
        let base: Rc<dyn Fs> = Rc::new(project::CachedLayeredFileSystem {
            fs: vfs::cachedvfs_from(counting.clone()),
            layered: counting.clone(),
        });
        let file_system = nil_error(new_request_file_system(
            &RequestFileSystem {
                kind: Kind::LAYER,
                removed_paths: removed(&["/index.ts"]),
                ..Default::default()
            },
            &base,
            "/",
        ));
        counting.get_file_calls.set(0);

        assert_eq!(
            project::LayeredFileSystem::overlays(imp(&file_system)).len(),
            0
        );
        assert_eq!(counting.get_file_calls.get(), 0);
        // Go: defer session.Close()
        session.close();
    }
}

// Go: requestfilesystem_test.go:229 TestRequestFileSystemCompleteDirectoryListingsFullExplicitEmpty
#[test]
fn request_file_system_complete_directory_listings_full_explicit_empty() {
    test_complete_directory_listing(Kind::FULL, true, listing(&[], &[]));
}

// Go: requestfilesystem_test.go:234 TestRequestFileSystemCompleteDirectoryListingsFullDerivedReplacement
#[test]
fn request_file_system_complete_directory_listings_full_derived_replacement() {
    test_complete_directory_listing(
        Kind::FULL,
        false,
        listing(&["replacement.ts"], &["replacement-dir"]),
    );
}

// Go: requestfilesystem_test.go:239 TestRequestFileSystemCompleteDirectoryListingsFullDerivedEmpty
#[test]
fn request_file_system_complete_directory_listings_full_derived_empty() {
    test_complete_directory_listing(Kind::FULL, false, listing(&[], &[]));
}

// Go: requestfilesystem_test.go:244 TestRequestFileSystemCompleteDirectoryListingsLayerExplicitReplacement
#[test]
fn request_file_system_complete_directory_listings_layer_explicit_replacement() {
    test_complete_directory_listing(
        Kind::LAYER,
        true,
        listing(&["replacement.ts"], &["replacement-dir"]),
    );
}

// Go: requestfilesystem_test.go:249 TestRequestFileSystemCompleteDirectoryListingsLayerExplicitEmpty
#[test]
fn request_file_system_complete_directory_listings_layer_explicit_empty() {
    test_complete_directory_listing(Kind::LAYER, true, listing(&[], &[]));
}

// Go: requestfilesystem_test.go:254 TestRequestFileSystemCompleteDirectoryListingsLayerDerivedReplacement
#[test]
fn request_file_system_complete_directory_listings_layer_derived_replacement() {
    test_complete_directory_listing(
        Kind::LAYER,
        false,
        listing(&["replacement.ts"], &["replacement-dir"]),
    );
}

// Go: requestfilesystem_test.go:259 TestRequestFileSystemCompleteDirectoryListingsLayerDerivedEmpty
#[test]
fn request_file_system_complete_directory_listings_layer_derived_empty() {
    test_complete_directory_listing(Kind::LAYER, false, listing(&[], &[]));
}

// Go: requestfilesystem_test.go:264 testCompleteDirectoryListing
fn test_complete_directory_listing(
    kind: Kind,
    explicit: bool,
    replacement: RequestDirectoryEntries,
) {
    let host = tracking(from_map(
        &[
            ("/dir/host.ts", "host"),
            ("/dir/host-dir/index.ts", "host child"),
        ],
        true,
    ));
    let host_fs: Rc<dyn Fs> = host.clone();
    let mut params = RequestFileSystem {
        kind,
        files: files(&[
            ("/dir/base.ts", "base"),
            ("/dir/base-dir/index.ts", "base child"),
        ]),
        ..Default::default()
    };
    if explicit {
        params.directories = directories(vec![("/dir", listing(&["base.ts"], &["base-dir"]))]);
    }
    let base = nil_error(new_request_file_system(&params, &host_fs, "/"));
    let layered = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            directories: directories(vec![("/dir", replacement.clone())]),
            ..Default::default()
        },
        &base,
        "/",
    ));

    // Omitting a listing in a later update still merges its derived
    // entries with the complete listing, without reopening host fallback.
    let next = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[
                ("/dir/added.ts", "added"),
                ("/dir/added-dir/index.ts", "added child"),
            ]),
            ..Default::default()
        },
        &layered,
        "/",
    ));
    clear_seen(&host);

    let verify = || {
        let entries = layered.get_accessible_entries("/dir");
        assert!(seen_is_empty(&host));
        assert_eq!(entries.files, replacement.files);
        assert_eq!(entries.directories, replacement.directories);
        let entries = next.get_accessible_entries("/dir");
        assert!(seen_is_empty(&host));
        let mut expected_files = vec!["added.ts".to_string()];
        expected_files.extend(replacement.files.iter().cloned());
        assert_eq!(entries.files, expected_files);
        let mut expected_directories = vec!["added-dir".to_string()];
        expected_directories.extend(replacement.directories.iter().cloned());
        assert_eq!(entries.directories, expected_directories);
    };
    verify();
    assert!(Rc::ptr_eq(&imp(&layered).base, &host_fs));
    assert!(Rc::ptr_eq(&imp(&next).base, &host_fs));
    verify();
}

// Go: requestfilesystem_test.go:323 TestRequestFileSystemSymlinkReplacesDirectoryFullRequestSealedSame
#[test]
fn request_file_system_symlink_replaces_directory_full_request_sealed_same() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::FULL,
        case_sensitive: true,
        link_path: "/dir/removed",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:328 TestRequestFileSystemSymlinkReplacesDirectoryFullRequestSealedParent
#[test]
fn request_file_system_symlink_replaces_directory_full_request_sealed_parent() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::FULL,
        case_sensitive: true,
        link_path: "/dir",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:333 TestRequestFileSystemSymlinkReplacesDirectoryFullRequestSealedChild
#[test]
fn request_file_system_symlink_replaces_directory_full_request_sealed_child() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::FULL,
        case_sensitive: true,
        link_path: "/dir/removed/child",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:338 TestRequestFileSystemSymlinkReplacesDirectoryFullRequestRemovedSame
#[test]
fn request_file_system_symlink_replaces_directory_full_request_removed_same() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::FULL,
        case_sensitive: true,
        remove: true,
        link_path: "/dir/removed",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:343 TestRequestFileSystemSymlinkReplacesDirectoryFullRequestRemovedParent
#[test]
fn request_file_system_symlink_replaces_directory_full_request_removed_parent() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::FULL,
        case_sensitive: true,
        remove: true,
        link_path: "/dir",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:348 TestRequestFileSystemSymlinkReplacesDirectoryFullRequestRemovedChild
#[test]
fn request_file_system_symlink_replaces_directory_full_request_removed_child() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::FULL,
        case_sensitive: true,
        remove: true,
        link_path: "/dir/removed/child",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:353 TestRequestFileSystemSymlinkReplacesDirectoryFullHostSealedSame
#[test]
fn request_file_system_symlink_replaces_directory_full_host_sealed_same() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::FULL,
        host_target: true,
        case_sensitive: true,
        link_path: "/dir/removed",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:358 TestRequestFileSystemSymlinkReplacesDirectoryFullHostSealedParent
#[test]
fn request_file_system_symlink_replaces_directory_full_host_sealed_parent() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::FULL,
        host_target: true,
        case_sensitive: true,
        link_path: "/dir",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:363 TestRequestFileSystemSymlinkReplacesDirectoryFullHostSealedChild
#[test]
fn request_file_system_symlink_replaces_directory_full_host_sealed_child() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::FULL,
        host_target: true,
        case_sensitive: true,
        link_path: "/dir/removed/child",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:368 TestRequestFileSystemSymlinkReplacesDirectoryFullHostRemovedSame
#[test]
fn request_file_system_symlink_replaces_directory_full_host_removed_same() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::FULL,
        host_target: true,
        case_sensitive: true,
        remove: true,
        link_path: "/dir/removed",
    });
}

// Go: requestfilesystem_test.go:373 TestRequestFileSystemSymlinkReplacesDirectoryFullHostRemovedParent
#[test]
fn request_file_system_symlink_replaces_directory_full_host_removed_parent() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::FULL,
        host_target: true,
        case_sensitive: true,
        remove: true,
        link_path: "/dir",
    });
}

// Go: requestfilesystem_test.go:378 TestRequestFileSystemSymlinkReplacesDirectoryFullHostRemovedChild
#[test]
fn request_file_system_symlink_replaces_directory_full_host_removed_child() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::FULL,
        host_target: true,
        case_sensitive: true,
        remove: true,
        link_path: "/dir/removed/child",
    });
}

// Go: requestfilesystem_test.go:383 TestRequestFileSystemSymlinkReplacesDirectoryLayerFallbackSealedSame
#[test]
fn request_file_system_symlink_replaces_directory_layer_fallback_sealed_same() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::LAYER,
        case_sensitive: true,
        link_path: "/dir/removed",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:388 TestRequestFileSystemSymlinkReplacesDirectoryLayerFallbackSealedParent
#[test]
fn request_file_system_symlink_replaces_directory_layer_fallback_sealed_parent() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::LAYER,
        case_sensitive: true,
        link_path: "/dir",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:393 TestRequestFileSystemSymlinkReplacesDirectoryLayerFallbackSealedChild
#[test]
fn request_file_system_symlink_replaces_directory_layer_fallback_sealed_child() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::LAYER,
        case_sensitive: true,
        link_path: "/dir/removed/child",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:398 TestRequestFileSystemSymlinkReplacesDirectoryLayerFallbackRemovedSame
#[test]
fn request_file_system_symlink_replaces_directory_layer_fallback_removed_same() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::LAYER,
        case_sensitive: true,
        remove: true,
        link_path: "/dir/removed",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:403 TestRequestFileSystemSymlinkReplacesDirectoryLayerFallbackRemovedParent
#[test]
fn request_file_system_symlink_replaces_directory_layer_fallback_removed_parent() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::LAYER,
        case_sensitive: true,
        remove: true,
        link_path: "/dir",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:408 TestRequestFileSystemSymlinkReplacesDirectoryLayerFallbackRemovedChild
#[test]
fn request_file_system_symlink_replaces_directory_layer_fallback_removed_child() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::LAYER,
        case_sensitive: true,
        remove: true,
        link_path: "/dir/removed/child",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:413 TestRequestFileSystemSymlinkReplacesDirectoryLayerHostInsensitiveSealedSame
#[test]
fn request_file_system_symlink_replaces_directory_layer_host_insensitive_sealed_same() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::LAYER,
        host_target: true,
        link_path: "/dir/removed",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:418 TestRequestFileSystemSymlinkReplacesDirectoryLayerHostInsensitiveSealedParent
#[test]
fn request_file_system_symlink_replaces_directory_layer_host_insensitive_sealed_parent() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::LAYER,
        host_target: true,
        link_path: "/dir",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:423 TestRequestFileSystemSymlinkReplacesDirectoryLayerHostInsensitiveSealedChild
#[test]
fn request_file_system_symlink_replaces_directory_layer_host_insensitive_sealed_child() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::LAYER,
        host_target: true,
        link_path: "/dir/removed/child",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:428 TestRequestFileSystemSymlinkReplacesDirectoryLayerHostInsensitiveRemovedSame
#[test]
fn request_file_system_symlink_replaces_directory_layer_host_insensitive_removed_same() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::LAYER,
        host_target: true,
        remove: true,
        link_path: "/dir/removed",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:433 TestRequestFileSystemSymlinkReplacesDirectoryLayerHostInsensitiveRemovedParent
#[test]
fn request_file_system_symlink_replaces_directory_layer_host_insensitive_removed_parent() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::LAYER,
        host_target: true,
        remove: true,
        link_path: "/dir",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:438 TestRequestFileSystemSymlinkReplacesDirectoryLayerHostInsensitiveRemovedChild
#[test]
fn request_file_system_symlink_replaces_directory_layer_host_insensitive_removed_child() {
    test_symlink_replaces_directory(SymlinkReplacementOptions {
        kind: Kind::LAYER,
        host_target: true,
        remove: true,
        link_path: "/dir/removed/child",
        ..Default::default()
    });
}

// Go: requestfilesystem_test.go:443 symlinkReplacementOptions
#[derive(Default)]
struct SymlinkReplacementOptions {
    kind: Kind,
    host_target: bool,
    case_sensitive: bool,
    remove: bool,
    link_path: &'static str,
}

// Go: requestfilesystem_test.go:451 testSymlinkReplacesDirectory
fn test_symlink_replaces_directory(options: SymlinkReplacementOptions) {
    let link_path = options.link_path;
    let remove = options.remove;
    let host = from_map(
        &[
            ("/dir/removed/old.ts", "old host"),
            ("/dir/removed/child/old.ts", "old host child"),
            ("/dir/removed/sibling.ts", "old sibling"),
            ("/dir/removed-other/old.ts", "unrelated"),
            ("/target/new.ts", "host target"),
            ("/target/removed/new.ts", "host target"),
        ],
        options.case_sensitive,
    );
    let mut params = RequestFileSystem {
        kind: options.kind.clone(),
        files: files(&[
            ("/dir/removed/cached.ts", "cached"),
            ("/dir/removed/child/cached.ts", "cached child"),
            ("/dir/removed-other/old.ts", "unrelated"),
        ]),
        directories: directories(vec![
            ("/dir", listing(&[], &["removed", "removed-other"])),
            ("/dir/removed", listing(&["cached.ts"], &["child"])),
            ("/dir/removed/child", listing(&["cached.ts"], &[])),
        ]),
        ..Default::default()
    };
    let mut expected_content = "host target";
    if options.kind == Kind::FULL {
        params
            .files
            .insert("/target/new.ts".to_string(), "request target".to_string());
        params.files.insert(
            "/target/removed/new.ts".to_string(),
            "request target".to_string(),
        );
        if !options.host_target {
            expected_content = "request target";
        }
    }
    let base = nil_error(new_request_file_system(&params, &host, "/"));
    let mut previous = base.clone();
    if remove {
        let mut removed_path = "/dir/removed".to_string();
        if !options.case_sensitive {
            removed_path = removed_path.to_uppercase();
        }
        previous = nil_error(new_layered_request_file_system(
            &RequestFileSystem {
                kind: Kind::LAYER,
                removed_paths: vec![removed_path],
                ..Default::default()
            },
            &base,
            "/",
        ));
    }
    let verify_previous = || {
        assert_eq!(previous.directory_exists("/dir/removed"), !remove);
        assert_eq!(previous.file_exists("/dir/removed/cached.ts"), !remove);
        if remove {
            assert!(!previous.file_exists("/dir/removed/old.ts"));
            assert_eq!(
                previous.get_accessible_entries("/dir/removed").files.len(),
                0
            );
            assert_eq!(
                previous
                    .get_accessible_entries("/dir/removed")
                    .directories
                    .len(),
                0
            );
        } else {
            assert_eq!(
                previous.get_accessible_entries("/dir/removed").files,
                vec!["cached.ts"]
            );
            assert_eq!(
                previous.get_accessible_entries("/dir/removed").directories,
                vec!["child"]
            );
        }
    };
    verify_previous();
    let linked = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            symlinks: symlinks(&[(link_path, "/target", options.host_target)]),
            ..Default::default()
        },
        &previous,
        "/",
    ));
    let verify_linked = |file_system: &Rc<dyn Fs>| {
        assert!(Rc::ptr_eq(&imp(file_system).base, &host));
        assert_eq!(imp(file_system).kind, options.kind);
        assert!(file_system.directory_exists(link_path));
        assert!(!file_system.file_exists(link_path));
        for suffix in ["/new.ts", "/removed/new.ts"] {
            let file_name = format!("{link_path}{suffix}");
            assert!(file_system.file_exists(&file_name), "{file_name}");
            let (content, ok) = file_system.read_file(&file_name);
            assert!(ok);
            assert_eq!(content, expected_content);
            let info = file_system.stat(&file_name);
            assert!(info.is_some());
            let info = info.unwrap();
            assert!(!info.is_dir());
            assert_eq!(info.size(), expected_content.len() as i64);
            assert_eq!(file_system.realpath(&file_name), format!("/target{suffix}"));
        }
        let info = file_system.stat(link_path);
        assert!(info.is_some());
        assert!(info.unwrap().is_dir());
        assert_eq!(file_system.realpath(link_path), "/target");
        assert_eq!(
            file_system.get_accessible_entries(link_path).files,
            vec!["new.ts"]
        );
        assert_eq!(
            file_system.get_accessible_entries(link_path).directories,
            vec!["removed"]
        );
        let parent_entries =
            file_system.get_accessible_entries(&tspath::get_directory_path(link_path));
        let link_name = tspath::get_base_file_name(link_path);
        assert!(parent_entries.directories.contains(&link_name));
        assert!(is_symlink(&parent_entries, &link_name));
        assert!(!file_system.file_exists(&format!("{link_path}/old.ts")));
        assert!(!file_system.file_exists(&format!("{link_path}/cached.ts")));
        if link_path != "/dir" {
            assert!(file_system.file_exists("/dir/removed-other/old.ts"));
        }
        if remove {
            assert!(!file_system.file_exists("/dir/removed/sibling.ts"));
        }
        assert_eq!(
            file_system
                .get_accessible_entries(&format!("{link_path}/removed"))
                .files,
            vec!["new.ts"]
        );
    };
    verify_linked(&linked);
    let next = nil_error(new_layered_request_file_system(
        &request(Kind::LAYER),
        &linked,
        "/",
    ));
    verify_linked(&next);
    let deleted = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            removed_paths: vec![format!("{link_path}/new.ts")],
            ..Default::default()
        },
        &next,
        "/",
    ));
    assert!(!deleted.file_exists(&format!("{link_path}/new.ts")));
    assert!(deleted.file_exists(&format!("{link_path}/removed/new.ts")));
    assert_eq!(deleted.get_accessible_entries(link_path).files.len(), 0);
    verify_linked(&linked);
    assert!(base.file_exists("/dir/removed/cached.ts"));
    verify_previous();
}

// Go: requestfilesystem_test.go:575 TestRequestFileSystemFileOverridesParentTombstone
#[test]
fn request_file_system_file_overrides_parent_tombstone() {
    test_object_overrides_tombstone("file", false, "/dir");
}

// Go: requestfilesystem_test.go:580 TestRequestFileSystemFileOverridesSameTombstone
#[test]
fn request_file_system_file_overrides_same_tombstone() {
    test_object_overrides_tombstone("file", false, "/dir/removed");
}

// Go: requestfilesystem_test.go:585 TestRequestFileSystemFileOverridesChildTombstone
#[test]
fn request_file_system_file_overrides_child_tombstone() {
    test_object_overrides_tombstone("file", false, "/dir/removed/child");
}

// Go: requestfilesystem_test.go:590 TestRequestFileSystemFileOverridesParentTombstoneInheritedLink
#[test]
fn request_file_system_file_overrides_parent_tombstone_inherited_link() {
    test_object_overrides_tombstone("file", true, "/dir");
}

// Go: requestfilesystem_test.go:595 TestRequestFileSystemFileOverridesSameTombstoneInheritedLink
#[test]
fn request_file_system_file_overrides_same_tombstone_inherited_link() {
    test_object_overrides_tombstone("file", true, "/dir/removed");
}

// Go: requestfilesystem_test.go:600 TestRequestFileSystemFileOverridesChildTombstoneInheritedLink
#[test]
fn request_file_system_file_overrides_child_tombstone_inherited_link() {
    test_object_overrides_tombstone("file", true, "/dir/removed/child");
}

// Go: requestfilesystem_test.go:605 TestRequestFileSystemDirectoryOverridesParentTombstone
#[test]
fn request_file_system_directory_overrides_parent_tombstone() {
    test_object_overrides_tombstone("directory", false, "/dir");
}

// Go: requestfilesystem_test.go:610 TestRequestFileSystemDirectoryOverridesSameTombstone
#[test]
fn request_file_system_directory_overrides_same_tombstone() {
    test_object_overrides_tombstone("directory", false, "/dir/removed");
}

// Go: requestfilesystem_test.go:615 TestRequestFileSystemDirectoryOverridesChildTombstone
#[test]
fn request_file_system_directory_overrides_child_tombstone() {
    test_object_overrides_tombstone("directory", false, "/dir/removed/child");
}

// Go: requestfilesystem_test.go:620 TestRequestFileSystemDirectoryOverridesParentTombstoneInheritedLink
#[test]
fn request_file_system_directory_overrides_parent_tombstone_inherited_link() {
    test_object_overrides_tombstone("directory", true, "/dir");
}

// Go: requestfilesystem_test.go:625 TestRequestFileSystemDirectoryOverridesSameTombstoneInheritedLink
#[test]
fn request_file_system_directory_overrides_same_tombstone_inherited_link() {
    test_object_overrides_tombstone("directory", true, "/dir/removed");
}

// Go: requestfilesystem_test.go:630 TestRequestFileSystemDirectoryOverridesChildTombstoneInheritedLink
#[test]
fn request_file_system_directory_overrides_child_tombstone_inherited_link() {
    test_object_overrides_tombstone("directory", true, "/dir/removed/child");
}

// Go: requestfilesystem_test.go:635 TestRequestFileSystemSymlinkOverridesParentTombstone
#[test]
fn request_file_system_symlink_overrides_parent_tombstone() {
    test_object_overrides_tombstone("symlink", false, "/dir");
}

// Go: requestfilesystem_test.go:640 TestRequestFileSystemSymlinkOverridesSameTombstone
#[test]
fn request_file_system_symlink_overrides_same_tombstone() {
    test_object_overrides_tombstone("symlink", false, "/dir/removed");
}

// Go: requestfilesystem_test.go:645 TestRequestFileSystemSymlinkOverridesChildTombstone
#[test]
fn request_file_system_symlink_overrides_child_tombstone() {
    test_object_overrides_tombstone("symlink", false, "/dir/removed/child");
}

// Go: requestfilesystem_test.go:650 TestRequestFileSystemSymlinkOverridesParentTombstoneInheritedLink
#[test]
fn request_file_system_symlink_overrides_parent_tombstone_inherited_link() {
    test_object_overrides_tombstone("symlink", true, "/dir");
}

// Go: requestfilesystem_test.go:655 TestRequestFileSystemSymlinkOverridesSameTombstoneInheritedLink
#[test]
fn request_file_system_symlink_overrides_same_tombstone_inherited_link() {
    test_object_overrides_tombstone("symlink", true, "/dir/removed");
}

// Go: requestfilesystem_test.go:660 TestRequestFileSystemSymlinkOverridesChildTombstoneInheritedLink
#[test]
fn request_file_system_symlink_overrides_child_tombstone_inherited_link() {
    test_object_overrides_tombstone("symlink", true, "/dir/removed/child");
}

// Go: requestfilesystem_test.go:665 TestRequestFileSystemFileSymlinkOverridesParentTombstone
#[test]
fn request_file_system_file_symlink_overrides_parent_tombstone() {
    test_object_overrides_tombstone("file-symlink", false, "/dir");
}

// Go: requestfilesystem_test.go:670 TestRequestFileSystemFileSymlinkOverridesSameTombstone
#[test]
fn request_file_system_file_symlink_overrides_same_tombstone() {
    test_object_overrides_tombstone("file-symlink", false, "/dir/removed");
}

// Go: requestfilesystem_test.go:675 TestRequestFileSystemFileSymlinkOverridesChildTombstone
#[test]
fn request_file_system_file_symlink_overrides_child_tombstone() {
    test_object_overrides_tombstone("file-symlink", false, "/dir/removed/child");
}

// Go: requestfilesystem_test.go:680 TestRequestFileSystemFileSymlinkOverridesParentTombstoneInheritedLink
#[test]
fn request_file_system_file_symlink_overrides_parent_tombstone_inherited_link() {
    test_object_overrides_tombstone("file-symlink", true, "/dir");
}

// Go: requestfilesystem_test.go:685 TestRequestFileSystemFileSymlinkOverridesSameTombstoneInheritedLink
#[test]
fn request_file_system_file_symlink_overrides_same_tombstone_inherited_link() {
    test_object_overrides_tombstone("file-symlink", true, "/dir/removed");
}

// Go: requestfilesystem_test.go:690 TestRequestFileSystemFileSymlinkOverridesChildTombstoneInheritedLink
#[test]
fn request_file_system_file_symlink_overrides_child_tombstone_inherited_link() {
    test_object_overrides_tombstone("file-symlink", true, "/dir/removed/child");
}

// Go: requestfilesystem_test.go:695 testObjectOverridesTombstone
fn test_object_overrides_tombstone(object: &str, inherited_link: bool, path: &str) {
    let host = tracking(from_map(
        &[
            ("/dir/removed/old.ts", "old"),
            ("/dir/removed/child.ts", "old child"),
            ("/old/removed/old.ts", "old target"),
            ("/target/file.ts", "target"),
        ],
        true,
    ));
    let host_fs: Rc<dyn Fs> = host.clone();
    let mut base_params = request(Kind::LAYER);
    if inherited_link {
        base_params.symlinks = symlinks(&[("/dir", "/old", false)]);
    }
    let base = nil_error(new_request_file_system(&base_params, &host_fs, "/"));
    let removed_fs = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            removed_paths: removed(&["/dir/removed"]),
            ..Default::default()
        },
        &base,
        "/",
    ));
    let mut params = request(Kind::LAYER);
    match object {
        "file" => params.files = files(&[(path, "new")]),
        "directory" => params.directories = directories(vec![(path, listing(&[], &[]))]),
        "symlink" => params.symlinks = symlinks(&[(path, "/target", false)]),
        "file-symlink" => params.symlinks = symlinks(&[(path, "/target/file.ts", false)]),
        _ => {}
    }
    let replaced = nil_error(new_layered_request_file_system(&params, &removed_fs, "/"));
    let is_file = object == "file" || object == "file-symlink";
    assert_eq!(replaced.file_exists(path), is_file);
    assert_eq!(replaced.directory_exists(path), !is_file);
    assert!(replaced.stat(path).is_some());
    let entries = replaced.get_accessible_entries(&tspath::get_directory_path(path));
    let entry_name = tspath::get_base_file_name(path);
    assert_eq!(entries.files.contains(&entry_name), is_file);
    assert_eq!(entries.directories.contains(&entry_name), !is_file);
    assert_eq!(
        is_symlink(&entries, &entry_name),
        object == "symlink" || object == "file-symlink"
    );
    assert!(!replaced.file_exists("/dir/removed/old.ts"));
    let (_, ok) = replaced.read_file("/dir/removed/old.ts");
    assert!(!ok);
    assert!(replaced.stat("/dir/removed/old.ts").is_none());
    if is_file {
        assert_eq!(
            replaced
                .get_accessible_entries(&format!("{path}/removed"))
                .files
                .len(),
            0
        );
        assert_eq!(replaced.get_accessible_entries(path).directories.len(), 0);
    }
    assert!(!removed_fs.directory_exists("/dir/removed"));
    let file_ts = format!("{path}/file.ts");
    verify_compaction_without_host_reads(
        &replaced,
        &host,
        &[
            path,
            &file_ts,
            "/dir",
            "/dir/removed",
            "/dir/removed/old.ts",
            "/target/file.ts",
        ],
    );
}

// Go: requestfilesystem_test.go:751 TestRequestFileSystemReplacementPreservesCurrentFullAliasDirectoryRemoval
#[test]
fn request_file_system_replacement_preserves_current_full_alias_directory_removal() {
    test_replacement_preserves_current_removal(Kind::FULL, "/dir/blocked");
}

// Go: requestfilesystem_test.go:756 TestRequestFileSystemReplacementPreservesCurrentFullAliasFileRemoval
#[test]
fn request_file_system_replacement_preserves_current_full_alias_file_removal() {
    test_replacement_preserves_current_removal(Kind::FULL, "/dir/blocked/gone.ts");
}

// Go: requestfilesystem_test.go:761 TestRequestFileSystemReplacementPreservesCurrentFullTargetDirectoryRemoval
#[test]
fn request_file_system_replacement_preserves_current_full_target_directory_removal() {
    test_replacement_preserves_current_removal(Kind::FULL, "/target/blocked");
}

// Go: requestfilesystem_test.go:766 TestRequestFileSystemReplacementPreservesCurrentFullTargetFileRemoval
#[test]
fn request_file_system_replacement_preserves_current_full_target_file_removal() {
    test_replacement_preserves_current_removal(Kind::FULL, "/target/blocked/gone.ts");
}

// Go: requestfilesystem_test.go:771 TestRequestFileSystemReplacementPreservesCurrentLayerAliasDirectoryRemoval
#[test]
fn request_file_system_replacement_preserves_current_layer_alias_directory_removal() {
    test_replacement_preserves_current_removal(Kind::LAYER, "/dir/blocked");
}

// Go: requestfilesystem_test.go:776 TestRequestFileSystemReplacementPreservesCurrentLayerAliasFileRemoval
#[test]
fn request_file_system_replacement_preserves_current_layer_alias_file_removal() {
    test_replacement_preserves_current_removal(Kind::LAYER, "/dir/blocked/gone.ts");
}

// Go: requestfilesystem_test.go:781 TestRequestFileSystemReplacementPreservesCurrentLayerTargetDirectoryRemoval
#[test]
fn request_file_system_replacement_preserves_current_layer_target_directory_removal() {
    test_replacement_preserves_current_removal(Kind::LAYER, "/target/blocked");
}

// Go: requestfilesystem_test.go:786 TestRequestFileSystemReplacementPreservesCurrentLayerTargetFileRemoval
#[test]
fn request_file_system_replacement_preserves_current_layer_target_file_removal() {
    test_replacement_preserves_current_removal(Kind::LAYER, "/target/blocked/gone.ts");
}

// Go: requestfilesystem_test.go:791 testReplacementPreservesCurrentRemoval
fn test_replacement_preserves_current_removal(kind: Kind, removed_path: &str) {
    let file_entries = [
        ("/dir/old.ts", "old host"),
        ("/target/keep.ts", "keep"),
        ("/target/blocked/gone.ts", "gone"),
    ];
    let host = from_map(&file_entries, true);
    let mut params = request(kind.clone());
    if kind == Kind::FULL {
        params.files = files(&file_entries);
    }
    let base = nil_error(new_request_file_system(&params, &host, "/"));
    let removed_fs = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            removed_paths: removed(&["/dir", "/dir/blocked"]),
            ..Default::default()
        },
        &base,
        "/",
    ));
    let linked = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            symlinks: symlinks(&[("/dir", "/target", kind == Kind::LAYER)]),
            removed_paths: removed(&[removed_path]),
            ..Default::default()
        },
        &removed_fs,
        "/",
    ));
    assert!(linked.file_exists("/dir/keep.ts"));
    assert!(!linked.file_exists("/dir/old.ts"));
    assert!(!linked.file_exists("/dir/blocked/gone.ts"));
    let (_, ok) = linked.read_file("/dir/blocked/gone.ts");
    assert!(!ok);
    assert!(linked.stat("/dir/blocked/gone.ts").is_none());
    assert_eq!(linked.get_accessible_entries("/dir/blocked").files.len(), 0);
    let deleted = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            removed_paths: removed(&["/dir"]),
            ..Default::default()
        },
        &linked,
        "/",
    ));
    assert!(!deleted.directory_exists("/dir"));
    assert!(!deleted.file_exists("/dir/keep.ts"));
    assert_eq!(deleted.get_accessible_entries("/dir").files.len(), 0);
    assert!(deleted.file_exists("/target/keep.ts"));
    assert!(linked.file_exists("/dir/keep.ts"));
}

// Go: requestfilesystem_test.go:835 TestRequestFileSystemSameLayerRemovalRequestAncestorStandalone
#[test]
fn request_file_system_same_layer_removal_request_ancestor_standalone() {
    test_same_layer_removal(false, "/links", "standalone");
}

// Go: requestfilesystem_test.go:840 TestRequestFileSystemSameLayerRemovalRequestAncestorLayered
#[test]
fn request_file_system_same_layer_removal_request_ancestor_layered() {
    test_same_layer_removal(false, "/links", "layered");
}

// Go: requestfilesystem_test.go:845 TestRequestFileSystemSameLayerRemovalRequestAncestorCompacted
#[test]
fn request_file_system_same_layer_removal_request_ancestor_compacted() {
    test_same_layer_removal(false, "/links", "compacted");
}

// Go: requestfilesystem_test.go:850 TestRequestFileSystemSameLayerRemovalRequestAncestorRecompacted
#[test]
fn request_file_system_same_layer_removal_request_ancestor_recompacted() {
    test_same_layer_removal(false, "/links", "recompacted");
}

// Go: requestfilesystem_test.go:855 TestRequestFileSystemSameLayerRemovalRequestAncestorCompactedInput
#[test]
fn request_file_system_same_layer_removal_request_ancestor_compacted_input() {
    test_same_layer_removal(false, "/links", "compacted-input");
}

// Go: requestfilesystem_test.go:860 TestRequestFileSystemSameLayerRemovalRequestLinkStandalone
#[test]
fn request_file_system_same_layer_removal_request_link_standalone() {
    test_same_layer_removal(false, "/links/pkg", "standalone");
}

// Go: requestfilesystem_test.go:865 TestRequestFileSystemSameLayerRemovalRequestLinkLayered
#[test]
fn request_file_system_same_layer_removal_request_link_layered() {
    test_same_layer_removal(false, "/links/pkg", "layered");
}

// Go: requestfilesystem_test.go:870 TestRequestFileSystemSameLayerRemovalRequestLinkCompacted
#[test]
fn request_file_system_same_layer_removal_request_link_compacted() {
    test_same_layer_removal(false, "/links/pkg", "compacted");
}

// Go: requestfilesystem_test.go:875 TestRequestFileSystemSameLayerRemovalRequestLinkRecompacted
#[test]
fn request_file_system_same_layer_removal_request_link_recompacted() {
    test_same_layer_removal(false, "/links/pkg", "recompacted");
}

// Go: requestfilesystem_test.go:880 TestRequestFileSystemSameLayerRemovalRequestLinkCompactedInput
#[test]
fn request_file_system_same_layer_removal_request_link_compacted_input() {
    test_same_layer_removal(false, "/links/pkg", "compacted-input");
}

// Go: requestfilesystem_test.go:885 TestRequestFileSystemSameLayerRemovalRequestDescendantStandalone
#[test]
fn request_file_system_same_layer_removal_request_descendant_standalone() {
    test_same_layer_removal(false, "/links/pkg/file.ts", "standalone");
}

// Go: requestfilesystem_test.go:890 TestRequestFileSystemSameLayerRemovalRequestDescendantLayered
#[test]
fn request_file_system_same_layer_removal_request_descendant_layered() {
    test_same_layer_removal(false, "/links/pkg/file.ts", "layered");
}

// Go: requestfilesystem_test.go:895 TestRequestFileSystemSameLayerRemovalRequestDescendantCompacted
#[test]
fn request_file_system_same_layer_removal_request_descendant_compacted() {
    test_same_layer_removal(false, "/links/pkg/file.ts", "compacted");
}

// Go: requestfilesystem_test.go:900 TestRequestFileSystemSameLayerRemovalRequestDescendantRecompacted
#[test]
fn request_file_system_same_layer_removal_request_descendant_recompacted() {
    test_same_layer_removal(false, "/links/pkg/file.ts", "recompacted");
}

// Go: requestfilesystem_test.go:905 TestRequestFileSystemSameLayerRemovalRequestDescendantCompactedInput
#[test]
fn request_file_system_same_layer_removal_request_descendant_compacted_input() {
    test_same_layer_removal(false, "/links/pkg/file.ts", "compacted-input");
}

// Go: requestfilesystem_test.go:910 TestRequestFileSystemSameLayerRemovalHostAncestorStandalone
#[test]
fn request_file_system_same_layer_removal_host_ancestor_standalone() {
    test_same_layer_removal(true, "/links", "standalone");
}

// Go: requestfilesystem_test.go:915 TestRequestFileSystemSameLayerRemovalHostAncestorLayered
#[test]
fn request_file_system_same_layer_removal_host_ancestor_layered() {
    test_same_layer_removal(true, "/links", "layered");
}

// Go: requestfilesystem_test.go:920 TestRequestFileSystemSameLayerRemovalHostAncestorCompacted
#[test]
fn request_file_system_same_layer_removal_host_ancestor_compacted() {
    test_same_layer_removal(true, "/links", "compacted");
}

// Go: requestfilesystem_test.go:925 TestRequestFileSystemSameLayerRemovalHostAncestorRecompacted
#[test]
fn request_file_system_same_layer_removal_host_ancestor_recompacted() {
    test_same_layer_removal(true, "/links", "recompacted");
}

// Go: requestfilesystem_test.go:930 TestRequestFileSystemSameLayerRemovalHostAncestorCompactedInput
#[test]
fn request_file_system_same_layer_removal_host_ancestor_compacted_input() {
    test_same_layer_removal(true, "/links", "compacted-input");
}

// Go: requestfilesystem_test.go:935 TestRequestFileSystemSameLayerRemovalHostLinkStandalone
#[test]
fn request_file_system_same_layer_removal_host_link_standalone() {
    test_same_layer_removal(true, "/links/pkg", "standalone");
}

// Go: requestfilesystem_test.go:940 TestRequestFileSystemSameLayerRemovalHostLinkLayered
#[test]
fn request_file_system_same_layer_removal_host_link_layered() {
    test_same_layer_removal(true, "/links/pkg", "layered");
}

// Go: requestfilesystem_test.go:945 TestRequestFileSystemSameLayerRemovalHostLinkCompacted
#[test]
fn request_file_system_same_layer_removal_host_link_compacted() {
    test_same_layer_removal(true, "/links/pkg", "compacted");
}

// Go: requestfilesystem_test.go:950 TestRequestFileSystemSameLayerRemovalHostLinkRecompacted
#[test]
fn request_file_system_same_layer_removal_host_link_recompacted() {
    test_same_layer_removal(true, "/links/pkg", "recompacted");
}

// Go: requestfilesystem_test.go:955 TestRequestFileSystemSameLayerRemovalHostLinkCompactedInput
#[test]
fn request_file_system_same_layer_removal_host_link_compacted_input() {
    test_same_layer_removal(true, "/links/pkg", "compacted-input");
}

// Go: requestfilesystem_test.go:960 TestRequestFileSystemSameLayerRemovalHostDescendantStandalone
#[test]
fn request_file_system_same_layer_removal_host_descendant_standalone() {
    test_same_layer_removal(true, "/links/pkg/file.ts", "standalone");
}

// Go: requestfilesystem_test.go:965 TestRequestFileSystemSameLayerRemovalHostDescendantLayered
#[test]
fn request_file_system_same_layer_removal_host_descendant_layered() {
    test_same_layer_removal(true, "/links/pkg/file.ts", "layered");
}

// Go: requestfilesystem_test.go:970 TestRequestFileSystemSameLayerRemovalHostDescendantCompacted
#[test]
fn request_file_system_same_layer_removal_host_descendant_compacted() {
    test_same_layer_removal(true, "/links/pkg/file.ts", "compacted");
}

// Go: requestfilesystem_test.go:975 TestRequestFileSystemSameLayerRemovalHostDescendantRecompacted
#[test]
fn request_file_system_same_layer_removal_host_descendant_recompacted() {
    test_same_layer_removal(true, "/links/pkg/file.ts", "recompacted");
}

// Go: requestfilesystem_test.go:980 TestRequestFileSystemSameLayerRemovalHostDescendantCompactedInput
#[test]
fn request_file_system_same_layer_removal_host_descendant_compacted_input() {
    test_same_layer_removal(true, "/links/pkg/file.ts", "compacted-input");
}

// Go: requestfilesystem_test.go:985 testSameLayerRemoval
fn test_same_layer_removal(host_target: bool, removed_path: &str, form: &str) {
    let host = tracking(from_map(&[("/target/file.ts", "host")], true));
    let host_fs: Rc<dyn Fs> = host.clone();
    let base = nil_error(new_request_file_system(&request(Kind::FULL), &host_fs, "/"));
    let params = RequestFileSystem {
        kind: Kind::LAYER,
        files: files(&[("/target/file.ts", "request")]),
        symlinks: symlinks(&[("/links/pkg", "/target", host_target)]),
        removed_paths: removed(&[removed_path]),
        ..Default::default()
    };
    let file_system = match form {
        "standalone" => new_request_file_system(&params, &host_fs, "/"),
        "layered" => new_request_file_system(&params, &base, "/"),
        _ => {
            let file_system = nil_error(new_layered_request_file_system(&params, &base, "/"));
            match form {
                "recompacted" => {
                    new_layered_request_file_system(&request(Kind::LAYER), &file_system, "/")
                }
                "compacted-input" => new_request_file_system(&params, &file_system, "/"),
                _ => Ok(file_system),
            }
        }
    };
    let file_system = nil_error(file_system);
    assert!(!file_system.file_exists("/links/pkg/file.ts"));
    let (_, ok) = file_system.read_file("/links/pkg/file.ts");
    assert!(!ok);
    assert!(file_system.stat("/links/pkg/file.ts").is_none());
    assert_eq!(
        file_system.realpath("/links/pkg/file.ts"),
        "/links/pkg/file.ts"
    );
    assert_eq!(
        file_system.get_accessible_entries("/links/pkg").files.len(),
        0
    );
    let link_exists = removed_path == "/links/pkg/file.ts";
    assert_eq!(file_system.directory_exists("/links/pkg"), link_exists);
    let entries = file_system.get_accessible_entries("/links");
    assert_eq!(
        entries.directories.contains(&"pkg".to_string()),
        link_exists
    );
    assert_eq!(is_symlink(&entries, "pkg"), link_exists);
    assert!(file_system.file_exists("/target/file.ts"));
    verify_compaction_without_host_reads(
        &file_system,
        &host,
        &[
            "/",
            "/links",
            "/links/pkg",
            "/links/pkg/file.ts",
            "/target",
            "/target/file.ts",
            "/missing",
        ],
    );
}

// Go: requestfilesystem_test.go:1033 TestRequestFileSystemRemovalExceptionsRequest
#[test]
fn request_file_system_removal_exceptions_request() {
    test_removal_exceptions(false, false);
}

// Go: requestfilesystem_test.go:1038 TestRequestFileSystemRemovalExceptionsRequestRemovedAgain
#[test]
fn request_file_system_removal_exceptions_request_removed_again() {
    test_removal_exceptions(false, true);
}

// Go: requestfilesystem_test.go:1043 TestRequestFileSystemRemovalExceptionsHost
#[test]
fn request_file_system_removal_exceptions_host() {
    test_removal_exceptions(true, false);
}

// Go: requestfilesystem_test.go:1048 TestRequestFileSystemRemovalExceptionsHostRemovedAgain
#[test]
fn request_file_system_removal_exceptions_host_removed_again() {
    test_removal_exceptions(true, true);
}

// Go: requestfilesystem_test.go:1053 testRemovalExceptions
fn test_removal_exceptions(host_target: bool, remove_again: bool) {
    let host = from_map(
        &[
            ("/dir/old.ts", "old"),
            ("/target/a.ts", "a"),
            ("/target/b.ts", "b"),
            ("/target/sub/c.ts", "c"),
        ],
        true,
    );
    let base = nil_error(new_request_file_system(&request(Kind::LAYER), &host, "/"));
    let removed_fs = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            removed_paths: removed(&["/dir"]),
            ..Default::default()
        },
        &base,
        "/",
    ));
    let params = RequestFileSystem {
        kind: Kind::LAYER,
        symlinks: symlinks(&[("/dir/pkg", "/target", host_target)]),
        removed_paths: removed(&["/dir/pkg/b.ts"]),
        ..Default::default()
    };
    let layered = nil_error(new_request_file_system(&params, &removed_fs, "/"));
    let compacted = nil_error(new_request_file_system(
        &request(Kind::LAYER),
        &layered,
        "/",
    ));
    let input = nil_error(new_request_file_system(
        &request(Kind::LAYER),
        &compacted,
        "/",
    ));
    let verify = |file_system: &Rc<dyn Fs>| {
        let mut file_system = file_system.clone();
        if remove_again {
            file_system = nil_error(new_layered_request_file_system(
                &RequestFileSystem {
                    kind: Kind::LAYER,
                    removed_paths: removed(&["/dir"]),
                    ..Default::default()
                },
                &file_system,
                "/",
            ));
        }
        assert_eq!(file_system.file_exists("/dir/pkg/a.ts"), !remove_again);
        assert!(!file_system.file_exists("/dir/pkg/b.ts"));
        assert!(!file_system.file_exists("/dir/old.ts"));
        let entries = file_system.get_accessible_entries("/dir/pkg");
        if remove_again {
            assert_eq!(entries.files.len(), 0);
            assert_eq!(entries.directories.len(), 0);
        } else {
            assert_eq!(entries.files, vec!["a.ts"]);
            assert_eq!(entries.directories, vec!["sub"]);
        }
    };
    verify(&layered);
    verify(&compacted);
    verify(&input);
    assert!(!removed_fs.directory_exists("/dir/pkg"));
    assert!(compacted.file_exists("/dir/pkg/a.ts"));
}

// Go: requestfilesystem_test.go:1112 TestRequestFileSystem/compaction preserves host fallback
#[test]
fn compaction_preserves_host_fallback() {
    let host = from_map(&[("/host.ts", "host")], true);
    let base_fs = nil_error(new_request_file_system(&request(Kind::LAYER), &host, "/"));
    let base = get_request_file_system(&*base_fs);
    assert!(base.is_some());
    let base = base.unwrap();
    assert!(Rc::ptr_eq(&base.base, &host));
    assert!(!base.file_exists("/created-after-base.ts"));
    host.write_file("/created-after-base.ts", "created")
        .unwrap();

    let layered_fs = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/layered.ts", "layered")]),
            ..Default::default()
        },
        &base_fs,
        "/",
    ));
    let layered = get_request_file_system(&*layered_fs);
    assert!(layered.is_some());
    let layered = layered.unwrap();
    assert!(Rc::ptr_eq(&layered.base, &host));
    assert!(layered.file_exists("/created-after-base.ts"));
    host.remove("/created-after-base.ts").unwrap();

    assert!(Rc::ptr_eq(&layered.base, &host));
    assert!(!layered.file_exists("/created-after-base.ts"));
    let (contents, ok) = layered.read_file("/host.ts");
    assert!(ok);
    assert_eq!(contents, "host");
}

// Go: requestfilesystem_test.go:1145 TestRequestFileSystem/memory is total and never falls back
#[test]
fn memory_is_total_and_never_falls_back() {
    let base = tracking(from_map(&[("/host.ts", "host")], true));
    let base_fs: Rc<dyn Fs> = base.clone();
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/src/index.ts", "memory")]),
            ..Default::default()
        },
        &base_fs,
        "/",
    ));

    let (contents, ok) = file_system.read_file("/src/index.ts");
    assert!(ok);
    assert_eq!(contents, "memory");
    assert!(file_system.file_exists("/src/index.ts"));
    assert!(file_system.directory_exists("/src"));
    assert_eq!(
        file_system.get_accessible_entries("/src").files,
        vec!["index.ts"]
    );

    let (_, ok) = file_system.read_file("/host.ts");
    assert!(!ok);
    assert!(!file_system.file_exists("/host.ts"));
    assert!(!seen(&base, "/host.ts"));
}

// Go: requestfilesystem_test.go:1171 TestRequestFileSystem/cache hits bypass the host and misses fall back
#[test]
fn cache_hits_bypass_the_host_and_misses_fall_back() {
    let base = tracking(from_map(&[("/fallback.ts", "fallback")], true));
    let base_fs: Rc<dyn Fs> = base.clone();
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/cached/index.ts", "cached")]),
            directories: directories(vec![("/cached", listing(&["index.ts"], &[]))]),
            ..Default::default()
        },
        &base_fs,
        "/",
    ));
    clear_seen(&base);

    let (contents, ok) = file_system.read_file("/cached/index.ts");
    assert!(ok);
    assert_eq!(contents, "cached");
    assert!(file_system.file_exists("/cached/index.ts"));
    assert!(file_system.directory_exists("/cached"));
    assert_eq!(
        file_system.get_accessible_entries("/cached").files,
        vec!["index.ts"]
    );
    assert!(!seen(&base, "/cached/index.ts"));
    assert!(!seen(&base, "/cached"));

    let (contents, ok) = file_system.read_file("/fallback.ts");
    assert!(ok);
    assert_eq!(contents, "fallback");
    assert!(seen(&base, "/fallback.ts"));
}

// Go: requestfilesystem_test.go:1205 TestRequestFileSystem/layered memory is a total replacement
#[test]
fn layered_memory_is_a_total_replacement() {
    let file_system = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/memory.ts", "memory")]),
            ..Default::default()
        },
        &from_map(&[("/host.ts", "host")], true),
        "/",
    ));
    let (contents, ok) = file_system.read_file("/memory.ts");
    assert!(ok);
    assert_eq!(contents, "memory");
    let (_, ok) = file_system.read_file("/host.ts");
    assert!(!ok);
}

// Go: requestfilesystem_test.go:1221 TestRequestFileSystem/memory resolves internal file and directory symlinks
#[test]
fn memory_resolves_internal_file_and_directory_symlinks() {
    let base = tracking(from_map(&[("/host.ts", "host")], true));
    let base_fs: Rc<dyn Fs> = base.clone();
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[(
                "/packages/pkg/index.d.ts",
                "export declare const value: number;",
            )]),
            symlinks: symlinks(&[
                ("/project/node_modules/pkg", "../../../packages/pkg", false),
                ("/project/pkg.d.ts", "../packages/pkg/index.d.ts", false),
            ]),
            ..Default::default()
        },
        &base_fs,
        "/",
    ));

    let (contents, ok) = file_system.read_file("/project/node_modules/pkg/index.d.ts");
    assert!(ok);
    assert_eq!(contents, "export declare const value: number;");
    let (contents, ok) = file_system.read_file("/project/pkg.d.ts");
    assert!(ok);
    assert_eq!(contents, "export declare const value: number;");
    assert_eq!(
        file_system.realpath("/project/node_modules/pkg/index.d.ts"),
        "/packages/pkg/index.d.ts"
    );

    let entries = file_system.get_accessible_entries("/project/node_modules");
    assert_eq!(entries.directories, vec!["pkg"]);
    assert!(is_symlink(&entries, "pkg"));
    let entries = file_system.get_accessible_entries("/project");
    assert_eq!(entries.files, vec!["pkg.d.ts"]);
    assert!(is_symlink(&entries, "pkg.d.ts"));
    assert!(seen_is_empty(&base));
}

// Go: requestfilesystem_test.go:1257 TestRequestFileSystem/cache resolves internal symlinks before the host
#[test]
fn cache_resolves_internal_symlinks_before_the_host() {
    let base = tracking(from_map(
        &[("/packages/pkg/index.d.ts", "host content")],
        true,
    ));
    let base_fs: Rc<dyn Fs> = base.clone();
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/packages/pkg/index.d.ts", "cached content")]),
            directories: directories(vec![("/project/node_modules", listing(&[], &[]))]),
            symlinks: symlinks(&[("/project/node_modules/pkg", "/packages/pkg", false)]),
            ..Default::default()
        },
        &base_fs,
        "/",
    ));
    clear_seen(&base);

    let (contents, ok) = file_system.read_file("/project/node_modules/pkg/index.d.ts");
    assert!(ok);
    assert_eq!(contents, "cached content");
    assert_eq!(
        file_system.realpath("/project/node_modules/pkg/index.d.ts"),
        "/packages/pkg/index.d.ts"
    );
    let entries = file_system.get_accessible_entries("/project/node_modules");
    assert_eq!(entries.directories, vec!["pkg"]);
    assert!(is_symlink(&entries, "pkg"));
    assert!(seen_is_empty(&base));
}

// Go: requestfilesystem_test.go:1290 TestRequestFileSystem/cache file shadows underlying symlink realpath
#[test]
fn cache_file_shadows_underlying_symlink_realpath() {
    let base = vfstest::from_map(
        [
            ("/project/node_modules/pkg", vfstest::symlink("/host/pkg")),
            ("/host/pkg/index.d.ts", MapFile::from("host content")),
        ],
        true,
    );
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/project/node_modules/pkg/index.d.ts", "cached content")]),
            ..Default::default()
        },
        &base,
        "/",
    ));

    let (contents, ok) = file_system.read_file("/project/node_modules/pkg/index.d.ts");
    assert!(ok);
    assert_eq!(contents, "cached content");
    assert_eq!(
        file_system.realpath("/project/node_modules/pkg/index.d.ts"),
        "/project/node_modules/pkg/index.d.ts"
    );
}

// Go: requestfilesystem_test.go:1314 TestRequestFileSystem/layered cache adds changes and blocks removed entries
#[test]
fn layered_cache_adds_changes_and_blocks_removed_entries() {
    let host = from_map(&[], true);
    let base = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[
                ("/keep.ts", "keep"),
                ("/change.ts", "old"),
                ("/remove.ts", "remove"),
                ("/removed-dir/gone.ts", "gone"),
                ("/becomes-file/child.ts", "child"),
                ("/becomes-directory.ts", "file"),
            ]),
            ..Default::default()
        },
        &host,
        "/",
    ));

    let layered = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[
                ("/change.ts", "new"),
                ("/added.ts", "added"),
                ("/remove.ts", "replacement"),
                ("/removed-dir/replacement.ts", "replacement"),
                ("/becomes-file", "file"),
                ("/becomes-directory.ts/child.ts", "child"),
            ]),
            directories: directories(vec![(
                "/",
                listing(
                    &["added.ts", "becomes-file", "change.ts", "remove.ts"],
                    &["becomes-directory.ts", "removed-dir"],
                ),
            )]),
            removed_paths: removed(&["/remove.ts", "/removed-dir"]),
            ..Default::default()
        },
        &base,
        "/",
    ));

    for (path, expected) in [
        ("/keep.ts", "keep"),
        ("/change.ts", "new"),
        ("/added.ts", "added"),
        ("/remove.ts", "replacement"),
        ("/removed-dir/replacement.ts", "replacement"),
        ("/becomes-file", "file"),
        ("/becomes-directory.ts/child.ts", "child"),
    ] {
        let (contents, ok) = layered.read_file(path);
        assert!(ok, "{path}");
        assert_eq!(contents, expected);
    }
    assert!(layered.file_exists("/remove.ts"));
    assert!(layered.directory_exists("/removed-dir"));
    assert!(!layered.file_exists("/removed-dir/gone.ts"));
    assert!(layered.stat("/remove.ts").is_some());
    assert!(layered.stat("/removed-dir/replacement.ts").is_some());
    assert_eq!(
        layered.realpath("/removed-dir/replacement.ts"),
        "/removed-dir/replacement.ts"
    );
    assert!(layered.file_exists("/becomes-file"));
    assert!(!layered.directory_exists("/becomes-file"));
    assert!(!layered.file_exists("/becomes-directory.ts"));
    assert!(layered.directory_exists("/becomes-directory.ts"));
    assert_eq!(
        layered.get_accessible_entries("/").files,
        vec!["added.ts", "becomes-file", "change.ts", "remove.ts"]
    );
    assert_eq!(
        layered.get_accessible_entries("/").directories,
        vec!["becomes-directory.ts", "removed-dir"]
    );
}

// Go: requestfilesystem_test.go:1374 TestRequestFileSystem/new layers override targets of inherited symlinks
#[test]
fn new_layers_override_targets_of_inherited_symlinks() {
    let host = from_map(&[], true);
    let base = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[
                ("/target/change.ts", "old"),
                ("/target/keep.ts", "keep"),
                ("/target/remove.ts", "remove"),
            ]),
            symlinks: symlinks(&[("/link", "/target", false)]),
            ..Default::default()
        },
        &host,
        "/",
    ));

    let layered = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/target/change.ts", "new"), ("/target/added.ts", "added")]),
            removed_paths: removed(&["/target/remove.ts"]),
            ..Default::default()
        },
        &base,
        "/",
    ));

    let (contents, ok) = layered.read_file("/link/change.ts");
    assert!(ok);
    assert_eq!(contents, "new");
    let (contents, ok) = layered.read_file("/link/added.ts");
    assert!(ok);
    assert_eq!(contents, "added");
    let (_, ok) = layered.read_file("/link/remove.ts");
    assert!(!ok);
    assert_eq!(
        layered.get_accessible_entries("/link").files,
        vec!["added.ts", "change.ts", "keep.ts"]
    );
}

// Go: requestfilesystem_test.go:1411 TestRequestFileSystem/alias tombstones take precedence over inherited symlink targets
#[test]
fn alias_tombstones_take_precedence_over_inherited_symlink_targets() {
    let host = from_map(&[], true);
    let base = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/target/file.ts", "old")]),
            symlinks: symlinks(&[("/link", "/target", false)]),
            ..Default::default()
        },
        &host,
        "/",
    ));

    let layered = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/target/file.ts", "new")]),
            removed_paths: removed(&["/link"]),
            ..Default::default()
        },
        &base,
        "/",
    ));

    let (_, ok) = layered.read_file("/link/file.ts");
    assert!(!ok);
    assert!(!layered.file_exists("/link/file.ts"));
    assert!(!layered.directory_exists("/link"));
    assert!(layered.stat("/link/file.ts").is_none());
    assert_eq!(layered.get_accessible_entries("/link").files.len(), 0);
}

// Go: requestfilesystem_test.go:1442 TestRequestFileSystem/alias tombstones take precedence over same-layer symlink targets
#[test]
fn alias_tombstones_take_precedence_over_same_layer_symlink_targets() {
    let host = from_map(&[("/host-target/file.ts", "host")], true);
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/target/file.ts", "memory")]),
            symlinks: symlinks(&[
                ("/link", "/target", false),
                ("/host-link", "/host-target", true),
            ]),
            removed_paths: removed(&["/link/file.ts", "/host-link/file.ts"]),
            ..Default::default()
        },
        &host,
        "/",
    ));

    for path in ["/link/file.ts", "/host-link/file.ts"] {
        let (_, ok) = file_system.read_file(path);
        assert!(!ok, "{path}");
        assert!(!file_system.file_exists(path), "{path}");
        assert!(file_system.stat(path).is_none(), "{path}");
    }
    assert_eq!(file_system.get_accessible_entries("/link").files.len(), 0);
    assert_eq!(
        file_system.get_accessible_entries("/host-link").files.len(),
        0
    );
}

// Go: requestfilesystem_test.go:1470 TestRequestFileSystem/compaction preserves overlays addressed through inherited symlinks
#[test]
fn compaction_preserves_overlays_addressed_through_inherited_symlinks() {
    let host = from_map(&[], true);
    let base_fs = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/target/remove.ts", "remove")]),
            symlinks: symlinks(&[("/link", "/target", false)]),
            ..Default::default()
        },
        &host,
        "/",
    ));

    let layered_fs = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[]),
            removed_paths: removed(&["/link/remove.ts"]),
            ..Default::default()
        },
        &base_fs,
        "/",
    ));
    let layered = get_request_file_system(&*layered_fs).unwrap();

    let (_, ok) = layered.read_file("/link/remove.ts");
    assert!(!ok);
}

// Go: requestfilesystem_test.go:1496 TestRequestFileSystem/compaction removes tombstones from explicit listings
#[test]
fn compaction_removes_tombstones_from_explicit_listings() {
    let host = from_map(&[], true);
    let base_fs = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/dir/remove.ts", "remove")]),
            directories: directories(vec![("/dir", listing(&["remove.ts"], &[]))]),
            ..Default::default()
        },
        &host,
        "/",
    ));

    let layered_fs = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[]),
            removed_paths: removed(&["/dir/remove.ts"]),
            ..Default::default()
        },
        &base_fs,
        "/",
    ));
    let layered = get_request_file_system(&*layered_fs).unwrap();
    assert_eq!(layered.get_accessible_entries("/dir").files.len(), 0);
}

// Go: requestfilesystem_test.go:1520 TestRequestFileSystem/compaction allows recreating a path removed through an inherited symlink
#[test]
fn compaction_allows_recreating_a_path_removed_through_an_inherited_symlink() {
    let host = from_map(&[], true);
    let base_fs = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/target/recreated.ts", "base")]),
            symlinks: symlinks(&[("/link", "/target", false)]),
            ..Default::default()
        },
        &host,
        "/",
    ));

    let removed_fs = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            removed_paths: removed(&["/link/recreated.ts"]),
            ..Default::default()
        },
        &base_fs,
        "/",
    ));

    let recreated_fs = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/link/recreated.ts", "recreated")]),
            ..Default::default()
        },
        &removed_fs,
        "/",
    ));
    let recreated = get_request_file_system(&*recreated_fs).unwrap();
    let (contents, ok) = recreated.read_file("/link/recreated.ts");
    assert!(ok);
    assert_eq!(contents, "recreated");
}

// Go: requestfilesystem_test.go:1553 TestRequestFileSystem/compaction allows recreating a descendant of a path removed through an inherited symlink
#[test]
fn compaction_allows_recreating_a_descendant_of_a_path_removed_through_an_inherited_symlink() {
    let host = from_map(&[], true);
    let base = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/target/dir/existing.ts", "existing")]),
            symlinks: symlinks(&[("/link", "/target", false)]),
            ..Default::default()
        },
        &host,
        "/",
    ));

    let removed_fs = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            removed_paths: removed(&["/link/dir"]),
            ..Default::default()
        },
        &base,
        "/",
    ));

    let recreated = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/link/dir/recreated.ts", "recreated")]),
            ..Default::default()
        },
        &removed_fs,
        "/",
    ));
    let (contents, ok) = recreated.read_file("/link/dir/recreated.ts");
    assert!(ok);
    assert_eq!(contents, "recreated");
    assert!(!recreated.file_exists("/link/dir/existing.ts"));
    assert_eq!(
        recreated.get_accessible_entries("/link/dir").files,
        vec!["recreated.ts"]
    );
    assert_eq!(
        recreated.get_accessible_entries("/link").directories,
        vec!["dir"]
    );
}

// Go: requestfilesystem_test.go:1588 TestRequestFileSystem/files replacing inherited symlink target directories have empty listings
#[test]
fn files_replacing_inherited_symlink_target_directories_have_empty_listings() {
    let host = from_map(&[], true);
    let base = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/target/item/child.ts", "child")]),
            symlinks: symlinks(&[("/link", "/target", false)]),
            ..Default::default()
        },
        &host,
        "/",
    ));

    let layered = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/target/item", "file")]),
            ..Default::default()
        },
        &base,
        "/",
    ));

    assert!(layered.file_exists("/link/item"));
    assert!(!layered.directory_exists("/link/item"));
    assert_eq!(layered.get_accessible_entries("/link/item").files.len(), 0);
    assert_eq!(
        layered
            .get_accessible_entries("/link/item")
            .directories
            .len(),
        0
    );
}

// Go: requestfilesystem_test.go:1616 TestRequestFileSystem/cache tombstones block host hits
#[test]
fn cache_tombstones_block_host_hits() {
    let base = tracking(from_map(
        &[("/remove.ts", "host"), ("/removed-dir/gone.ts", "host")],
        true,
    ));
    let base_fs: Rc<dyn Fs> = base.clone();
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[]),
            removed_paths: removed(&["/remove.ts", "/removed-dir"]),
            ..Default::default()
        },
        &base_fs,
        "/",
    ));
    clear_seen(&base);

    assert!(!file_system.file_exists("/remove.ts"));
    assert!(!file_system.directory_exists("/removed-dir"));
    assert!(!file_system.file_exists("/removed-dir/gone.ts"));
    assert!(seen_is_empty(&base));
}

// Go: requestfilesystem_test.go:1638 TestRequestFileSystem/compacted filesystem layers retain host fallback
#[test]
fn compacted_filesystem_layers_retain_host_fallback() {
    let host = from_map(
        &[
            ("/host.ts", "host"),
            ("/removed.ts", "host removed"),
            ("/sealed/host.ts", "hidden from listing"),
            ("/open/host.ts", "host listing"),
            ("/open/layer-listed.ts", "host listed"),
        ],
        true,
    );
    let base_fs = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[
                ("/inherited.ts", "inherited"),
                ("/sealed/inherited.ts", "sealed inherited"),
            ]),
            directories: directories(vec![("/sealed", listing(&["inherited.ts"], &[]))]),
            removed_paths: removed(&["/removed.ts"]),
            ..Default::default()
        },
        &host,
        "/",
    ));

    let layered_fs = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/added.ts", "added"), ("/sealed/added.ts", "sealed added")]),
            directories: directories(vec![("/open", listing(&["layer-listed.ts"], &[]))]),
            ..Default::default()
        },
        &base_fs,
        "/",
    ));
    let layered = get_request_file_system(&*layered_fs).unwrap();
    assert!(Rc::ptr_eq(&layered.base, &host));
    assert_eq!(layered.kind, Kind::LAYER);

    for (path, expected) in [
        ("/host.ts", "host"),
        ("/inherited.ts", "inherited"),
        ("/added.ts", "added"),
    ] {
        let (contents, ok) = layered.read_file(path);
        assert!(ok, "{path}");
        assert_eq!(contents, expected);
    }
    let (_, ok) = layered.read_file("/removed.ts");
    assert!(!ok);
    assert_eq!(
        layered.get_accessible_entries("/sealed").files,
        vec!["added.ts", "inherited.ts"]
    );
    assert_eq!(
        layered.get_accessible_entries("/open").files,
        vec!["layer-listed.ts"]
    );
}

// Go: requestfilesystem_test.go:1690 TestRequestFileSystem/compacting a filesystem layer over a full filesystem produces a full filesystem
#[test]
fn compacting_a_filesystem_layer_over_a_full_filesystem_produces_a_full_filesystem() {
    let host = from_map(&[("/host.ts", "host")], true);
    let base_fs = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/target/inherited.ts", "inherited")]),
            directories: directories(vec![("/target", listing(&["inherited.ts"], &[]))]),
            symlinks: symlinks(&[("/link", "/target", false)]),
            ..Default::default()
        },
        &host,
        "/",
    ));

    let layered_fs = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/target/added.ts", "added")]),
            ..Default::default()
        },
        &base_fs,
        "/",
    ));
    let layered = get_request_file_system(&*layered_fs).unwrap();
    assert_eq!(layered.kind, Kind::FULL);
    assert!(Rc::ptr_eq(&layered.base, &host));

    for (path, expected) in [
        ("/link/inherited.ts", "inherited"),
        ("/link/added.ts", "added"),
    ] {
        let (contents, ok) = layered.read_file(path);
        assert!(ok, "{path}");
        assert_eq!(contents, expected);
    }
    let (_, ok) = layered.read_file("/host.ts");
    assert!(!ok);
}

// Go: requestfilesystem_test.go:1732 TestRequestFileSystem/memory routes explicit host symlinks to the host only through the link
#[test]
fn memory_routes_explicit_host_symlinks_to_the_host_only_through_the_link() {
    let base = tracking(from_map(
        &[
            (
                "/host/node_modules/pkg/index.d.ts",
                "export declare const hostValue: string;",
            ),
            ("/host/outside.ts", "outside"),
        ],
        true,
    ));
    let base_fs: Rc<dyn Fs> = base.clone();
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/project/index.ts", r#"import { hostValue } from "pkg";"#)]),
            symlinks: symlinks(&[("/project/node_modules", "/host/node_modules", true)]),
            ..Default::default()
        },
        &base_fs,
        "/",
    ));

    let (_, ok) = file_system.read_file("/host/outside.ts");
    assert!(!ok);
    assert!(!seen(&base, "/host/outside.ts"));

    let (contents, ok) = file_system.read_file("/project/node_modules/pkg/index.d.ts");
    assert!(ok);
    assert_eq!(contents, "export declare const hostValue: string;");
    assert!(seen(&base, "/host/node_modules/pkg/index.d.ts"));
    assert_eq!(
        file_system.realpath("/project/node_modules/pkg/index.d.ts"),
        "/host/node_modules/pkg/index.d.ts"
    );

    let entries = file_system.get_accessible_entries("/project");
    assert_eq!(entries.directories, vec!["node_modules"]);
    assert!(is_symlink(&entries, "node_modules"));
}

// Go: requestfilesystem_test.go:1765 TestRequestFileSystem/layered host symlinks bypass snapshot bases
#[test]
fn layered_host_symlinks_bypass_snapshot_bases() {
    let host = tracking(from_map(&[("/host/pkg/index.d.ts", "host")], true));
    let host_fs: Rc<dyn Fs> = host.clone();
    let base = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/memory.ts", "memory")]),
            ..Default::default()
        },
        &host_fs,
        "/",
    ));

    let layered = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[]),
            symlinks: symlinks(&[("/project/pkg", "/host/pkg", true)]),
            ..Default::default()
        },
        &base,
        "/",
    ));

    let (contents, ok) = layered.read_file("/project/pkg/index.d.ts");
    assert!(ok);
    assert_eq!(contents, "host");
    assert!(layered.file_exists("/project/pkg/index.d.ts"));
    assert!(layered.directory_exists("/project/pkg"));
    assert_eq!(
        layered.get_accessible_entries("/project/pkg").files,
        vec!["index.d.ts"]
    );
    assert_eq!(
        layered.realpath("/project/pkg/index.d.ts"),
        "/host/pkg/index.d.ts"
    );
    let info = layered.stat("/project/pkg/index.d.ts");
    assert!(info.is_some());
    assert_eq!(info.unwrap().name(), "index.d.ts");
    assert!(seen(&host, "/host/pkg/index.d.ts"));
}

// Go: requestfilesystem_test.go:1800 TestRequestFileSystem/inherited host symlinks bypass newer cache entries at the target
#[test]
fn inherited_host_symlinks_bypass_newer_cache_entries_at_the_target() {
    let host = from_map(
        &[
            ("/host/pkg/host.ts", "host"),
            ("/host/pkg/removed.ts", "removed"),
        ],
        true,
    );
    let base = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[]),
            symlinks: symlinks(&[("/link", "/host/pkg", true)]),
            ..Default::default()
        },
        &host,
        "/",
    ));

    let layered = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            removed_paths: removed(&["/link/removed.ts"]),
            files: files(&[
                ("/host/pkg/host.ts", "cache"),
                ("/host/pkg/cache-only.ts", "cache only"),
            ]),
            ..Default::default()
        },
        &base,
        "/",
    ));

    let (contents, ok) = layered.read_file("/link/host.ts");
    assert!(ok);
    assert_eq!(contents, "host");
    assert!(!layered.file_exists("/link/cache-only.ts"));
    assert!(!layered.file_exists("/link/removed.ts"));
    assert_eq!(
        layered.stat("/link/host.ts").unwrap().size(),
        "host".len() as i64
    );
    assert_eq!(
        layered.get_accessible_entries("/link").files,
        vec!["host.ts"]
    );
}

// Go: requestfilesystem_test.go:1834 TestRequestFileSystem/canonical path collisions are rejected
#[test]
fn canonical_path_collisions_are_rejected() {
    let base = from_map(&[], false);

    error_contains(
        new_request_file_system(
            &RequestFileSystem {
                kind: Kind::FULL,
                files: files(&[(r"C:\Repo\file.ts", "first"), ("c:/repo/file.ts", "second")]),
                ..Default::default()
            },
            &base,
            r"C:\Workspace",
        ),
        "duplicate request filesystem file path",
    );

    error_contains(
        new_request_file_system(
            &RequestFileSystem {
                kind: Kind::FULL,
                files: files(&[]),
                directories: directories(vec![
                    (r"C:\Repo", listing(&[], &[])),
                    ("c:/repo/.", listing(&[], &[])),
                ]),
                ..Default::default()
            },
            &base,
            r"C:\Workspace",
        ),
        "duplicate request filesystem directory path",
    );

    error_contains(
        new_request_file_system(
            &RequestFileSystem {
                kind: Kind::FULL,
                files: files(&[]),
                symlinks: symlinks(&[
                    (r"C:\Repo\link", r"C:\Target", false),
                    ("c:/repo/link", r"C:\Other", false),
                ]),
                ..Default::default()
            },
            &base,
            r"C:\Workspace",
        ),
        "duplicate request filesystem symlink path",
    );
}

// Go: requestfilesystem_test.go:1868 TestRequestFileSystem/symlink cycles are treated as missing
#[test]
fn symlink_cycles_are_treated_as_missing() {
    let base = tracking(from_map(&[("/host.ts", "host")], true));
    let base_fs: Rc<dyn Fs> = base.clone();
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[]),
            symlinks: symlinks(&[("/a", "/b", false), ("/b", "/a", false)]),
            ..Default::default()
        },
        &base_fs,
        "/",
    ));

    let (_, ok) = file_system.read_file("/a/file.ts");
    assert!(!ok);
    assert!(!file_system.directory_exists("/a"));
    assert_eq!(file_system.realpath("/a"), "/a");
    assert!(seen_is_empty(&base));
}

// Go: requestfilesystem_test.go:1890 TestRequestFileSystem/posix relative symlink targets resolve from the link directory
#[test]
fn posix_relative_symlink_targets_resolve_from_the_link_directory() {
    let base = tracking(from_map(&[], true));
    let base_fs: Rc<dyn Fs> = base.clone();
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[(
                "/packages/pkg/index.d.ts",
                "export declare const value: number;",
            )]),
            symlinks: symlinks(&[("/project/pkg", "../packages/pkg", false)]),
            ..Default::default()
        },
        &base_fs,
        r"C:\Workspace",
    ));

    let (contents, ok) = file_system.read_file("/project/pkg/index.d.ts");
    assert!(ok);
    assert_eq!(contents, "export declare const value: number;");
    assert_eq!(
        file_system.realpath("/project/pkg/index.d.ts"),
        "/packages/pkg/index.d.ts"
    );
    assert!(seen_is_empty(&base));
}

// Go: requestfilesystem_test.go:1911 TestRequestFileSystem/vscode document URI paths support listings symlinks and tombstones
#[test]
fn vscode_document_uri_paths_support_listings_symlinks_and_tombstones() {
    let base = tracking(from_map(&[], true));
    let base_fs: Rc<dyn Fs> = base.clone();
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[
                (
                    "vscode-remote://ssh-remote+host/workspace/src/index.ts",
                    "index",
                ),
                (
                    "vscode-remote://ssh-remote+host/workspace/packages/pkg/a.ts",
                    "package",
                ),
            ]),
            symlinks: symlinks(&[(
                "vscode-remote://ssh-remote+host/workspace/src/pkg",
                "../packages/pkg",
                false,
            )]),
            removed_paths: removed(&[
                "vscode-remote://ssh-remote+host/workspace/packages/pkg/removed.ts",
            ]),
            ..Default::default()
        },
        &base_fs,
        "/",
    ));

    let (contents, ok) =
        file_system.read_file("vscode-remote://ssh-remote+host/workspace/src/index.ts");
    assert!(ok);
    assert_eq!(contents, "index");
    let (contents, ok) =
        file_system.read_file("vscode-remote://ssh-remote+host/workspace/src/pkg/a.ts");
    assert!(ok);
    assert_eq!(contents, "package");
    assert_eq!(
        file_system.realpath("vscode-remote://ssh-remote+host/workspace/src/pkg/a.ts"),
        "vscode-remote://ssh-remote+host/workspace/packages/pkg/a.ts"
    );
    assert_eq!(
        file_system
            .get_accessible_entries("vscode-remote://ssh-remote+host/workspace/src")
            .files,
        vec!["index.ts"]
    );
    assert_eq!(
        file_system
            .get_accessible_entries("vscode-remote://ssh-remote+host/workspace/src")
            .directories,
        vec!["pkg"]
    );
    assert!(
        !file_system.file_exists("vscode-remote://ssh-remote+host/workspace/src/pkg/removed.ts")
    );
    assert!(seen_is_empty(&base));
}

// Go: requestfilesystem_test.go:1954 TestRequestFileSystem/windows paths resolve symlinks case insensitively
#[test]
fn windows_paths_resolve_symlinks_case_insensitively() {
    let base = tracking(from_map(&[("C:/Host/outside.ts", "outside")], false));
    let base_fs: Rc<dyn Fs> = base.clone();
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[(
                r"C:\Repo\Packages\Pkg\Index.d.ts",
                "export declare const windowsValue: number;",
            )]),
            directories: directories(vec![(
                r"C:\Repo\Project\node_modules",
                listing(&[], &["pkg"]),
            )]),
            symlinks: symlinks(&[
                (
                    r"C:\Repo\Project\node_modules\PKG",
                    r"..\..\Packages\Pkg",
                    false,
                ),
                (
                    r"C:\Repo\Project\Current.d.ts",
                    r"..\Packages\Pkg\Index.d.ts",
                    false,
                ),
            ]),
            ..Default::default()
        },
        &base_fs,
        r"C:\Workspace",
    ));

    let (contents, ok) = file_system.read_file(r"c:\repo\project\NODE_MODULES\pkg\INDEX.D.TS");
    assert!(ok);
    assert_eq!(contents, "export declare const windowsValue: number;");
    let (contents, ok) = file_system.read_file(r"C:\REPO\PROJECT\current.d.ts");
    assert!(ok);
    assert_eq!(contents, "export declare const windowsValue: number;");
    assert_eq!(
        file_system.realpath(r"c:\repo\project\node_modules\pkg\index.d.ts"),
        "C:/Repo/Packages/Pkg/index.d.ts"
    );

    let entries = file_system.get_accessible_entries(r"c:\REPO\project\NODE_MODULES");
    assert_eq!(entries.directories, vec!["PKG"]);
    assert!(is_symlink(&entries, "PKG"));
    assert!(seen_is_empty(&base));
}

// Go: requestfilesystem_test.go:1993 TestRequestFileSystem/case insensitive symlink matching handles unicode byte length changes
#[test]
fn case_insensitive_symlink_matching_handles_unicode_byte_length_changes() {
    let base = tracking(from_map(&[], false));
    let base_fs: Rc<dyn Fs> = base.clone();
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("C:/Repo/target.ts", "target")]),
            // The link name ends in U+212A KELVIN SIGN, as in Go.
            symlinks: symlinks(&[("C:/Repo/\u{212A}", "C:/Repo/target.ts", false)]),
            ..Default::default()
        },
        &base_fs,
        "C:/Repo",
    ));

    let (contents, ok) = file_system.read_file("c:/repo/k");
    assert!(ok);
    assert_eq!(contents, "target");
}

// Go: requestfilesystem_test.go:2012 TestRequestFileSystem/full request filesystems are immutable after eager compaction
#[test]
fn full_request_filesystems_are_immutable_after_eager_compaction() {
    let host = from_map(&[("/host.ts", "host")], true);
    let memory = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/src/a.ts", "a")]),
            ..Default::default()
        },
        &host,
        "/",
    ));
    assert!(is_err_invalid(memory.write_file("/src/b.ts", "b")));
    assert!(is_err_invalid(memory.append_file("/src/a.ts", "b")));
    assert!(is_err_invalid(memory.remove("/src")));
    let (contents, ok) = memory.read_file("/src/a.ts");
    assert!(ok);
    assert_eq!(contents, "a");

    let cache = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[]),
            ..Default::default()
        },
        &memory,
        "/",
    ));
    assert_eq!(imp(&cache).kind, Kind::FULL);
    assert!(is_err_invalid(cache.write_file("/written.ts", "written")));
}

// Go: requestfilesystem_test.go:2040 TestRequestFileSystem/layer request filesystems write through after eager compaction
#[test]
fn layer_request_filesystems_write_through_after_eager_compaction() {
    let host = from_map(&[], true);
    let base = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[]),
            ..Default::default()
        },
        &host,
        "/",
    ));
    let cache = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[]),
            ..Default::default()
        },
        &base,
        "/",
    ));
    assert_eq!(imp(&cache).kind, Kind::LAYER);
    cache.write_file("/written.ts", "written").unwrap();
    cache.append_file("/written.ts", " appended").unwrap();
    let (contents, ok) = host.read_file("/written.ts");
    assert!(ok);
    assert_eq!(contents, "written appended");
    cache.remove("/written.ts").unwrap();
    assert!(!host.file_exists("/written.ts"));
}

// Go: requestfilesystem_test.go:2063 TestRequestFileSystem/cache mutations follow inherited request symlinks
#[test]
fn cache_mutations_follow_inherited_request_symlinks() {
    let host = from_map(
        &[
            ("/target/write.ts", "target"),
            ("/target/append.ts", "target"),
            ("/target/remove.ts", "target"),
            ("/target/times.ts", "target"),
            ("/link/write.ts", "alias"),
            ("/link/append.ts", "alias"),
            ("/link/remove.ts", "alias"),
            ("/link/times.ts", "alias"),
        ],
        true,
    );
    let base = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[]),
            symlinks: symlinks(&[("/link", "/target", false)]),
            ..Default::default()
        },
        &host,
        "/",
    ));
    let cache = nil_error(new_layered_request_file_system(
        &request(Kind::LAYER),
        &base,
        "/",
    ));

    cache.write_file("/link/write.ts", "written").unwrap();
    let (contents, ok) = host.read_file("/target/write.ts");
    assert!(ok);
    assert_eq!(contents, "written");

    cache.append_file("/link/append.ts", " appended").unwrap();
    let (contents, ok) = host.read_file("/target/append.ts");
    assert!(ok);
    assert_eq!(contents, "target appended");

    cache.remove("/link/remove.ts").unwrap();
    assert!(!host.file_exists("/target/remove.ts"));

    let modified = UNIX_EPOCH + Duration::from_secs(123);
    cache
        .chtimes("/link/times.ts", Some(modified), Some(modified))
        .unwrap();
    assert_eq!(
        host.stat("/target/times.ts").unwrap().mod_time(),
        Some(modified)
    );
}

// Go: requestfilesystem_test.go:2104 TestRequestFileSystem/mixed windows and posix roots support cross-root and relative symlinks
#[test]
fn mixed_windows_and_posix_roots_support_cross_root_and_relative_symlinks() {
    let base = tracking(from_map(
        &[(
            "C:/Host/node_modules/host-pkg/index.d.ts",
            "export declare const hostValue: boolean;",
        )],
        false,
    ));
    let base_fs: Rc<dyn Fs> = base.clone();
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[
                (
                    r"C:\Repo\Packages\windows-pkg\index.d.ts",
                    "export declare const windowsValue: number;",
                ),
                (
                    "/repo/packages/posix-pkg/index.d.ts",
                    "export declare const posixValue: string;",
                ),
            ]),
            symlinks: symlinks(&[
                // Cross between drive-letter and POSIX roots in both directions.
                (
                    r"C:\Repo\Project\node_modules\posix-pkg",
                    "/repo/packages/posix-pkg",
                    false,
                ),
                (
                    "/repo/project/node_modules/windows-pkg",
                    r"C:\Repo\Packages\windows-pkg",
                    false,
                ),
                // Windows symlink targets read from disk may be relative to the link's directory.
                (
                    r"C:\Repo\Project\windows-pkg.d.ts",
                    r"..\Packages\windows-pkg\index.d.ts",
                    false,
                ),
                (
                    r"C:\Repo\Project\node_modules\host-pkg",
                    r"..\..\..\Host\node_modules\host-pkg",
                    true,
                ),
            ]),
            ..Default::default()
        },
        &base_fs,
        r"C:\Workspace",
    ));

    let (contents, ok) =
        file_system.read_file(r"c:\REPO\project\NODE_MODULES\POSIX-PKG\INDEX.D.TS");
    assert!(ok);
    assert_eq!(contents, "export declare const posixValue: string;");
    let (contents, ok) = file_system.read_file("/REPO/PROJECT/NODE_MODULES/WINDOWS-PKG/INDEX.D.TS");
    assert!(ok);
    assert_eq!(contents, "export declare const windowsValue: number;");
    let (contents, ok) = file_system.read_file(r"c:\repo\project\WINDOWS-PKG.D.TS");
    assert!(ok);
    assert_eq!(contents, "export declare const windowsValue: number;");
    let (contents, ok) = file_system.read_file(r"C:\Repo\Project\node_modules\HOST-PKG\index.d.ts");
    assert!(ok);
    assert_eq!(contents, "export declare const hostValue: boolean;");

    assert_eq!(
        file_system.realpath(r"c:\repo\project\node_modules\posix-pkg\index.d.ts"),
        "/repo/packages/posix-pkg/index.d.ts"
    );
    assert_eq!(
        file_system.realpath("/repo/project/node_modules/windows-pkg/index.d.ts"),
        "C:/Repo/Packages/windows-pkg/index.d.ts"
    );
    assert!(seen(&base, "C:/Host/node_modules/host-pkg/index.d.ts"));
}

/// Go `assert.DeepEqual(t, entries, vfs.Entries{...})`.
pub(crate) fn assert_entries(
    entries: &vfs::Entries,
    files: &[&str],
    directories: &[&str],
    symlinks: Option<&[&str]>,
) {
    assert_eq!(
        comparable_entries(entries),
        expected_entries(files, directories, symlinks)
    );
}
