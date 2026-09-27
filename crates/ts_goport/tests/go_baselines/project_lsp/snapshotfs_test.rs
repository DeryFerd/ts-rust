//! Port of Go `internal/project/snapshotfs_test.go` (`TestSnapshotFSBuilder`,
//! `TestSnapshotFS`, `TestSourceFS`, `TestAutoImportBuilderFS`,
//! `TestRealpathAliasLifecycle`, `TestExpandAndFilterWatchEvents`). No
//! program is built, so the tests run in the test process.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use ts_goport::flags::ScriptKind;
use ts_goport::frontend::tspath::Path;
use ts_goport::frontend::vfs::Fs;
use ts_goport::lsp::lsproto;
use ts_goport::project::dirty::CloneableMap;
use ts_goport::project::{
    AutoImportBuilderFS, DiskFile, FileBase, FileChangeSummary, FileContent, FileSource, Overlay,
    RealpathAliasSet, SnapshotFS, SnapshotFSBuilder, new_disk_file, new_snapshot_fs_builder,
    new_source_fs,
};

use super::util::uri;
use crate::support::vfstest::{self, MapFile};

type DiskFiles = FxHashMap<Path, Rc<RefCell<DiskFile>>>;
type Dirs = FxHashMap<Path, CloneableMap<Path, String>>;
type Aliases = FxHashMap<Path, Rc<RefCell<RealpathAliasSet>>>;
type Overlays = IndexMap<Path, Rc<Overlay>>;

fn p(s: &str) -> Path {
    Path(s.to_string())
}

// Go: snapshotfs_test.go:18 toPath
fn to_path() -> Rc<dyn Fn(&str) -> Path> {
    Rc::new(|file_name: &str| Path(file_name.to_string()))
}

fn text_fs(entries: &[(&str, &str)], case_sensitive: bool) -> Rc<dyn Fs> {
    vfstest::from_map(entries.iter().copied(), case_sensitive)
}

fn any_fs(entries: Vec<(&str, MapFile)>, case_sensitive: bool) -> Rc<dyn Fs> {
    vfstest::from_map(entries, case_sensitive)
}

fn text(s: &str) -> MapFile {
    MapFile::from(s)
}

/// Go `newSnapshotFSBuilder(fs, prevOverlays{}, overlays, diskFiles, diskDirectories, aliases, UTF16, toPath)`.
fn builder(
    fs: Rc<dyn Fs>,
    overlays: Overlays,
    disk_files: DiskFiles,
    dirs: Dirs,
    aliases: Aliases,
) -> Rc<SnapshotFSBuilder> {
    new_snapshot_fs_builder(
        fs,
        IndexMap::default(), // prevOverlays
        overlays,
        disk_files,
        dirs,
        aliases,
        lsproto::PositionEncodingKind::UTF16,
        to_path(),
    )
}

fn empty_builder(fs: Rc<dyn Fs>) -> Rc<SnapshotFSBuilder> {
    builder(
        fs,
        Overlays::default(),
        DiskFiles::default(),
        Dirs::default(),
        Aliases::default(),
    )
}

/// Go `map[tspath.Path]dirty.CloneableMap[tspath.Path, string]{...}`.
fn dirs(entries: &[(&str, &[(&str, &str)])]) -> Dirs {
    entries
        .iter()
        .map(|(dir, children)| {
            let map: FxHashMap<Path, String> = children
                .iter()
                .map(|(k, v)| (p(k), v.to_string()))
                .collect();
            (p(dir), CloneableMap(Rc::new(RefCell::new(map))))
        })
        .collect()
}

/// Go `map[tspath.Path]*diskFile{path: newDiskFile(path, content), ...}`.
fn disk_files(entries: &[(&str, &str)]) -> DiskFiles {
    entries
        .iter()
        .map(|(name, content)| (p(name), new_disk_file(name, content.to_string())))
        .collect()
}

/// Go `&Overlay{fileBase: fileBase{fileName: name, content: content}}`.
fn overlay(name: &str, content: &str) -> Rc<Overlay> {
    Rc::new(Overlay {
        file_base: FileBase {
            file_name: name.to_string(),
            content: content.to_string(),
            ..FileBase::default()
        },
        version: Cell::new(0),
        kind: ScriptKind::UNKNOWN,
        matches_disk_text: Cell::new(false),
    })
}

fn overlays(entries: &[(&str, &str)]) -> Overlays {
    entries
        .iter()
        .map(|(name, content)| (p(name), overlay(name, content)))
        .collect()
}

/// Go `snapshot.diskDirectories[dir][child]` presence.
fn dir_has(dirs: &Dirs, dir: &str, child: &str) -> bool {
    dirs.get(&p(dir))
        .is_some_and(|d| d.0.borrow().contains_key(&p(child)))
}

/// Go `builder.diskFiles.Load(path)` then `entry.Delete()`.
fn delete_disk_file(b: &SnapshotFSBuilder, path: &str) {
    if let (Some(entry), true) = b.disk_files.load(&p(path)) {
        entry.delete();
    }
}

fn file_content(file: Option<Rc<dyn ts_goport::project::FileHandle>>) -> String {
    file.expect("file should exist").content()
}

fn alias_has(aliases: &Aliases, realpath: &str, symlink: &str) -> bool {
    aliases
        .get(&p(realpath))
        .is_some_and(|set| set.borrow().paths.contains(&p(symlink)))
}

// ---------------------------------------------------------------------------
// TestSnapshotFSBuilder
// ---------------------------------------------------------------------------

// Go: snapshotfs_test.go:22 TestSnapshotFSBuilder/builds directory tree on file add
#[test]
fn builder_builds_directory_tree_on_file_add() {
    let b = empty_builder(text_fs(&[("/src/foo.ts", "const foo = 1;")], false));

    // Read the file to add it to the diskFiles
    assert_eq!(file_content(b.get_file("/src/foo.ts")), "const foo = 1;");

    // Finalize and check directories
    let (snapshot, changed) = b.finalize();
    assert!(changed, "should have changed");

    // /src should contain /src/foo.ts
    assert!(
        snapshot.disk_directories.contains_key(&p("/src")),
        "/src directory should exist"
    );
    assert!(
        dir_has(&snapshot.disk_directories, "/src", "/src/foo.ts"),
        "/src should contain /src/foo.ts"
    );

    // / should contain /src
    assert!(
        snapshot.disk_directories.contains_key(&p("/")),
        "/ directory should exist"
    );
    assert!(
        dir_has(&snapshot.disk_directories, "/", "/src"),
        "/ should contain /src"
    );
}

// Go: snapshotfs_test.go:62 TestSnapshotFSBuilder/builds nested directory tree
#[test]
fn builder_builds_nested_directory_tree() {
    let b = empty_builder(text_fs(
        &[("/src/nested/deep/file.ts", "export const x = 1;")],
        false,
    ));

    assert!(
        b.get_file("/src/nested/deep/file.ts").is_some(),
        "file should exist"
    );

    let (snapshot, changed) = b.finalize();
    assert!(changed, "should have changed");

    // Check the complete directory tree
    let d = &snapshot.disk_directories;
    assert!(dir_has(d, "/src/nested/deep", "/src/nested/deep/file.ts"));
    assert!(dir_has(d, "/src/nested", "/src/nested/deep"));
    assert!(dir_has(d, "/src", "/src/nested"));
    assert!(dir_has(d, "/", "/src"));
}

// Go: snapshotfs_test.go:97 TestSnapshotFSBuilder/removes directory entries on file delete
#[test]
fn builder_removes_directory_entries_on_file_delete() {
    let b = builder(
        text_fs(&[("/src/foo.ts", "const foo = 1;")], false),
        Overlays::default(),
        disk_files(&[("/src/foo.ts", "const foo = 1;")]),
        dirs(&[
            ("/", &[("/src", "src")]),
            ("/src", &[("/src/foo.ts", "foo.ts")]),
        ]),
        Aliases::default(),
    );

    // Mark the file for deletion by loading and deleting
    delete_disk_file(&b, "/src/foo.ts");

    let (snapshot, changed) = b.finalize();
    assert!(changed, "should have changed");

    // File should be deleted
    assert!(
        !snapshot.disk_files.contains_key(&p("/src/foo.ts")),
        "file should be deleted"
    );

    // Directory tree should be cleaned up
    assert!(
        !snapshot.disk_directories.contains_key(&p("/src")),
        "/src directory should be removed"
    );
    assert!(
        !snapshot.disk_directories.contains_key(&p("/")),
        "root directory should be removed"
    );
}

// Go: snapshotfs_test.go:147 TestSnapshotFSBuilder/removes only empty directories on file delete
#[test]
fn builder_removes_only_empty_directories_on_file_delete() {
    let b = builder(
        text_fs(
            &[
                ("/src/foo.ts", "const foo = 1;"),
                ("/src/bar.ts", "const bar = 2;"),
            ],
            false,
        ),
        Overlays::default(),
        disk_files(&[
            ("/src/foo.ts", "const foo = 1;"),
            ("/src/bar.ts", "const bar = 2;"),
        ]),
        dirs(&[
            ("/", &[("/src", "src")]),
            (
                "/src",
                &[("/src/foo.ts", "foo.ts"), ("/src/bar.ts", "bar.ts")],
            ),
        ]),
        Aliases::default(),
    );

    // Delete only foo.ts
    delete_disk_file(&b, "/src/foo.ts");

    let (snapshot, changed) = b.finalize();
    assert!(changed, "should have changed");

    assert!(
        !snapshot.disk_files.contains_key(&p("/src/foo.ts")),
        "foo.ts should be deleted"
    );
    assert!(
        snapshot.disk_files.contains_key(&p("/src/bar.ts")),
        "bar.ts should still exist"
    );

    // /src directory should still exist with bar.ts
    assert!(
        snapshot.disk_directories.contains_key(&p("/src")),
        "/src directory should still exist"
    );
    assert!(
        !dir_has(&snapshot.disk_directories, "/src", "/src/foo.ts"),
        "/src should not contain foo.ts"
    );
    assert!(
        dir_has(&snapshot.disk_directories, "/src", "/src/bar.ts"),
        "/src should contain bar.ts"
    );

    // root should still contain /src
    assert!(
        snapshot.disk_directories.contains_key(&p("/")),
        "root directory should still exist"
    );
    assert!(
        dir_has(&snapshot.disk_directories, "/", "/src"),
        "root should contain /src"
    );
}

// Go: snapshotfs_test.go:211 TestSnapshotFSBuilder/adds file to existing directory
#[test]
fn builder_adds_file_to_existing_directory() {
    let b = builder(
        text_fs(
            &[
                ("/src/foo.ts", "const foo = 1;"),
                ("/src/bar.ts", "const bar = 2;"),
            ],
            false,
        ),
        Overlays::default(),
        disk_files(&[("/src/foo.ts", "const foo = 1;")]),
        dirs(&[
            ("/", &[("/src", "src")]),
            ("/src", &[("/src/foo.ts", "foo.ts")]),
        ]),
        Aliases::default(),
    );

    // Read bar.ts to add it
    assert!(b.get_file("/src/bar.ts").is_some(), "bar.ts should exist");

    let (snapshot, changed) = b.finalize();
    assert!(changed, "should have changed");

    // /src should contain both files
    assert!(
        dir_has(&snapshot.disk_directories, "/src", "/src/foo.ts"),
        "/src should contain foo.ts"
    );
    assert!(
        dir_has(&snapshot.disk_directories, "/src", "/src/bar.ts"),
        "/src should contain bar.ts"
    );
}

// Go: snapshotfs_test.go:257 TestSnapshotFSBuilder/no change when no files added or deleted
#[test]
fn builder_no_change_when_no_files_added_or_deleted() {
    let b = builder(
        text_fs(&[("/src/foo.ts", "const foo = 1;")], false),
        Overlays::default(),
        disk_files(&[("/src/foo.ts", "const foo = 1;")]),
        dirs(&[
            ("/", &[("/src", "src")]),
            ("/src", &[("/src/foo.ts", "foo.ts")]),
        ]),
        Aliases::default(),
    );

    // Don't add or delete any files
    let (snapshot, changed) = b.finalize();
    assert!(!changed, "should not have changed");

    // Directories should remain the same
    assert!(dir_has(&snapshot.disk_directories, "/src", "/src/foo.ts"));
}

// Go: snapshotfs_test.go:296 TestSnapshotFSBuilder/overlay files are returned over disk files
#[test]
fn builder_overlay_files_are_returned_over_disk_files() {
    let b = builder(
        text_fs(&[("/src/foo.ts", "const foo = 1;")], false),
        overlays(&[("/src/foo.ts", "const foo = 999;")]),
        DiskFiles::default(),
        Dirs::default(),
        Aliases::default(),
    );

    // Should return overlay content
    assert_eq!(file_content(b.get_file("/src/foo.ts")), "const foo = 999;");
}

// Go: snapshotfs_test.go:325 TestSnapshotFSBuilder/multiple files added and deleted in single cycle
#[test]
fn builder_multiple_files_added_and_deleted_in_single_cycle() {
    let b = builder(
        text_fs(
            &[
                ("/src/a.ts", "const a = 1;"),
                ("/src/b.ts", "const b = 2;"),
                ("/lib/utils.ts", "export const util = 1;"),
                ("/lib/helpers.ts", "export const helper = 1;"),
                ("/other/single.ts", "const single = 1;"),
            ],
            false,
        ),
        Overlays::default(),
        disk_files(&[
            ("/src/a.ts", "const a = 1;"),
            ("/other/single.ts", "const single = 1;"),
        ]),
        dirs(&[
            ("/", &[("/src", "src"), ("/other", "other")]),
            ("/src", &[("/src/a.ts", "a.ts")]),
            ("/other", &[("/other/single.ts", "single.ts")]),
        ]),
        Aliases::default(),
    );

    // Add new files
    assert!(b.get_file("/src/b.ts").is_some());
    assert!(b.get_file("/lib/utils.ts").is_some());
    assert!(b.get_file("/lib/helpers.ts").is_some());

    // Delete existing files
    delete_disk_file(&b, "/src/a.ts");
    delete_disk_file(&b, "/other/single.ts");

    let (snapshot, changed) = b.finalize();
    assert!(changed, "should have changed");

    // Verify deleted files are gone
    assert!(
        !snapshot.disk_files.contains_key(&p("/src/a.ts")),
        "/src/a.ts should be deleted"
    );
    assert!(
        !snapshot.disk_files.contains_key(&p("/other/single.ts")),
        "/other/single.ts should be deleted"
    );

    // Verify added files exist
    assert!(
        snapshot.disk_files.contains_key(&p("/src/b.ts")),
        "/src/b.ts should exist"
    );
    assert!(
        snapshot.disk_files.contains_key(&p("/lib/utils.ts")),
        "/lib/utils.ts should exist"
    );
    assert!(
        snapshot.disk_files.contains_key(&p("/lib/helpers.ts")),
        "/lib/helpers.ts should exist"
    );

    let d = &snapshot.disk_directories;
    // Verify /other directory is cleaned up (was only entry deleted)
    assert!(
        !d.contains_key(&p("/other")),
        "/other directory should be removed"
    );

    // Verify /src still exists with b.ts (a.ts deleted, b.ts added)
    assert!(d.contains_key(&p("/src")), "/src directory should exist");
    assert!(
        !dir_has(d, "/src", "/src/a.ts"),
        "/src should not contain a.ts"
    );
    assert!(dir_has(d, "/src", "/src/b.ts"), "/src should contain b.ts");

    // Verify /lib was created with both files
    assert!(d.contains_key(&p("/lib")), "/lib directory should exist");
    assert!(
        dir_has(d, "/lib", "/lib/utils.ts"),
        "/lib should contain utils.ts"
    );
    assert!(
        dir_has(d, "/lib", "/lib/helpers.ts"),
        "/lib should contain helpers.ts"
    );

    // Verify root contains /src and /lib but not /other
    assert!(dir_has(d, "/", "/src"), "root should contain /src");
    assert!(dir_has(d, "/", "/lib"), "root should contain /lib");
    assert!(!dir_has(d, "/", "/other"), "root should not contain /other");
}

// Go: snapshotfs_test.go:427 TestSnapshotFSBuilder/overlay directories are computed from overlays
#[test]
fn builder_overlay_directories_are_computed_from_overlays() {
    let b = builder(
        text_fs(&[], false),
        overlays(&[
            ("/src/overlay.ts", "const x = 1;"),
            ("/src/nested/deep.ts", "const y = 2;"),
        ]),
        DiskFiles::default(),
        Dirs::default(),
        Aliases::default(),
    );

    let od = &b.overlay_directories;
    let has = |dir: &str, child: &str| od.get(&p(dir)).is_some_and(|d| d.contains_key(&p(child)));
    assert!(
        od.contains_key(&p("/src")),
        "/src overlay directory should exist"
    );
    assert!(
        has("/src", "/src/overlay.ts"),
        "/src should contain overlay.ts"
    );
    assert!(has("/src", "/src/nested"), "/src should contain nested/");

    assert!(
        od.contains_key(&p("/src/nested")),
        "/src/nested overlay directory should exist"
    );
    assert!(
        has("/src/nested", "/src/nested/deep.ts"),
        "/src/nested should contain deep.ts"
    );

    assert!(od.contains_key(&p("/")), "/ overlay directory should exist");
    assert!(has("/", "/src"), "/ should contain /src");
}

// Go: snapshotfs_test.go:470 TestSnapshotFSBuilder/GetAccessibleEntries combines disk and overlay
#[test]
fn builder_get_accessible_entries_combines_disk_and_overlay() {
    let b = builder(
        text_fs(&[("/src/disk.ts", "const disk = 1;")], false),
        overlays(&[("/src/overlay.ts", "const overlay = 1;")]),
        DiskFiles::default(),
        Dirs::default(),
        Aliases::default(),
    );

    let entries = b.get_accessible_entries("/src");

    // Should contain both disk file and overlay file (both as basenames)
    assert!(
        entries.files.iter().any(|f| f == "disk.ts"),
        "should contain disk.ts"
    );
    assert!(
        entries.files.iter().any(|f| f == "overlay.ts"),
        "should contain overlay.ts"
    );
}

// ---------------------------------------------------------------------------
// TestSnapshotFS
// ---------------------------------------------------------------------------

/// Go `&SnapshotFS{toPath, fs, overlays, overlayDirectories, diskFiles, diskDirectories}`.
fn snapshot_fs(
    fs: Rc<dyn Fs>,
    overlays: Overlays,
    overlay_directories: FxHashMap<Path, FxHashMap<Path, String>>,
    disk_files: DiskFiles,
    disk_directories: Dirs,
) -> Rc<SnapshotFS> {
    Rc::new(SnapshotFS {
        to_path: to_path(),
        fs,
        overlays,
        overlay_directories,
        disk_files,
        disk_directories,
        read_files: RefCell::default(),
        node_modules_realpath_aliases: Aliases::default(),
    })
}

// Go: snapshotfs_test.go:508 TestSnapshotFS/GetFile returns overlay file
#[test]
fn snapshot_fs_get_file_returns_overlay_file() {
    let s = snapshot_fs(
        text_fs(&[("/src/foo.ts", "disk content")], false),
        overlays(&[("/src/foo.ts", "overlay content")]),
        FxHashMap::default(),
        DiskFiles::default(),
        Dirs::default(),
    );
    assert_eq!(file_content(s.get_file("/src/foo.ts")), "overlay content");
}

// Go: snapshotfs_test.go:534 TestSnapshotFS/GetFile returns disk file when not in overlay
#[test]
fn snapshot_fs_get_file_returns_disk_file_when_not_in_overlay() {
    let s = snapshot_fs(
        text_fs(&[("/src/foo.ts", "disk content")], false),
        Overlays::default(),
        FxHashMap::default(),
        disk_files(&[("/src/foo.ts", "disk content")]),
        Dirs::default(),
    );
    assert_eq!(file_content(s.get_file("/src/foo.ts")), "disk content");
}

// Go: snapshotfs_test.go:558 TestSnapshotFS/GetFile reads from fs when not cached
#[test]
fn snapshot_fs_get_file_reads_from_fs_when_not_cached() {
    let s = snapshot_fs(
        text_fs(&[("/src/foo.ts", "fs content")], false),
        Overlays::default(),
        FxHashMap::default(),
        DiskFiles::default(),
        Dirs::default(),
    );
    assert_eq!(file_content(s.get_file("/src/foo.ts")), "fs content");
}

// Go: snapshotfs_test.go:578 TestSnapshotFS/GetFile returns nil for non-existent file
#[test]
fn snapshot_fs_get_file_returns_nil_for_non_existent_file() {
    let s = snapshot_fs(
        text_fs(&[], false),
        Overlays::default(),
        FxHashMap::default(),
        DiskFiles::default(),
        Dirs::default(),
    );
    assert!(
        s.get_file("/src/nonexistent.ts").is_none(),
        "should return nil for non-existent file"
    );
}

// Go: snapshotfs_test.go:595 TestSnapshotFS/isOpenFile returns true for overlays
#[test]
fn snapshot_fs_is_open_file_returns_true_for_overlays() {
    let s = snapshot_fs(
        text_fs(&[], false),
        overlays(&[("/src/foo.ts", "overlay content")]),
        FxHashMap::default(),
        DiskFiles::default(),
        Dirs::default(),
    );
    assert!(s.is_open_file("/src/foo.ts"), "overlay file should be open");
    assert!(
        !s.is_open_file("/src/bar.ts"),
        "non-overlay file should not be open"
    );
}

// Go: snapshotfs_test.go:618 TestSnapshotFS/GetFileByPath uses provided path
#[test]
fn snapshot_fs_get_file_by_path_uses_provided_path() {
    let s = snapshot_fs(
        text_fs(&[("/src/foo.ts", "disk content")], false),
        overlays(&[("/src/foo.ts", "overlay content")]),
        FxHashMap::default(),
        DiskFiles::default(),
        Dirs::default(),
    );
    // GetFileByPath should use the provided path directly
    assert_eq!(
        file_content(s.get_file_by_path("/src/foo.ts", &p("/src/foo.ts"))),
        "overlay content"
    );
}

// Go: snapshotfs_test.go:645 TestSnapshotFS/GetAccessibleEntries combines disk and overlay directories
#[test]
fn snapshot_fs_get_accessible_entries_combines_disk_and_overlay_directories() {
    let mut overlay_directories: FxHashMap<Path, FxHashMap<Path, String>> = FxHashMap::default();
    overlay_directories.insert(
        p("/"),
        [(p("/src"), "src".to_string())].into_iter().collect(),
    );
    overlay_directories.insert(
        p("/src"),
        [(p("/src/overlay.ts"), "overlay.ts".to_string())]
            .into_iter()
            .collect(),
    );
    let s = snapshot_fs(
        text_fs(&[], false),
        overlays(&[("/src/overlay.ts", "overlay content")]),
        overlay_directories,
        disk_files(&[("/src/disk.ts", "disk content")]),
        dirs(&[
            ("/", &[("/src", "src")]),
            ("/src", &[("/src/disk.ts", "disk.ts")]),
        ]),
    );

    let entries = s.get_accessible_entries("/src");

    // Should contain both disk file and overlay file (both as basenames)
    assert!(
        entries.files.iter().any(|f| f == "disk.ts"),
        "should contain disk.ts"
    );
    assert!(
        entries.files.iter().any(|f| f == "overlay.ts"),
        "should contain overlay.ts"
    );
}

// ---------------------------------------------------------------------------
// TestSourceFS
// ---------------------------------------------------------------------------

fn plain_snapshot(entries: &[(&str, &str)]) -> Rc<SnapshotFS> {
    snapshot_fs(
        text_fs(entries, false),
        Overlays::default(),
        FxHashMap::default(),
        DiskFiles::default(),
        Dirs::default(),
    )
}

// Go: snapshotfs_test.go:698 TestSourceFS/tracks files when tracking enabled
#[test]
fn source_fs_tracks_files_when_tracking_enabled() {
    let snapshot = plain_snapshot(&[("/src/foo.ts", "content")]);
    let source_fs = new_source_fs(true /* tracking */, snapshot, to_path());

    // File should not be seen yet
    assert!(!source_fs.seen_file(&p("/src/foo.ts")));

    // Read the file
    assert!(source_fs.get_file("/src/foo.ts").is_some());

    // Now it should be seen
    assert!(source_fs.seen_file(&p("/src/foo.ts")));
}

// Go: snapshotfs_test.go:726 TestSourceFS/does not track files when tracking disabled
#[test]
fn source_fs_does_not_track_files_when_tracking_disabled() {
    let snapshot = plain_snapshot(&[("/src/foo.ts", "content")]);
    let source_fs = new_source_fs(false /* tracking */, snapshot, to_path());

    // Read the file
    assert!(source_fs.get_file("/src/foo.ts").is_some());

    // Should not be seen since tracking is disabled
    assert!(!source_fs.seen_file(&p("/src/foo.ts")));
}

// Go: snapshotfs_test.go:751 TestSourceFS/DisableTracking stops tracking
#[test]
fn source_fs_disable_tracking_stops_tracking() {
    let snapshot = plain_snapshot(&[("/src/foo.ts", "content"), ("/src/bar.ts", "content")]);
    let source_fs = new_source_fs(true /* tracking */, snapshot, to_path());

    // Read foo while tracking
    source_fs.get_file("/src/foo.ts");
    assert!(source_fs.seen_file(&p("/src/foo.ts")));

    // Disable tracking
    source_fs.disable_tracking();

    // Read bar after tracking disabled
    source_fs.get_file("/src/bar.ts");
    assert!(!source_fs.seen_file(&p("/src/bar.ts")));
}

// Go: snapshotfs_test.go:781 TestSourceFS/FileExists returns true for files in source
#[test]
fn source_fs_file_exists_returns_true_for_files_in_source() {
    let snapshot = plain_snapshot(&[("/src/foo.ts", "content")]);
    let source_fs = new_source_fs(false /* tracking */, snapshot, to_path());

    assert!(Fs::file_exists(&*source_fs, "/src/foo.ts"));
    assert!(!Fs::file_exists(&*source_fs, "/src/nonexistent.ts"));
}

// Go: snapshotfs_test.go:802 TestSourceFS/ReadFile returns content for files in source
#[test]
fn source_fs_read_file_returns_content_for_files_in_source() {
    let snapshot = plain_snapshot(&[("/src/foo.ts", "file content")]);
    let source_fs = new_source_fs(false /* tracking */, snapshot, to_path());

    let (content, ok) = Fs::read_file(&*source_fs, "/src/foo.ts");
    assert!(ok);
    assert_eq!(content, "file content");

    let (_, ok) = Fs::read_file(&*source_fs, "/src/nonexistent.ts");
    assert!(!ok);
}

// ---------------------------------------------------------------------------
// TestAutoImportBuilderFS
// ---------------------------------------------------------------------------

// Go: snapshotfs_test.go:842 TestAutoImportBuilderFS/symlink cache mismatch: file cached at symlink path, missed at realpath after deletion
#[test]
fn auto_import_builder_fs_symlink_cache_mismatch() {
    // Create a VFS with a real file and a symlinked directory pointing to it.
    let test_fs = any_fs(
        vec![
            (
                "/real/pkg/index.d.ts",
                text("export declare const x: number;"),
            ),
            ("/project/node_modules/pkg", vfstest::symlink("/real/pkg")),
        ],
        true, /* useCaseSensitiveFileNames */
    );

    // Verify symlink works as expected
    let symlink_path = "/project/node_modules/pkg/index.d.ts";
    let realpath_path = test_fs.realpath(symlink_path);
    assert_eq!(
        realpath_path, "/real/pkg/index.d.ts",
        "Realpath should resolve the symlink to the real path"
    );

    let b = empty_builder(test_fs.clone());

    let auto_import_fs = AutoImportBuilderFS {
        snapshot_fs_builder: b,
        untracked_files: RefCell::default(),
    };

    // Step 1: Read the file via its symlink path.
    let fh = auto_import_fs.get_file(symlink_path);
    assert_eq!(file_content(fh), "export declare const x: number;");

    // Step 2: Simulate a file deletion from disk.
    test_fs.remove("/real/pkg/index.d.ts").unwrap();

    // Step 3: Request the file by its realpath.
    let fh2 = auto_import_fs.get_file(&realpath_path);
    assert!(
        fh2.is_none(),
        "File should be nil when accessed by realpath after deletion from disk"
    );
}

// ---------------------------------------------------------------------------
// TestRealpathAliasLifecycle
// ---------------------------------------------------------------------------

// Go: snapshotfs_test.go:901 TestRealpathAliasLifecycle/alias recorded when reading symlinked node_modules file
#[test]
fn alias_recorded_when_reading_symlinked_node_modules_file() {
    let b = empty_builder(any_fs(
        vec![
            (
                "/project/node_modules/mylib",
                vfstest::symlink("/packages/mylib"),
            ),
            (
                "/packages/mylib/package.json",
                text(r#"{"name": "mylib", "main": "index.js"}"#),
            ),
            (
                "/packages/mylib/index.d.ts",
                text("export declare const x: number;"),
            ),
            (
                "/project/node_modules/nolink/package.json",
                text(r#"{"name": "nolink"}"#),
            ),
        ],
        false,
    ));

    // Read a file through the symlink — should record an alias.
    assert_eq!(
        file_content(b.get_file("/project/node_modules/mylib/package.json")),
        r#"{"name": "mylib", "main": "index.js"}"#
    );

    // Read a non-symlinked node_modules file — should NOT record an alias.
    assert!(
        b.get_file("/project/node_modules/nolink/package.json")
            .is_some()
    );

    let (snapshot, _) = b.finalize();

    // Alias exists for the symlinked file.
    assert!(
        snapshot
            .node_modules_realpath_aliases
            .contains_key(&p("/packages/mylib/package.json")),
        "alias should exist for realpath of symlinked file"
    );
    assert!(alias_has(
        &snapshot.node_modules_realpath_aliases,
        "/packages/mylib/package.json",
        "/project/node_modules/mylib/package.json"
    ));

    // No alias for the non-symlinked file.
    assert!(
        !snapshot
            .node_modules_realpath_aliases
            .contains_key(&p("/project/node_modules/nolink/package.json")),
        "no alias should exist for non-symlinked file"
    );
}

// Go: snapshotfs_test.go:942 TestRealpathAliasLifecycle/no alias recorded for files outside node_modules
#[test]
fn no_alias_recorded_for_files_outside_node_modules() {
    let b = empty_builder(any_fs(
        vec![
            ("/project/link", vfstest::symlink("/elsewhere")),
            ("/elsewhere/index.ts", text("export const x = 1;")),
        ],
        false,
    ));

    assert!(b.get_file("/project/link/index.ts").is_some());

    let (snapshot, _) = b.finalize();
    assert_eq!(
        snapshot.node_modules_realpath_aliases.len(),
        0,
        "no aliases for non-node_modules symlinks"
    );
}

/// The file system of the "one symlink to mylib" subtests.
fn mylib_fs(extra: Vec<(&'static str, MapFile)>) -> Rc<dyn Fs> {
    let mut entries = vec![
        (
            "/project/node_modules/mylib",
            vfstest::symlink("/packages/mylib"),
        ),
        ("/packages/mylib/package.json", text(r#"{"name": "mylib"}"#)),
    ];
    entries.extend(extra);
    any_fs(entries, false)
}

/// Go `newSnapshotFSBuilder(fs, {}, {}, prev.diskFiles, prev.diskDirectories, prev.nodeModulesRealpathAliases, ...)`.
fn next_builder(fs: Rc<dyn Fs>, prev: &SnapshotFS) -> Rc<SnapshotFSBuilder> {
    builder(
        fs,
        Overlays::default(),
        prev.disk_files.clone(),
        prev.disk_directories.clone(),
        prev.node_modules_realpath_aliases.clone(),
    )
}

// Go: snapshotfs_test.go:967 TestRealpathAliasLifecycle/aliases carried over across snapshots
#[test]
fn aliases_carried_over_across_snapshots() {
    let test_fs = mylib_fs(Vec::new());

    // Build first snapshot.
    let builder1 = empty_builder(test_fs.clone());
    builder1.get_file("/project/node_modules/mylib/package.json");
    let (snapshot1, _) = builder1.finalize();

    // Build second snapshot from the first, without reading the file again.
    let builder2 = next_builder(test_fs, &snapshot1);
    let (snapshot2, _) = builder2.finalize();

    // Alias should still be present.
    assert!(
        snapshot2
            .node_modules_realpath_aliases
            .contains_key(&p("/packages/mylib/package.json")),
        "alias should survive across snapshots"
    );
    assert!(alias_has(
        &snapshot2.node_modules_realpath_aliases,
        "/packages/mylib/package.json",
        "/project/node_modules/mylib/package.json"
    ));
}

// Go: snapshotfs_test.go:1007 TestRealpathAliasLifecycle/alias pruned when symlinked file is deleted
#[test]
fn alias_pruned_when_symlinked_file_is_deleted() {
    let test_fs = mylib_fs(vec![(
        "/packages/mylib/index.d.ts",
        text("export declare const x: number;"),
    )]);

    // Build first snapshot — read both files.
    let builder1 = empty_builder(test_fs.clone());
    builder1.get_file("/project/node_modules/mylib/package.json");
    builder1.get_file("/project/node_modules/mylib/index.d.ts");
    let (snapshot1, _) = builder1.finalize();

    // Both should be aliased under the same realpath directory but separate files.
    assert!(
        snapshot1
            .node_modules_realpath_aliases
            .contains_key(&p("/packages/mylib/package.json"))
    );
    assert!(
        snapshot1
            .node_modules_realpath_aliases
            .contains_key(&p("/packages/mylib/index.d.ts"))
    );

    // Build second snapshot — delete one file via markDirtyFiles.
    let builder2 = next_builder(test_fs, &snapshot1);

    // Simulate deletion of index.d.ts from the disk file cache.
    delete_disk_file(&builder2, "/project/node_modules/mylib/index.d.ts");

    let (snapshot2, _) = builder2.finalize();

    // package.json alias should remain.
    assert!(
        snapshot2
            .node_modules_realpath_aliases
            .contains_key(&p("/packages/mylib/package.json")),
        "package.json alias should survive"
    );
    assert!(alias_has(
        &snapshot2.node_modules_realpath_aliases,
        "/packages/mylib/package.json",
        "/project/node_modules/mylib/package.json"
    ));

    // index.d.ts alias should be fully pruned (empty set → removed from map).
    assert!(
        !snapshot2
            .node_modules_realpath_aliases
            .contains_key(&p("/packages/mylib/index.d.ts")),
        "index.d.ts alias should be pruned after deletion"
    );
}

fn two_symlink_fs() -> Rc<dyn Fs> {
    mylib_fs(vec![(
        "/project/node_modules/alias",
        vfstest::symlink("/packages/mylib"),
    )])
}

// Go: snapshotfs_test.go:1066 TestRealpathAliasLifecycle/multiple symlinks to same realpath
#[test]
fn multiple_symlinks_to_same_realpath() {
    let b = empty_builder(two_symlink_fs());

    // Read via both symlinks.
    assert!(
        b.get_file("/project/node_modules/mylib/package.json")
            .is_some()
    );
    assert!(
        b.get_file("/project/node_modules/alias/package.json")
            .is_some()
    );

    let (snapshot, _) = b.finalize();

    let aliases = &snapshot.node_modules_realpath_aliases;
    assert!(
        aliases.contains_key(&p("/packages/mylib/package.json")),
        "alias should exist"
    );
    assert!(alias_has(
        aliases,
        "/packages/mylib/package.json",
        "/project/node_modules/mylib/package.json"
    ));
    assert!(alias_has(
        aliases,
        "/packages/mylib/package.json",
        "/project/node_modules/alias/package.json"
    ));
}

// Go: snapshotfs_test.go:1099 TestRealpathAliasLifecycle/multiple symlinks pruned individually
#[test]
fn multiple_symlinks_pruned_individually() {
    let test_fs = two_symlink_fs();

    // Build first snapshot – read via both symlinks.
    let builder1 = empty_builder(test_fs.clone());
    builder1.get_file("/project/node_modules/mylib/package.json");
    builder1.get_file("/project/node_modules/alias/package.json");
    let (snapshot1, _) = builder1.finalize();

    // Build second snapshot – delete ONE of the symlink disk entries.
    let builder2 = next_builder(test_fs, &snapshot1);
    delete_disk_file(&builder2, "/project/node_modules/alias/package.json");
    let (snapshot2, _) = builder2.finalize();

    // The realpath alias set should still exist, but only contain the surviving symlink.
    let aliases = &snapshot2.node_modules_realpath_aliases;
    assert!(
        aliases.contains_key(&p("/packages/mylib/package.json")),
        "alias set should still exist"
    );
    assert!(
        alias_has(
            aliases,
            "/packages/mylib/package.json",
            "/project/node_modules/mylib/package.json"
        ),
        "surviving symlink should remain"
    );
    assert!(
        !alias_has(
            aliases,
            "/packages/mylib/package.json",
            "/project/node_modules/alias/package.json"
        ),
        "deleted symlink should be pruned"
    );
}

// Go: snapshotfs_test.go:1145 TestRealpathAliasLifecycle/expandRealpathAliases expands change events
#[test]
fn expand_realpath_aliases_expands_change_events() {
    let b = empty_builder(mylib_fs(Vec::new()));
    b.get_file("/project/node_modules/mylib/package.json");
    let (snapshot, _) = b.finalize();

    // Simulate a watch event on the REALPATH.
    let mut change = FileChangeSummary::default();
    change
        .changed
        .insert(uri("file:///packages/mylib/package.json"));

    let expanded = snapshot.expand_realpath_aliases(change);

    // Should now also contain the symlink path.
    assert!(
        expanded
            .changed
            .contains(&uri("file:///packages/mylib/package.json")),
        "original event should remain"
    );
    assert!(
        expanded
            .changed
            .contains(&uri("file:///project/node_modules/mylib/package.json")),
        "symlink event should be added"
    );
}

// Go: snapshotfs_test.go:1176 TestRealpathAliasLifecycle/expandRealpathAliases expands delete events
#[test]
fn expand_realpath_aliases_expands_delete_events() {
    let b = empty_builder(mylib_fs(Vec::new()));
    b.get_file("/project/node_modules/mylib/package.json");
    let (snapshot, _) = b.finalize();

    // Simulate a delete watch event on the REALPATH.
    let mut change = FileChangeSummary::default();
    change
        .deleted
        .insert(uri("file:///packages/mylib/package.json"));

    let expanded = snapshot.expand_realpath_aliases(change);

    assert!(
        expanded
            .deleted
            .contains(&uri("file:///project/node_modules/mylib/package.json")),
        "symlink deletion should be added"
    );
}

// Go: snapshotfs_test.go:1205 TestRealpathAliasLifecycle/expandRealpathAliases is a no-op with no aliases
// PORT: Go leaves the other SnapshotFS fields nil; they are empty here.
#[test]
fn expand_realpath_aliases_is_a_no_op_with_no_aliases() {
    let snapshot = plain_snapshot(&[]);

    let mut change = FileChangeSummary::default();
    change.changed.insert(uri("file:///some/file.ts"));

    let expanded = snapshot.expand_realpath_aliases(change);
    assert_eq!(expanded.changed.len(), 1);
    assert!(expanded.changed.contains(&uri("file:///some/file.ts")));
}

// Go: snapshotfs_test.go:1220 TestRealpathAliasLifecycle/markDirtyFiles invalidates symlinked file via realpath event
#[test]
fn mark_dirty_files_invalidates_symlinked_file_via_realpath_event() {
    let test_fs = any_fs(
        vec![
            (
                "/project/node_modules/mylib",
                vfstest::symlink("/packages/mylib"),
            ),
            (
                "/packages/mylib/package.json",
                text(r#"{"name": "mylib", "main": "index.js"}"#),
            ),
        ],
        false,
    );

    // Build first snapshot — read the symlinked file.
    let builder1 = empty_builder(test_fs.clone());
    assert_eq!(
        file_content(builder1.get_file("/project/node_modules/mylib/package.json")),
        r#"{"name": "mylib", "main": "index.js"}"#
    );
    let (snapshot1, _) = builder1.finalize();

    // Modify the real file on disk.
    test_fs
        .write_file("/packages/mylib/package.json", r#"{"name": "mylib"}"#)
        .unwrap();

    // Build second snapshot — simulate realpath change event, expanded via aliases.
    let builder2 = next_builder(test_fs, &snapshot1);

    let mut change = FileChangeSummary::default();
    change
        .changed
        .insert(uri("file:///packages/mylib/package.json"));

    // Expand the realpath event to include the symlink path.
    let change = snapshot1.expand_realpath_aliases(change);
    // Now mark dirty — should find the file under the symlink key.
    builder2.mark_dirty_files(&change);

    // Trigger reload by reading the file (simulates program construction).
    assert_eq!(
        file_content(builder2.get_file("/project/node_modules/mylib/package.json")),
        r#"{"name": "mylib"}"#,
        "builder should serve updated content after dirty marking"
    );

    let (snapshot2, _) = builder2.finalize();

    // The file should have been reloaded with new content.
    let file = snapshot2
        .disk_files
        .get(&p("/project/node_modules/mylib/package.json"))
        .expect("file should still be in diskFiles");
    assert_eq!(
        file.content(),
        r#"{"name": "mylib"}"#,
        "content should be updated"
    );
}

// Go: snapshotfs_test.go:1280 TestRealpathAliasLifecycle/alias clone isolation between snapshots
#[test]
fn alias_clone_isolation_between_snapshots() {
    let test_fs = mylib_fs(vec![
        (
            "/project/node_modules/other",
            vfstest::symlink("/packages/other"),
        ),
        ("/packages/other/package.json", text(r#"{"name": "other"}"#)),
    ]);

    // Build first snapshot — read only mylib.
    let builder1 = empty_builder(test_fs.clone());
    builder1.get_file("/project/node_modules/mylib/package.json");
    let (snapshot1, _) = builder1.finalize();

    // Build second snapshot — also read other.
    let builder2 = next_builder(test_fs, &snapshot1);
    builder2.get_file("/project/node_modules/other/package.json");
    let (snapshot2, _) = builder2.finalize();

    // snapshot1 should only have mylib alias.
    assert!(
        snapshot1
            .node_modules_realpath_aliases
            .contains_key(&p("/packages/mylib/package.json")),
        "snapshot1 should have mylib alias"
    );
    assert!(
        !snapshot1
            .node_modules_realpath_aliases
            .contains_key(&p("/packages/other/package.json")),
        "snapshot1 should NOT have other alias — it was added in a later snapshot"
    );

    // snapshot2 should have both.
    assert!(
        snapshot2
            .node_modules_realpath_aliases
            .contains_key(&p("/packages/mylib/package.json")),
        "snapshot2 should have mylib alias"
    );
    assert!(
        snapshot2
            .node_modules_realpath_aliases
            .contains_key(&p("/packages/other/package.json")),
        "snapshot2 should have other alias"
    );
}

// Go: snapshotfs_test.go:1330 TestRealpathAliasLifecycle/adding symlink to inherited realpath key does not mutate previous snapshot
#[test]
fn adding_symlink_to_inherited_realpath_key_does_not_mutate_previous_snapshot() {
    let test_fs = two_symlink_fs();

    // Snapshot 1: read via one symlink only.
    let builder1 = empty_builder(test_fs.clone());
    builder1.get_file("/project/node_modules/mylib/package.json");
    let (snapshot1, _) = builder1.finalize();

    // Verify snapshot1 has exactly one alias for the realpath.
    let aliases1 = snapshot1
        .node_modules_realpath_aliases
        .get(&p("/packages/mylib/package.json"))
        .expect("alias set")
        .clone();
    assert_eq!(aliases1.borrow().paths.len(), 1);
    assert!(
        aliases1
            .borrow()
            .paths
            .contains(&p("/project/node_modules/mylib/package.json"))
    );

    // Snapshot 2: read via the SECOND symlink, which maps to the same realpath.
    let builder2 = next_builder(test_fs, &snapshot1);
    builder2.get_file("/project/node_modules/alias/package.json");
    let (snapshot2, _) = builder2.finalize();

    // Snapshot 2 should have both symlinks.
    let aliases2 = snapshot2
        .node_modules_realpath_aliases
        .get(&p("/packages/mylib/package.json"))
        .expect("alias set");
    assert_eq!(aliases2.borrow().paths.len(), 2);
    assert!(
        aliases2
            .borrow()
            .paths
            .contains(&p("/project/node_modules/mylib/package.json"))
    );
    assert!(
        aliases2
            .borrow()
            .paths
            .contains(&p("/project/node_modules/alias/package.json"))
    );

    // Snapshot 1 must NOT have been mutated — it should still have only one alias.
    assert_eq!(
        aliases1.borrow().paths.len(),
        1,
        "snapshot1 alias set must not be mutated by snapshot2"
    );
    assert!(
        !aliases1
            .borrow()
            .paths
            .contains(&p("/project/node_modules/alias/package.json")),
        "snapshot1 must not contain alias added in snapshot2"
    );
}

// ---------------------------------------------------------------------------
// TestExpandAndFilterWatchEvents
// ---------------------------------------------------------------------------

// Go: snapshotfs_test.go:1408 TestExpandAndFilterWatchEvents/preserves node_modules directory deletion even when untracked
#[test]
fn preserves_node_modules_directory_deletion_even_when_untracked() {
    let b = empty_builder(text_fs(
        &[("/project/index.ts", "export const x = 1;")],
        false,
    ));

    let mut change = FileChangeSummary::default();
    change.deleted.insert(uri("file:///project/node_modules"));

    let expanded = b.expand_and_filter_watch_events(change);
    assert!(
        expanded
            .deleted
            .contains(&uri("file:///project/node_modules")),
        "bare node_modules directory deletion should be preserved"
    );
}

// Go: snapshotfs_test.go:1425 TestExpandAndFilterWatchEvents/preserves deletion of a package directory inside node_modules
#[test]
fn preserves_deletion_of_a_package_directory_inside_node_modules() {
    let b = empty_builder(text_fs(
        &[("/project/index.ts", "export const x = 1;")],
        false,
    ));

    let mut change = FileChangeSummary::default();
    change
        .deleted
        .insert(uri("file:///project/node_modules/@scope/pkg"));

    let expanded = b.expand_and_filter_watch_events(change);
    assert!(
        expanded
            .deleted
            .contains(&uri("file:///project/node_modules/@scope/pkg")),
        "package directory deletion inside node_modules should be preserved"
    );
}

// Go: snapshotfs_test.go:1439 TestExpandAndFilterWatchEvents/drops irrelevant untracked deletion outside node_modules
#[test]
fn drops_irrelevant_untracked_deletion_outside_node_modules() {
    let b = empty_builder(text_fs(
        &[("/project/index.ts", "export const x = 1;")],
        false,
    ));

    let mut change = FileChangeSummary::default();
    change.deleted.insert(uri("file:///project/build"));

    let expanded = b.expand_and_filter_watch_events(change);
    assert_eq!(
        expanded.deleted.len(),
        0,
        "untracked non-node_modules directory deletion should be dropped"
    );
}

// Go: snapshotfs_test.go:1453 TestExpandAndFilterWatchEvents/expands tracked directory deletion into file deletions
#[test]
fn expands_tracked_directory_deletion_into_file_deletions() {
    let b = builder(
        text_fs(&[("/src/foo.ts", "const foo = 1;")], false),
        Overlays::default(),
        disk_files(&[("/src/foo.ts", "const foo = 1;")]),
        dirs(&[
            ("/", &[("/src", "src")]),
            ("/src", &[("/src/foo.ts", "foo.ts")]),
        ]),
        Aliases::default(),
    );

    let mut change = FileChangeSummary::default();
    change.deleted.insert(uri("file:///src"));

    let expanded = b.expand_and_filter_watch_events(change);
    assert!(
        expanded.deleted.contains(&uri("file:///src/foo.ts")),
        "tracked directory deletion should expand to contained file deletions"
    );
    assert!(
        !expanded.deleted.contains(&uri("file:///src")),
        "the directory URI itself should be replaced by its files"
    );
}
