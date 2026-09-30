//! Port of Go `internal/api/requestfilesystem/filechanges_test.go`
//! (ts#64115, ts#64291).

use std::rc::Rc;

use ts_goport::api::requestfilesystem::{Kind, RequestFileSystem, new_for_update};
use ts_goport::frontend::vfs::Fs;
use ts_goport::project;

use super::requestfilesystem_test::{
    directories, files, from_map, listing, new_request_file_system, nil_error, removed, symlinks,
};
use super::util::uri;

// Go: filechanges_test.go:11 TestFileChangesIncludeDirectoryTombstones
#[test]
fn file_changes_include_directory_tombstones() {
    let base = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[
                ("/removed/nested/file.ts", "removed"),
                ("/replaced.ts", "old"),
            ]),
            symlinks: symlinks(&[("/alias", "/removed", false)]),
            ..Default::default()
        },
        &from_map(&[], true),
        "/",
    ));

    let mut summary = project::FileChangeSummary::default();
    nil_error(new_for_update(
        Some(&RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/replaced.ts", "new")]),
            removed_paths: removed(&["removed", "/missing", "/replaced.ts"]),
            ..Default::default()
        }),
        base,
        "/",
        &mut summary,
    ));
    assert!(!summary.invalidate_all);
    assert!(summary.includes_watch_change_outside_node_modules);
    assert_eq!(summary.deleted.len(), 2);
    assert!(summary.deleted.contains(&uri("file:///removed")));
    assert!(summary.deleted.contains(&uri("file:///alias")));
    assert_eq!(summary.changed.len(), 1);
    assert!(summary.changed.contains(&uri("file:///replaced.ts")));
}

// Go: filechanges_test.go:42 TestFileChangesIncludeListingsAndSymlinks
#[test]
fn file_changes_include_listings_and_symlinks() {
    let base: Rc<dyn Fs> = from_map(
        &[
            ("/dir/old.ts", "old listing"),
            ("/link/old.ts", "old target"),
        ],
        true,
    );
    let mut summary = project::FileChangeSummary::default();
    nil_error(new_for_update(
        Some(&RequestFileSystem {
            kind: Kind::LAYER,
            directories: directories(vec![("/dir", listing(&[], &[]))]),
            symlinks: symlinks(&[("/link", "/target", false), ("/new", "/host", true)]),
            ..Default::default()
        }),
        base,
        "/",
        &mut summary,
    ));
    assert!(!summary.invalidate_all);
    assert_eq!(summary.deleted.len(), 2);
    assert!(summary.deleted.contains(&uri("file:///dir")));
    assert!(summary.deleted.contains(&uri("file:///link")));
    assert_eq!(summary.created.len(), 3);
    assert!(summary.created.contains(&uri("file:///dir")));
    assert!(summary.created.contains(&uri("file:///link")));
    assert!(summary.created.contains(&uri("file:///new")));
}

// Go: filechanges_test.go:71 TestFileChangesIncludeRecursiveSymlinkAliases
#[test]
fn file_changes_include_recursive_symlink_aliases() {
    let base = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/dir/file.ts", "old")]),
            symlinks: symlinks(&[("/dir/link", "/dir", false)]),
            ..Default::default()
        },
        &from_map(&[], true),
        "/",
    ));

    let mut summary = project::FileChangeSummary::default();
    nil_error(new_for_update(
        Some(&RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/dir/file.ts", "new")]),
            ..Default::default()
        }),
        base,
        "/",
        &mut summary,
    ));
    assert_eq!(summary.changed.len(), 2);
    assert!(summary.changed.contains(&uri("file:///dir/file.ts")));
    assert!(summary.changed.contains(&uri("file:///dir/link/file.ts")));
    assert_eq!(summary.created.len(), 0);
}

// Go: filechanges_test.go:95 TestFileChangesIncludeRootSymlinkAliases
#[test]
fn file_changes_include_root_symlink_aliases() {
    let base = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/file.ts", "old")]),
            symlinks: symlinks(&[("/link", "/", false)]),
            ..Default::default()
        },
        &from_map(&[], true),
        "/",
    ));
    let (content, ok) = base.read_file("/link/file.ts");
    assert!(ok);
    assert_eq!(content, "old");

    let mut summary = project::FileChangeSummary::default();
    nil_error(new_for_update(
        Some(&RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/file.ts", "new")]),
            ..Default::default()
        }),
        base,
        "/",
        &mut summary,
    ));
    assert_eq!(summary.changed.len(), 2);
    assert!(summary.changed.contains(&uri("file:///file.ts")));
    assert!(summary.changed.contains(&uri("file:///link/file.ts")));
    assert_eq!(summary.created.len(), 0);
}
