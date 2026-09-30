//! Port of Go `internal/api/requestfilesystem/pathtree_test.go` (ts#64115,
//! ts#64277, ts#64291).
//!
//! PORT: Go `&requestPathNode{}` is a new `RequestPathNodeRef`, and the node
//! methods are the free functions of `pathtree` (`node.lookup(path)` is
//! `lookup(Some(&node), &path)`).
//!
//! PORT: Go `*requestFile` and `*requestDirectory` are the `vfs.FileInfo` and
//! the `vfs.DirEntry` themselves, and the Go tests compare those pointers
//! (`any(info) == node.entry`). A port `vfs::FileInfo` is a value that the
//! entry makes (`file_info`), so the tests compare the values. The port has
//! no `Sys` and no `DirEntry` of an entry: `entry.Type()` is
//! `info.mode.type_()` and `entry.Info()` is the entry's `file_info`.

use std::rc::Rc;
use std::time::{Duration, UNIX_EPOCH};

use ts_goport::api::requestfilesystem::pathtree::{
    RequestDirectory, RequestEntry, RequestFallback, RequestFile, RequestPathNode,
    RequestPathNodeRef, RequestSymlinkEntry, compose_request_paths, contains_file_ancestor, ensure,
    lookup,
};
use ts_goport::api::requestfilesystem::{Kind, RequestFileSystem};
use ts_goport::frontend::vfs::wrapvfs::{Replacements, wrapvfs_wrap};
use ts_goport::frontend::vfs::{self, FileMode, Fs};

use super::requestfilesystem_test::{
    assert_entries, directories, files, from_map, imp, listing, new_layered_request_file_system,
    new_request_file_system, nil_error, request, symlinks, tracking,
    verify_compaction_without_host_reads,
};
use super::util::path;

/// Go `&requestPathNode{}`.
fn new_node() -> RequestPathNodeRef {
    Rc::new(std::cell::RefCell::new(RequestPathNode::default()))
}

/// Go `node.entry.(*requestFile)`.
fn as_file(node: &RequestPathNodeRef) -> Option<Rc<RequestFile>> {
    match &node.borrow().entry {
        Some(RequestEntry::File(file)) => Some(file.clone()),
        _ => None,
    }
}

/// Go `node.entry.(*requestDirectory)`.
fn as_directory(node: &RequestPathNodeRef) -> Option<Rc<RequestDirectory>> {
    match &node.borrow().entry {
        Some(RequestEntry::Directory(directory)) => Some(directory.clone()),
        _ => None,
    }
}

/// Go `node.entry.(*requestSymlink)`.
fn is_symlink_entry(node: &RequestPathNodeRef) -> bool {
    matches!(node.borrow().entry, Some(RequestEntry::Symlink(_)))
}

// Go: pathtree_test.go:14 TestRequestPathTreeChildOverridesInheritedMissing
#[test]
fn request_path_tree_child_overrides_inherited_missing() {
    let base = new_node();
    ensure(&base, &path("/dir")).borrow_mut().fallback = RequestFallback::Missing;
    let layer = new_node();
    ensure(&layer, &path("/dir/pkg")).borrow_mut().entry =
        Some(RequestEntry::Symlink(Rc::new(RequestSymlinkEntry {
            link_name: "/dir/pkg".to_string(),
            target: "/target".to_string(),
            host: false,
        })));
    let compacted = compose_request_paths(
        Some(base.clone()),
        Some(&layer),
        RequestFallback::Allowed,
        true,
    )
    .unwrap();
    let (_, fallback) = lookup(Some(&compacted), &path("/dir/pkg/file.ts"));
    assert_eq!(fallback, RequestFallback::Allowed);
    let (_, fallback) = lookup(Some(&compacted), &path("/dir/other.ts"));
    assert_eq!(fallback, RequestFallback::Missing);
    let (_, fallback) = lookup(Some(&base), &path("/dir/pkg/file.ts"));
    assert_eq!(fallback, RequestFallback::Missing);
}

// Go: pathtree_test.go:29 TestRequestPathTreeSameLayerMissingBlocksSymlink
#[test]
fn request_path_tree_same_layer_missing_blocks_symlink() {
    let layer = new_node();
    ensure(&layer, &path("/dir")).borrow_mut().fallback = RequestFallback::Missing;
    ensure(&layer, &path("/dir/pkg")).borrow_mut().entry =
        Some(RequestEntry::Symlink(Rc::new(RequestSymlinkEntry {
            link_name: "/dir/pkg".to_string(),
            target: "/target".to_string(),
            host: false,
        })));
    let compacted = compose_request_paths(
        Some(new_node()),
        Some(&layer),
        RequestFallback::Allowed,
        true,
    )
    .unwrap();
    let (_, fallback) = lookup(Some(&compacted), &path("/dir/pkg/file.ts"));
    assert_eq!(fallback, RequestFallback::Missing);
}

// Go: pathtree_test.go:39 TestRequestPathTreeDirectoryPreservesInheritedMissing
#[test]
fn request_path_tree_directory_preserves_inherited_missing() {
    let base = new_node();
    ensure(&base, &path("/dir")).borrow_mut().fallback = RequestFallback::Missing;
    let layer = new_node();
    ensure(&layer, &path("/dir/new")).borrow_mut().entry =
        Some(RequestEntry::Directory(Rc::new(RequestDirectory {
            directory_name: "/dir/new".to_string(),
            listing: None,
        })));
    let compacted =
        compose_request_paths(Some(base), Some(&layer), RequestFallback::Allowed, true).unwrap();
    let (node, fallback) = lookup(Some(&compacted), &path("/dir/new"));
    let directory = as_directory(&node.unwrap());
    assert!(directory.is_some());
    assert_eq!(directory.unwrap().directory_name, "/dir/new");
    assert_eq!(fallback, RequestFallback::Missing);
    let (_, fallback) = lookup(Some(&compacted), &path("/dir/new/old.ts"));
    assert_eq!(fallback, RequestFallback::Missing);
}

// Go: pathtree_test.go:55 TestRequestPathTreeFileReplacesSubtree
#[test]
fn request_path_tree_file_replaces_subtree() {
    let base = new_node();
    ensure(&base, &path("/dir")).borrow_mut().entry =
        Some(RequestEntry::Directory(Rc::new(RequestDirectory {
            directory_name: "/dir".to_string(),
            listing: Some(vfs::Entries {
                files: vec!["old.ts".to_string()],
                ..Default::default()
            }),
        })));
    ensure(&base, &path("/dir/old.ts")).borrow_mut().entry =
        Some(RequestEntry::File(Rc::new(RequestFile {
            file_name: "/dir/old.ts".to_string(),
            content: "old".to_string(),
        })));
    let layer = new_node();
    ensure(&layer, &path("/dir")).borrow_mut().entry =
        Some(RequestEntry::File(Rc::new(RequestFile {
            file_name: "/dir".to_string(),
            content: "new".to_string(),
        })));
    let compacted = compose_request_paths(
        Some(base.clone()),
        Some(&layer),
        RequestFallback::Allowed,
        true,
    )
    .unwrap();
    let (node, _) = lookup(Some(&compacted), &path("/dir"));
    let node = node.unwrap();
    let file = as_file(&node);
    assert!(file.is_some());
    assert_eq!(file.unwrap().content, "new");
    assert_eq!(node.borrow().children.as_ref().map_or(0, |c| c.len()), 0);
    assert!(contains_file_ancestor(
        Some(&compacted),
        &path("/dir/old.ts")
    ));
    let (previous, _) = lookup(Some(&base), &path("/dir/old.ts"));
    let previous_file = as_file(&previous.unwrap());
    assert!(previous_file.is_some());
    assert_eq!(previous_file.unwrap().content, "old");
}

// Go: pathtree_test.go:75 TestRequestPathTreeListingReplacementDoesNotRemoveFiles
#[test]
fn request_path_tree_listing_replacement_does_not_remove_files() {
    let host = tracking(from_map(&[], true));
    let host_fs: Rc<dyn Fs> = host.clone();
    let base = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            files: files(&[("/dir/retained.ts", "retained")]),
            directories: directories(vec![("/dir", listing(&["retained.ts"], &[]))]),
            ..Default::default()
        },
        &host_fs,
        "/",
    ));
    let compacted = nil_error(new_layered_request_file_system(
        &RequestFileSystem {
            kind: Kind::LAYER,
            directories: directories(vec![("/dir", listing(&[], &[]))]),
            ..Default::default()
        },
        &base,
        "/",
    ));
    let (content, ok) = compacted.read_file("/dir/retained.ts");
    assert!(ok);
    assert_eq!(content, "retained");
    assert_eq!(
        compacted.get_accessible_entries("/dir").files,
        Vec::<String>::new()
    );
    assert_eq!(
        base.get_accessible_entries("/dir").files,
        vec!["retained.ts"]
    );
    verify_compaction_without_host_reads(&compacted, &host, &["/dir", "/dir/retained.ts"]);
}

// Go: pathtree_test.go:101 TestRequestPathTreeCompositionPreservesListingSnapshots
#[test]
fn request_path_tree_composition_preserves_listing_snapshots() {
    let base = new_node();
    ensure(&base, &path("/dir")).borrow_mut().entry =
        Some(RequestEntry::Directory(Rc::new(RequestDirectory {
            directory_name: "/dir".to_string(),
            listing: Some(vfs::Entries {
                files: vec!["OLD.ts".to_string()],
                ..Default::default()
            }),
        })));
    ensure(&base, &path("/dir/old.ts")).borrow_mut().entry =
        Some(RequestEntry::File(Rc::new(RequestFile {
            file_name: "/dir/OLD.ts".to_string(),
            content: String::new(),
        })));
    let layer = new_node();
    ensure(&layer, &path("/dir/old.ts")).borrow_mut().fallback = RequestFallback::Missing;
    ensure(&layer, &path("/dir/new.ts")).borrow_mut().entry =
        Some(RequestEntry::File(Rc::new(RequestFile {
            file_name: "/dir/new.ts".to_string(),
            content: String::new(),
        })));
    let compacted = compose_request_paths(
        Some(base.clone()),
        Some(&layer),
        RequestFallback::Allowed,
        false,
    )
    .unwrap();
    let (node, _) = lookup(Some(&compacted), &path("/dir"));
    let node = node.unwrap();
    let directory = as_directory(&node);
    assert!(directory.is_some());
    assert_eq!(
        directory.unwrap().listing.as_ref().unwrap().files,
        vec!["new.ts"]
    );
    let (previous, _) = lookup(Some(&base), &path("/dir"));
    let previous_directory = as_directory(&previous.unwrap());
    assert!(previous_directory.is_some());
    assert_eq!(
        previous_directory.unwrap().listing.as_ref().unwrap().files,
        vec!["OLD.ts"]
    );
    let next = compose_request_paths(
        Some(compacted),
        Some(&new_node()),
        RequestFallback::Allowed,
        false,
    )
    .unwrap();
    let (next_node, _) = lookup(Some(&next), &path("/dir"));
    assert!(Rc::ptr_eq(&next_node.unwrap(), &node));
}

// Go: pathtree_test.go:123 TestRequestPathTreeFileTakesPrecedenceOverSameLayerSymlink
#[test]
fn request_path_tree_file_takes_precedence_over_same_layer_symlink() {
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/item", "file"), ("/target/file.ts", "target")]),
            symlinks: symlinks(&[("/item", "/target", false)]),
            ..Default::default()
        },
        &from_map(&[], true),
        "/",
    ));
    let (content, ok) = file_system.read_file("/item");
    assert!(ok);
    assert_eq!(content, "file");
    assert!(!file_system.directory_exists("/item"));
    assert_eq!(file_system.realpath("/item"), "/item");
    let (node, _) = lookup(Some(&imp(&file_system).paths), &path("/item"));
    assert!(as_file(&node.unwrap()).is_some());
    assert!(!imp(&file_system).paths.borrow().has_symlinks);
    assert_eq!(file_system.get_accessible_entries("/").files, vec!["item"]);
}

// Go: pathtree_test.go:146 TestRequestPathTreeDirectoryTakesPrecedenceOverSameLayerSymlink
#[test]
fn request_path_tree_directory_takes_precedence_over_same_layer_symlink() {
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/item/child.ts", "child"), ("/target.ts", "target")]),
            directories: directories(vec![("/item", listing(&["child.ts"], &[]))]),
            symlinks: symlinks(&[("/item", "/target.ts", false)]),
            ..Default::default()
        },
        &from_map(&[], true),
        "/",
    ));
    assert!(file_system.directory_exists("/item"));
    assert!(!file_system.file_exists("/item"));
    assert_eq!(file_system.realpath("/item"), "/item");
    let (content, ok) = file_system.read_file("/item/child.ts");
    assert!(ok);
    assert_eq!(content, "child");
    let (node, _) = lookup(Some(&imp(&file_system).paths), &path("/item"));
    assert!(as_directory(&node.unwrap()).is_some());
    assert!(!imp(&file_system).paths.borrow().has_symlinks);
    assert_eq!(
        file_system.get_accessible_entries("/item").files,
        vec!["child.ts"]
    );
}

// Go: pathtree_test.go:171 TestRequestPathTreeSymlinkTakesPrecedenceOverListingHint
#[test]
fn request_path_tree_symlink_takes_precedence_over_listing_hint() {
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/target/file.ts", "target")]),
            directories: directories(vec![("/links", listing(&[], &["pkg"]))]),
            symlinks: symlinks(&[("/links/pkg", "/target", false)]),
            ..Default::default()
        },
        &from_map(&[], true),
        "/",
    ));
    let (node, _) = lookup(Some(&imp(&file_system).paths), &path("/links/pkg"));
    assert!(is_symlink_entry(&node.unwrap()));
    assert!(imp(&file_system).paths.borrow().has_symlinks);
    let (content, ok) = file_system.read_file("/links/pkg/file.ts");
    assert!(ok);
    assert_eq!(content, "target");
    assert_eq!(file_system.realpath("/links/pkg"), "/target");
    assert_entries(
        &file_system.get_accessible_entries("/links"),
        &[],
        &["pkg"],
        Some(&["pkg"]),
    );
}

// Go: pathtree_test.go:194 TestRequestPathTreeFileTakesPrecedenceOverSameLayerDirectory
#[test]
fn request_path_tree_file_takes_precedence_over_same_layer_directory() {
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/item", "file")]),
            directories: directories(vec![("/item", listing(&["listed.ts"], &[]))]),
            ..Default::default()
        },
        &from_map(&[], true),
        "/",
    ));
    let (node, _) = lookup(Some(&imp(&file_system).paths), &path("/item"));
    assert!(as_file(&node.unwrap()).is_some());
    let (content, ok) = file_system.read_file("/item");
    assert!(ok);
    assert_eq!(content, "file");
    assert!(!file_system.directory_exists("/item"));
    assert_eq!(file_system.get_accessible_entries("/item").files.len(), 0);
}

// Go: pathtree_test.go:212 TestRequestPathTreeFileProvidesStatAndDirEntry
#[test]
fn request_path_tree_file_provides_stat_and_dir_entry() {
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/dir/file.ts", "file content")]),
            ..Default::default()
        },
        &from_map(&[], true),
        "/",
    ));
    let (node, _) = lookup(Some(&imp(&file_system).paths), &path("/dir/file.ts"));
    let info = file_system.stat("/dir/file.ts");
    assert!(info.is_some());
    let info = info.unwrap();
    assert_eq!(info.name(), "file.ts");
    assert_eq!(info.size(), "file content".len() as i64);
    assert_eq!(info.mode(), FileMode(0o444));
    assert!(!info.is_dir());
    assert_eq!(info.mod_time(), None);
    // PORT: `any(info) == node.entry` (see the file header).
    let entry = as_file(&node.unwrap()).unwrap();
    assert_eq!(entry.file_info(), info);
    // Go: entry.Type(), entry.Info()
    assert_eq!(entry.file_info().mode().type_(), FileMode(0));
    assert_eq!(entry.file_info(), info);
}

// Go: pathtree_test.go:236 TestRequestPathTreeDirectoryProvidesStatAndDirEntry
#[test]
fn request_path_tree_directory_provides_stat_and_dir_entry() {
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            directories: directories(vec![("/dir", listing(&[], &[]))]),
            ..Default::default()
        },
        &from_map(&[], true),
        "/",
    ));
    let (node, _) = lookup(Some(&imp(&file_system).paths), &path("/dir"));
    let info = file_system.stat("/dir");
    assert!(info.is_some());
    let info = info.unwrap();
    assert_eq!(info.name(), "dir");
    assert_eq!(info.size(), 0);
    assert_eq!(info.mode(), FileMode::DIR | FileMode(0o555));
    assert!(info.is_dir());
    assert_eq!(info.mod_time(), None);
    // PORT: `any(info) == node.entry` (see the file header).
    let entry = as_directory(&node.unwrap()).unwrap();
    assert_eq!(entry.file_info(), info);
    // Go: entry.Type(), entry.Info()
    assert_eq!(entry.file_info().mode().type_(), FileMode::DIR);
    assert_eq!(entry.file_info(), info);
}

// Go: pathtree_test.go:260 TestRequestPathTreeSymlinkReportsTargetMetadata
#[test]
fn request_path_tree_symlink_reports_target_metadata() {
    let file_system = nil_error(new_request_file_system(
        &RequestFileSystem {
            kind: Kind::FULL,
            files: files(&[("/target/file.ts", "target content")]),
            symlinks: symlinks(&[("/link.ts", "/target/file.ts", false)]),
            ..Default::default()
        },
        &from_map(&[], true),
        "/",
    ));
    let info = file_system.stat("/target/file.ts");
    assert_eq!(file_system.stat("/link.ts"), info);
}

// Go: pathtree_test.go:272 requestTestHostMetadata
// PORT: a `wrapvfs` wrapper whose `Stat` returns `info`.
fn request_test_host_metadata(fs: Rc<dyn Fs>, info: Option<vfs::FileInfo>) -> Rc<dyn Fs> {
    wrapvfs_wrap(
        fs,
        Replacements {
            stat: Some(Box::new(move |_| info.clone())),
            ..Default::default()
        },
    )
}

// Go: pathtree_test.go:279 TestRequestPathTreeStatPreservesHostMetadata
#[test]
fn request_path_tree_stat_preserves_host_metadata() {
    let host_fs = from_map(&[("/host.ts", "host content")], true);
    // Go: time.Date(2026, time.September, 9, 12, 0, 0, 0, time.UTC)
    let modified = UNIX_EPOCH + Duration::from_secs(1_788_955_200);
    host_fs
        .chtimes("/host.ts", Some(modified), Some(modified))
        .unwrap();
    let info = host_fs.stat("/host.ts");
    let host = request_test_host_metadata(host_fs, info.clone());
    let file_system = nil_error(new_request_file_system(&request(Kind::LAYER), &host, "/"));
    assert_eq!(file_system.stat("/host.ts"), info);
    let entry_info = file_system.stat("/host.ts").unwrap();
    assert_eq!(entry_info.mod_time(), Some(modified));
    assert_eq!(entry_info.size(), "host content".len() as i64);
}

// Go: pathtree_test.go:296 TestRequestPathTreeStatSupportsExistenceOnlyHost
#[test]
fn request_path_tree_stat_supports_existence_only_host() {
    let host =
        request_test_host_metadata(from_map(&[("/dir/file.ts", "host content")], true), None);
    let file_system = nil_error(new_request_file_system(&request(Kind::LAYER), &host, "/"));
    let file_info = file_system.stat("/dir/file.ts");
    assert!(file_info.is_some());
    let file_info = file_info.unwrap();
    assert_eq!(file_info.name(), "file.ts");
    assert_eq!(file_info.size(), 0);
    assert_eq!(file_info.mode(), FileMode(0o444));
    assert!(!file_info.is_dir());
    let directory_info = file_system.stat("/dir");
    assert!(directory_info.is_some());
    let directory_info = directory_info.unwrap();
    assert_eq!(directory_info.name(), "dir");
    assert_eq!(directory_info.mode(), FileMode::DIR | FileMode(0o555));
    assert!(directory_info.is_dir());
    assert!(file_system.stat("/missing").is_none());
}
