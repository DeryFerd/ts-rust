//! Go: `internal/vfs/walkdir_test.go` (ts#64277, microsoft/TypeScript
//! 673a5f17d713). The Go file is the external test package `vfs_test`.
//!
//! PORT: Go `assert.NilError(t, err)` inside the walk function is a panic.
//! Go `wrapvfs.Wrap(base, wrapvfs.Replacements{...})` is `wrapvfs_wrap`; each
//! replacement closure holds its own `Rc` of the base file system.

use std::cell::RefCell;
use std::rc::Rc;

use ts_goport::frontend::vfs::{
    DirEntry, Entries, FileMode, Fs, FsError, Replacements, walk_dir, wrapvfs_wrap,
};

use crate::support::vfstest;

/// Go `assert.NilError(t, err)` on the error a walk function gets.
fn nil_error(err: Option<FsError>) {
    if let Some(err) = err {
        panic!("unexpected error: {err:?}");
    }
}

/// The entry of a walk call with no error.
fn entry(entry: Option<&DirEntry>) -> &DirEntry {
    entry.expect("WalkDir passes an entry when there is no error")
}

// Go: walkdir_test.go:14 TestWalkDir
#[test]
fn test_walk_dir() {
    let base = vfstest::from_map(
        [
            ("/root/a.ts", ""),
            ("/root/dir/b.ts", ""),
            ("/root/link/hidden.ts", ""),
            ("/target/hidden.ts", ""),
        ],
        true,
    );
    let entries_base = Rc::clone(&base);
    let file_system = wrapvfs_wrap(
        base,
        Replacements {
            get_accessible_entries: Some(Box::new(move |path: &str| -> Entries {
                let mut entries = entries_base.get_accessible_entries(path);
                entries.symlinks = None;
                if path == "/root" {
                    entries.files.push("C:/foreign.ts".to_string());
                }
                entries
            })),
            realpath: Some(Box::new(|path: &str| -> String {
                match path {
                    "/root/link" => "/target".to_string(),
                    "/root/link/hidden.ts" => "/target/hidden.ts".to_string(),
                    _ => path.to_string(),
                }
            })),
            ..Default::default()
        },
    );

    let mut paths: Vec<String> = Vec::new();
    let mut modes: Vec<FileMode> = Vec::new();
    let result = walk_dir(&*file_system, "/root", &mut |path, e, err| {
        nil_error(err);
        let e = entry(e);
        paths.push(path.to_string());
        modes.push(e.type_());
        if e.type_().intersects(FileMode::SYMLINK) {
            let info = e
                .info()
                .unwrap_or_else(|err| panic!("unexpected error: {err:?}"));
            assert_eq!(info.mode(), FileMode::SYMLINK);
            assert!(!info.is_dir());
        }
        Ok(())
    });
    assert!(result.is_ok(), "unexpected error: {result:?}");
    assert_eq!(
        paths,
        [
            "/root",
            "/root/a.ts",
            "/root/dir",
            "/root/dir/b.ts",
            "/root/link"
        ]
    );
    assert_eq!(
        modes,
        [
            FileMode::DIR,
            FileMode(0),
            FileMode::DIR,
            FileMode(0),
            FileMode::SYMLINK
        ]
    );
}

// Go: walkdir_test.go:63 TestWalkDirDoesNotFollowRootSymlink
#[test]
fn test_walk_dir_does_not_follow_root_symlink() {
    let base = vfstest::from_map(
        [("/root/link/hidden.ts", ""), ("/target/hidden.ts", "")],
        true,
    );
    let entries_base = Rc::clone(&base);
    let file_system = wrapvfs_wrap(
        base,
        Replacements {
            get_accessible_entries: Some(Box::new(move |path: &str| -> Entries {
                let mut entries = entries_base.get_accessible_entries(path);
                entries.symlinks = None;
                entries
            })),
            realpath: Some(Box::new(|path: &str| -> String {
                if path == "/root/link" {
                    return "/target".to_string();
                }
                path.to_string()
            })),
            ..Default::default()
        },
    );

    let mut paths: Vec<String> = Vec::new();
    let result = walk_dir(&*file_system, "/root/link", &mut |path, e, err| {
        nil_error(err);
        paths.push(path.to_string());
        assert_eq!(entry(e).type_(), FileMode::SYMLINK);
        Ok(())
    });
    assert!(result.is_ok(), "unexpected error: {result:?}");
    assert_eq!(paths, ["/root/link"]);
}

// Go: walkdir_test.go:95 TestWalkDirReportsRootFileSymlink
#[test]
fn test_walk_dir_reports_root_file_symlink() {
    let base = vfstest::from_map([("/target/file.ts", "")], true);
    let stat_base = Rc::clone(&base);
    let file_system = wrapvfs_wrap(
        base,
        Replacements {
            stat: Some(Box::new(move |path: &str| {
                if path == "/root/link.ts" {
                    return stat_base.stat("/target/file.ts");
                }
                stat_base.stat(path)
            })),
            realpath: Some(Box::new(|path: &str| -> String {
                if path == "/root/link.ts" {
                    return "/target/file.ts".to_string();
                }
                path.to_string()
            })),
            ..Default::default()
        },
    );

    let result = walk_dir(&*file_system, "/root/link.ts", &mut |path, e, err| {
        nil_error(err);
        let e = entry(e);
        assert_eq!(path, "/root/link.ts");
        assert_eq!(e.name(), "link.ts");
        assert_eq!(e.type_(), FileMode::SYMLINK);
        Ok(())
    });
    assert!(result.is_ok(), "unexpected error: {result:?}");
}

// Go: walkdir_test.go:126 TestWalkDirSkipDir
#[test]
fn test_walk_dir_skip_dir() {
    let file_system = vfstest::from_map([("/root/a/hidden.ts", ""), ("/root/b.ts", "")], true);
    let mut paths: Vec<String> = Vec::new();
    let result = walk_dir(&*file_system, "/root", &mut |path, _, err| {
        nil_error(err);
        paths.push(path.to_string());
        if path == "/root/a" {
            return Err(FsError::SkipDir);
        }
        Ok(())
    });
    assert!(result.is_ok(), "unexpected error: {result:?}");
    assert_eq!(paths, ["/root", "/root/a", "/root/b.ts"]);
}

// Go: walkdir_test.go:146 TestWalkDirSkipAll
#[test]
fn test_walk_dir_skip_all() {
    let file_system = vfstest::from_map([("/root/a.ts", ""), ("/root/b.ts", "")], true);
    let mut paths: Vec<String> = Vec::new();
    let result = walk_dir(&*file_system, "/root", &mut |path, _, err| {
        nil_error(err);
        paths.push(path.to_string());
        if path == "/root/a.ts" {
            return Err(FsError::SkipAll);
        }
        Ok(())
    });
    assert!(result.is_ok(), "unexpected error: {result:?}");
    assert_eq!(paths, ["/root", "/root/a.ts"]);
}

// Go: walkdir_test.go:166 TestWalkDirConsumesSkipDirForRootFile
#[test]
fn test_walk_dir_consumes_skip_dir_for_root_file() {
    let file_system = vfstest::from_map([("/root.ts", "")], true);
    let result = walk_dir(&*file_system, "/root.ts", &mut |_, _, err| {
        nil_error(err);
        Err(FsError::SkipDir)
    });
    assert!(result.is_ok(), "unexpected error: {result:?}");
}

// Go: walkdir_test.go:177 TestWalkDirConsumesSkipForMissingRoot
#[test]
fn test_walk_dir_consumes_skip_for_missing_root() {
    let file_system = vfstest::from_map(Vec::<(&str, &str)>::new(), true);
    for sentinel in [FsError::SkipDir, FsError::SkipAll] {
        let result = walk_dir(&*file_system, "/missing", &mut |_, _, err| {
            // Go `assert.ErrorIs(t, err, fs.ErrNotExist)`.
            assert!(
                matches!(err, Some(FsError::NotExist)),
                "expected ErrNotExist, got {err:?}"
            );
            Err(sentinel.clone())
        });
        assert!(result.is_ok(), "unexpected error: {result:?}");
    }
}

// Go: walkdir_test.go:190 TestWalkDirUsesSymlinkMetadataWithoutRealpathCalls
#[test]
fn test_walk_dir_uses_symlink_metadata_without_realpath_calls() {
    let base = vfstest::from_map([("/root/dir/file.ts", "")], true);
    let realpath_calls: Rc<RefCell<Vec<String>>> = Rc::default();
    let calls = Rc::clone(&realpath_calls);
    let file_system: Rc<dyn Fs> = wrapvfs_wrap(
        base,
        Replacements {
            realpath: Some(Box::new(move |path: &str| -> String {
                calls.borrow_mut().push(path.to_string());
                path.to_string()
            })),
            ..Default::default()
        },
    );

    let result = walk_dir(&*file_system, "/root", &mut |_, _, err| match err {
        Some(err) => Err(err),
        None => Ok(()),
    });
    assert!(result.is_ok(), "unexpected error: {result:?}");
    assert!(
        !realpath_calls
            .borrow()
            .iter()
            .any(|path| path == "/root/dir")
    );
}
