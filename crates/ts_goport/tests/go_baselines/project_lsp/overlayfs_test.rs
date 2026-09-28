//! Port of Go `internal/project/overlayfs_test.go` (`TestProcessChanges`).
//! No program is built, so the tests run in the test process.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::rc::Rc;

use indexmap::IndexMap;
use ts_goport::flags::ScriptKind;
use ts_goport::frontend::tspath;
use ts_goport::lsp::lsproto;
use ts_goport::project::{FileChange, FileChangeKind, FileHandle, OverlayFS, new_overlay_fs};

use super::util::uri;
use crate::support::vfstest;

// Go: overlayfs_test.go:16 createOverlayFS
fn create_overlay_fs() -> Rc<OverlayFS> {
    let test_fs = vfstest::from_map(
        [
            ("/test1.ts", "// existing content"),
            ("/test2.ts", "// existing content"),
            ("/script", "// extensionless content"),
        ],
        false, /* useCaseSensitiveFileNames */
    );
    new_overlay_fs(
        test_fs,
        IndexMap::default(),
        lsproto::PositionEncodingKind::UTF16,
        Rc::new(|file_name: &str| tspath::Path(file_name.to_string())),
    )
}

// Test URI constants
const TEST_URI1: &str = "file:///test1.ts";
const TEST_URI2: &str = "file:///test2.ts";

fn open_change(u: &str, version: i32, content: &str, kind: lsproto::LanguageKind) -> FileChange {
    FileChange {
        kind: FileChangeKind::OPEN,
        uri: uri(u),
        version,
        content: content.to_string(),
        language_kind: kind,
        ..Default::default()
    }
}

fn change(kind: FileChangeKind, u: &str) -> FileChange {
    FileChange {
        kind,
        uri: uri(u),
        ..Default::default()
    }
}

fn file(fs: &OverlayFS, u: &str) -> Rc<dyn FileHandle> {
    fs.get_file(&uri(u).file_name()).expect("file handle")
}

// Go: overlayfs_test.go:37 TestProcessChanges/multiple opens should panic
#[test]
fn multiple_opens_should_panic() {
    let fs = create_overlay_fs();

    let changes = vec![
        open_change(
            TEST_URI1,
            1,
            "const x = 1;",
            lsproto::LanguageKind::TYPE_SCRIPT,
        ),
        open_change(
            TEST_URI2,
            1,
            "const y = 2;",
            lsproto::LanguageKind::TYPE_SCRIPT,
        ),
    ];

    let panicked = catch_unwind(AssertUnwindSafe(|| {
        fs.process_changes(&changes);
    }))
    .is_err();
    assert!(panicked);
}

// Go: overlayfs_test.go:69 TestProcessChanges/watch create then delete becomes nothing
#[test]
fn watch_create_then_delete_becomes_nothing() {
    let fs = create_overlay_fs();

    let changes = vec![
        change(FileChangeKind::WATCH_CREATE, TEST_URI1),
        change(FileChangeKind::WATCH_DELETE, TEST_URI1),
    ];

    let (result, _) = fs.process_changes(&changes);
    assert!(result.is_empty());
}

// Go: overlayfs_test.go:88 TestProcessChanges/watch delete then create becomes change
#[test]
fn watch_delete_then_create_becomes_change() {
    let fs = create_overlay_fs();

    let changes = vec![
        change(FileChangeKind::WATCH_DELETE, TEST_URI1),
        change(FileChangeKind::WATCH_CREATE, TEST_URI1),
    ];

    let (result, _) = fs.process_changes(&changes);

    assert_eq!(result.created.len(), 0);
    assert_eq!(result.deleted.len(), 0);
    assert!(result.changed.contains(&uri(TEST_URI1)));
}

// Go: overlayfs_test.go:110 TestProcessChanges/multiple watch changes deduplicated
#[test]
fn multiple_watch_changes_deduplicated() {
    let fs = create_overlay_fs();

    let changes = vec![
        change(FileChangeKind::WATCH_CHANGE, TEST_URI1),
        change(FileChangeKind::WATCH_CHANGE, TEST_URI1),
        change(FileChangeKind::WATCH_CHANGE, TEST_URI1),
    ];

    let (result, _) = fs.process_changes(&changes);

    assert!(result.changed.contains(&uri(TEST_URI1)));
    assert_eq!(result.changed.len(), 1);
}

// Go: overlayfs_test.go:135 TestProcessChanges/save marks overlay as matching disk
#[test]
fn save_marks_overlay_as_matching_disk() {
    let fs = create_overlay_fs();

    // First create an overlay
    fs.process_changes(&[open_change(
        TEST_URI1,
        1,
        "const x = 1;",
        lsproto::LanguageKind::TYPE_SCRIPT,
    )]);
    // Then save
    let (result, _) = fs.process_changes(&[change(FileChangeKind::SAVE, TEST_URI1)]);
    // We don't observe saves for snapshot changes,
    // so they're not included in the summary
    assert!(result.is_empty());

    // Check that the overlay is marked as matching disk text
    let fh = file(&fs, TEST_URI1);
    assert!(fh.matches_disk_text());
}

// Go: overlayfs_test.go:166 TestProcessChanges/open falls back to file extension for unknown language kind
#[test]
fn open_falls_back_to_file_extension_for_unknown_language_kind() {
    let fs = create_overlay_fs();
    let u = "file:///test1.mts";

    fs.process_changes(&[open_change(
        u,
        1,
        "export const x = 1;",
        lsproto::LanguageKind("mts".into()),
    )]);

    let fh = file(&fs, u);
    assert_eq!(fh.kind(), ScriptKind::TS);
}

// Go: overlayfs_test.go:187 TestProcessChanges/open extensionless file preserves unknown script kind
// PORT: tsgo #4712 renamed this #4628 test (was "open extensionless file with
// unknown language kind falls back to TS") and flipped it to `ScriptKindUnknown`.
#[test]
fn open_extensionless_file_preserves_unknown_script_kind() {
    let fs = create_overlay_fs();
    let u = "file:///script";

    fs.process_changes(&[open_change(
        u,
        1,
        "const x = 1;",
        lsproto::LanguageKind("plaintext".into()),
    )]);

    let fh = file(&fs, u);
    assert_eq!(fh.kind(), ScriptKind::UNKNOWN);
}

// Go: overlayfs_test.go:207 TestProcessChanges/extensionless disk file preserves unknown script kind
// PORT: tsgo #4712 renamed this #4628 test (was "extensionless disk file falls
// back to TS") and flipped it to `ScriptKindUnknown`.
#[test]
fn extensionless_disk_file_preserves_unknown_script_kind() {
    let fs = create_overlay_fs();

    let fh = fs.get_file("/script").expect("file handle");
    assert_eq!(fh.kind(), ScriptKind::UNKNOWN);
}

// Go: overlayfs_test.go:186 TestProcessChanges/watch change on overlay marks as not matching disk
#[test]
fn watch_change_on_overlay_marks_as_not_matching_disk() {
    let fs = create_overlay_fs();

    // First create an overlay
    fs.process_changes(&[open_change(
        TEST_URI1,
        1,
        "const x = 1;",
        lsproto::LanguageKind::TYPE_SCRIPT,
    )]);
    assert!(!file(&fs, TEST_URI1).matches_disk_text());

    // Then save
    fs.process_changes(&[change(FileChangeKind::SAVE, TEST_URI1)]);
    assert!(file(&fs, TEST_URI1).matches_disk_text());

    // Now process a watch change
    fs.process_changes(&[change(FileChangeKind::WATCH_CHANGE, TEST_URI1)]);
    assert!(!file(&fs, TEST_URI1).matches_disk_text());
}

// Go: overlayfs_test.go:221 TestProcessChanges/save without overlay should not panic
#[test]
fn save_without_overlay_should_not_panic() {
    let fs = create_overlay_fs();

    // Save a file that was never opened (no overlay exists).
    let (result, _) = fs.process_changes(&[change(FileChangeKind::SAVE, TEST_URI1)]);
    // Should be treated as a disk change
    assert!(result.changed.contains(&uri(TEST_URI1)));
}

// Go: overlayfs_test.go:238 TestProcessChanges/close then open in same batch marks as changed
#[test]
fn close_then_open_in_same_batch_marks_as_changed() {
    let fs = create_overlay_fs();

    // First create an overlay
    fs.process_changes(&[open_change(
        TEST_URI1,
        1,
        "const x = 1;",
        lsproto::LanguageKind::TYPE_SCRIPT,
    )]);

    // Now close and reopen in the same batch (like Neovim does for file reload)
    let (result, _) = fs.process_changes(&[
        change(FileChangeKind::CLOSE, TEST_URI1),
        open_change(
            TEST_URI1,
            0,
            "const x = 2;",
            lsproto::LanguageKind::TYPE_SCRIPT,
        ),
    ]);

    // Should not be marked as opened since it was already open
    assert!(
        result.opened.0.is_empty(),
        "close then open should not mark as opened"
    );
    // Should also be marked as changed since it was closed and reopened
    assert!(
        result.changed.contains(&uri(TEST_URI1)),
        "close then open should mark as changed"
    );
    // Should have the new content
    let fh = file(&fs, TEST_URI1);
    assert_eq!(fh.content(), "const x = 2;");
}
