//! Go: `internal/bundled/bundled_test.go`.
//!
//! These tests run only on the default (embed) build.
//!
//! Blocked: `TestTestingLibPath`. Go `bundled.TestingLibPath` is for Go tests
//! only and is not ported (see `src/frontend/bundled.rs`).

use ts_goport::frontend::bundled;
use ts_goport::frontend::vfs::osvfs_fs;

// Go: bundled_test.go:28 TestEmbeddedLibs (ts#64277)
#[test]
fn test_embedded_libs() {
    let fs = bundled::wrap_fs(osvfs_fs());

    let mut files = fs.get_accessible_entries(&bundled::lib_path()).files;
    files.sort();
    let want: Vec<String> = bundled::LIB_NAMES.iter().map(|s| s.to_string()).collect();
    assert_eq!(files, want);
}
