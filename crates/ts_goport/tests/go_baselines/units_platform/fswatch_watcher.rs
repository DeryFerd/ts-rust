//! Go: `internal/fswatch/watcher_test.go` and `testutil_test.go` helpers.

use std::path::PathBuf;

use crate::astnav_api::jstest::TempDir;

// Go: watcher_test.go:110 newTmpDir
/// A fresh temp dir with symlinks resolved, so it matches what backends
/// report. The `TempDir` removes it on drop.
pub(crate) fn new_tmp_dir() -> (TempDir, PathBuf) {
    let d = TempDir::new();
    let resolved = d.path().canonicalize().expect("EvalSymlinks");
    (d, resolved)
}
