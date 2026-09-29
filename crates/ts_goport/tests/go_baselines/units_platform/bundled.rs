//! Go: `internal/bundled/bundled_test.go`.
//!
//! These tests run only on the default (embed) build.
//!
//! Blocked: `TestTestingLibPath`. Go `bundled.TestingLibPath` is for Go tests
//! only and is not ported (see `src/frontend/bundled.rs`).

use std::cell::RefCell;

use ts_goport::frontend::bundled;
use ts_goport::frontend::tspath;
use ts_goport::frontend::vfs::osvfs_fs;

// Go: bundled_test.go:30 TestEmbeddedLibs
#[test]
fn test_embedded_libs() {
    let fs = bundled::wrap_fs(osvfs_fs());
    let files: RefCell<Vec<String>> = RefCell::new(Vec::new());
    let result = fs.walk_dir(&bundled::lib_path(), &mut |path, d, err| {
        if let Some(err) = err {
            return Err(err);
        }
        if !d.expect("a dir entry").is_dir() {
            files.borrow_mut().push(tspath::get_base_file_name(path));
        }
        Ok(())
    });
    assert!(result.is_ok(), "walk_dir failed: {:?}", result.err());
    let want: Vec<String> = bundled::LIB_NAMES.iter().map(|s| s.to_string()).collect();
    assert_eq!(files.into_inner(), want);
}
