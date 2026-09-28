//! Go: internal/fswatch/walkdir.go (the portable directory walk).
//!
//! PORT: Go uses it on platforms without a native walk (walkdir_other.go)
//! and in tests. On Linux the backends use `walkdir_unix::walk_dir`.
//! `os.Lstat` and `os.ReadDir` are `std::fs`; their error text is the Rust
//! text (Go prints `lstat <path>: <errno text>`).

use crate::fswatch::prelude::*;

use crate::fswatch::unix;
use crate::gostd::errors;

// Go: walkdir.go:14 walkDirGeneric
/// walkDirGeneric is the portable walkDir implementation. It is used as the
/// primary implementation on platforms without a native version, and is
/// tested on all platforms.
///
/// PORT: Go `syscall.ENOTDIR` is `unix::ENOTDIR` (the unix shim has the Go
/// errno values). A non-unix build is out of scope.
pub fn walk_dir_generic(
    dir: &str,
    recursive: bool,
    fn_: Option<&mut (dyn FnMut(&str, bool) -> Result<(), GoError> + '_)>,
) -> Result<(), GoError> {
    let info = match std::fs::symlink_metadata(dir) {
        Ok(info) => info,
        Err(err) => return Err(path_error("lstat", dir, &err)),
    };
    if !info.is_dir() {
        return Err(errors::from_value(unix::ENOTDIR));
    }
    walk_dir_generic_visit(dir, recursive, fn_)
}

// Go: walkdir.go:25 walkDirGenericVisit
pub fn walk_dir_generic_visit(
    dir: &str,
    recursive: bool,
    mut fn_: Option<&mut (dyn FnMut(&str, bool) -> Result<(), GoError> + '_)>,
) -> Result<(), GoError> {
    // Go: entries, err := os.ReadDir(dir)
    let mut entries: Vec<std::fs::DirEntry> = Vec::new();
    let read = std::fs::read_dir(dir).and_then(|rd| {
        for e in rd {
            entries.push(e?);
        }
        Ok(())
    });
    if let Err(err) = read {
        if err.kind() == std::io::ErrorKind::PermissionDenied
            || err.kind() == std::io::ErrorKind::NotFound
        {
            return Ok(());
        }
        return Err(path_error("open", dir, &err));
    }
    // PORT: os.ReadDir returns the entries sorted by file name.
    entries.sort_by_key(std::fs::DirEntry::file_name);
    if let Some(f) = fn_.as_deref_mut() {
        f(dir, true)?;
    }
    for e in &entries {
        // PORT: Go names are bytes; a non-UTF-8 name is converted lossily.
        let name = e.file_name().to_string_lossy().into_owned();
        let path = format!("{dir}{}{name}", std::path::MAIN_SEPARATOR);
        // PORT: Go `e.IsDir()` uses the dirent type without following
        // links; `DirEntry::file_type` does the same. A failed type lookup
        // is "not a directory".
        let is_dir = e.file_type().map(|t| t.is_dir()).unwrap_or(false);
        if is_dir {
            if recursive {
                walk_dir_generic_visit(&path, recursive, fn_.as_deref_mut())?;
            } else if let Some(f) = fn_.as_deref_mut() {
                f(&path, true)?;
            }
        } else if let Some(f) = fn_.as_deref_mut() {
            f(&path, false)?;
        }
    }
    Ok(())
}

// PORT: Go `*fs.PathError` (`op path: err`) for a `std::io::Error`.
pub(crate) fn path_error(op: &str, path: &str, err: &std::io::Error) -> GoError {
    errors::new(format!("{op} {path}: {err}"))
}
