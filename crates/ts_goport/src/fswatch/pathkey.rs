//! Go: internal/fswatch/pathkey.go (ts#64210).

use crate::fswatch::prelude::*;

use crate::fswatch::pathcompare::PathComparer;

// Go: pathkey.go:10 NativePathComparisonAvailable
/// NativePathComparisonAvailable reports whether this platform implements the
/// native watch-name comparison. Volume sensitivity is queried separately.
pub const NATIVE_PATH_COMPARISON_AVAILABLE: bool = NATIVE_PATH_FOLDING;

// Go: pathkey.go:14 PathComparer
/// PathComparer describes the filename equivalence of a watched volume. Its zero
/// value compares bytes exactly. It is immutable and safe to share.
// PORT: named `PathComparerExported` because Go also has the unexported
// `pathComparer` (pathcompare.go), which is `PathComparer` (PORTING "Names").
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct PathComparerExported {
    pub comparer: PathComparer,
}

impl PathComparerExported {
    // Go: pathkey.go:21 PathComparer.Key
    /// Key returns a watch-only comparison key, not a filesystem path or a compiler
    /// identity. Native Darwin comparers use the same CoreFoundation folding as the
    /// watcher. Other comparers preserve bytes, including malformed UTF-8.
    pub fn key(&self, path: &str) -> String {
        if !self.comparer.ignore_case || !NATIVE_PATH_FOLDING {
            return path.to_string();
        }
        if path.contains('\0') {
            return path.to_string();
        }
        let folded = fold_native_path(path);
        if !folded.is_empty() {
            return folded;
        }
        // Invalid UTF-8 and NUL-containing names are opaque, not Unicode aliases.
        path.to_string()
    }

    // Go: pathkey.go:37 PathComparer.Rebase
    /// Rebase replaces a matching directory prefix while preserving the spelling and
    /// byte boundaries of the remaining event path.
    pub fn rebase(&self, path: &str, from: &str, to: &str) -> (String, bool) {
        if !valid_string(path) || !valid_string(from) || path.contains('\0') || from.contains('\0')
        {
            return PathComparer::default().rebase(path, from, to);
        }
        self.comparer.rebase(path, from, to)
    }
}

/// Go `utf8.ValidString` of a Go string in the port form (see `gostring`).
fn valid_string(s: &str) -> bool {
    !crate::scanner_util::contains_go_string_marker(s)
        || std::str::from_utf8(&crate::scanner_util::go_string_bytes(s)).is_ok()
}
