//! Go: internal/fswatch/canonicalize_other.go.
//!
//! PORT: Go builds this file on every platform except darwin (amd64 and
//! arm64), which uses canonicalize_darwin.go (NFD path normalization); so
//! does the port (canonicalize_darwin.rs).

use crate::fswatch::prelude::*;

// Go: canonicalize_other.go:8 canonicalizePath
/// canonicalizePath is a no-op on platforms whose watchers report paths
/// using the same bytes the caller provided. See canonicalize_darwin.go
/// for the rationale on macOS.
pub fn canonicalize_path(p: &str) -> String {
    p.to_string()
}
