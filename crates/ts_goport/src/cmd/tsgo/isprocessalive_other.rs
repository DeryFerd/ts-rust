//! Go `cmd/tsc/isprocessalive_other.go` (`//go:build !unix && !windows`;
//! the module is declared under `#[cfg(not(unix))]`).
//!
//! PORT: Go `isprocessalive_windows.go` is not ported (plan: deferred), so
//! Windows uses this file too.

use crate::cmd::tsgo::prelude::*;

// Go: cmd/tsc/isprocessalive_other.go:5 processAliveSupported
pub const PROCESS_ALIVE_SUPPORTED: bool = false;

// Go: cmd/tsc/isprocessalive_other.go:7 isProcessAlive
pub fn is_process_alive(_pid: i32) -> bool {
    panic!("isProcessAlive is not supported on this platform");
}
