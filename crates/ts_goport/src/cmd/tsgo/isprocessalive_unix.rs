//! Go `cmd/tsgo/isprocessalive_unix.go` (`//go:build unix`; the module is
//! declared under `#[cfg(unix)]`).

use crate::cmd::tsgo::prelude::*;

// Go: cmd/tsgo/isprocessalive_unix.go:11 processAliveSupported
pub const PROCESS_ALIVE_SUPPORTED: bool = true;

// Go: cmd/tsgo/isprocessalive_unix.go:18 isProcessAlive
// isProcessAlive checks if a process with the given PID is still running.
// On Unix, FindProcess always succeeds, so we send signal 0 to probe the
// process. If the signal returns nil or EPERM, the process exists (EPERM
// means it exists but we lack permission to signal it). ESRCH or any
// other error indicates the process is gone.
// PORT: sending a signal needs `libc` and `unsafe`, which the crate does
// not allow. On Linux, `/proc/<pid>` exists exactly when signal 0 finds
// the process: also for a zombie and for a process of another user (EPERM).
pub fn is_process_alive(pid: i32) -> bool {
    if cfg!(target_os = "linux") {
        return std::path::Path::new(&format!("/proc/{pid}")).exists();
    }
    unported!("os.Process.Signal")
}
