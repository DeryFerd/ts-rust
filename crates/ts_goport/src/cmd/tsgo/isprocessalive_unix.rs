//! Go `cmd/tsgo/isprocessalive_unix.go` (`//go:build unix`; the module is
//! declared under `#[cfg(unix)]`).

use rustix::io::Errno;
use rustix::process::{Pid, test_kill_process};

// Go: cmd/tsgo/isprocessalive_unix.go:11 processAliveSupported
pub const PROCESS_ALIVE_SUPPORTED: bool = true;

// Go: cmd/tsgo/isprocessalive_unix.go:18 isProcessAlive
// isProcessAlive checks if a process with the given PID is still running.
// On Unix, FindProcess always succeeds, so we send signal 0 to probe the
// process. If the signal returns nil or EPERM, the process exists (EPERM
// means it exists but we lack permission to signal it). ESRCH or any
// other error indicates the process is gone.
// PORT: `proc.Signal(syscall.Signal(0))` is `kill(pid, 0)`
// (`test_kill_process`). On Linux Go signals through a pidfd; for a live
// pid both give the same result. The only caller passes a pid above 0; Go
// fails for 0 ("os: process not initialized") and -1 (released), so the
// port returns false for any pid of 0 or less.
pub fn is_process_alive(pid: i32) -> bool {
    let Some(pid) = Pid::from_raw(pid.max(0)) else {
        return false;
    };
    match test_kill_process(pid) {
        Ok(()) | Err(Errno::PERM) => true,
        Err(_) => false,
    }
}
