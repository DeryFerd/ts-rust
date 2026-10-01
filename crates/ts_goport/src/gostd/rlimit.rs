//! Go `syscall` RLIMIT_NOFILE handling (syscall/rlimit.go, go1.27.1). A Go
//! process raises its soft open-file limit to one below the hard limit at
//! start, and a process that it starts gets the original limit back
//! (syscall/exec_linux.go forkAndExecInChild1).

#[cfg(unix)]
use std::sync::OnceLock;

/// The open-file limit at start, when `raise_open_file_limit` raised it.
#[cfg(unix)]
static ORIGINAL: OnceLock<rustix::process::Rlimit> = OnceLock::new();

// Go: rlimit.go:30 init
/// Raises the soft open-file limit to one below the hard limit (Go uses
/// one below, so that it can see a later change by another process's
/// `prlimit`). The bins call it at start, before other threads open files.
/// PORT: Go on macOS lowers the raised limit to `kern.maxfilesperproc`
/// (`adjustFileLimit`). The port does not raise to an unlimited hard
/// limit (on Linux that fails in Go too).
pub fn raise_open_file_limit() {
    #[cfg(unix)]
    {
        use rustix::process::{Resource, Rlimit, getrlimit, setrlimit};
        let limit = getrlimit(Resource::Nofile);
        let (Some(current), Some(max)) = (limit.current, limit.maximum) else {
            return;
        };
        if max == 0 || current >= max - 1 {
            return;
        }
        let raised = Rlimit {
            current: Some(max - 1),
            maximum: Some(max),
        };
        if setrlimit(Resource::Nofile, raised).is_ok() {
            let _ = ORIGINAL.set(limit);
        }
    }
}

// Go: exec_linux.go:644 "Restore original rlimit."
/// Gives `child`, which this process started, the open-file limit that
/// this process had before `raise_open_file_limit`, unless another process
/// changed this process's limit since then.
/// PORT: Go sets it between fork and exec. Without `unsafe` (no
/// `pre_exec`) the port sets it on the started child (`prlimit`), so the
/// child's first steps run with the raised limit.
#[cfg(target_os = "linux")]
pub fn restore_open_file_limit(child: &std::process::Child) {
    use rustix::process::{Pid, Resource, getrlimit, prlimit};
    let Some(&original) = ORIGINAL.get() else {
        return;
    };
    let now = getrlimit(Resource::Nofile);
    let max = original.maximum;
    if now.maximum == max && now.current == max.map(|max| max - 1) {
        let _ = prlimit(Some(Pid::from_child(child)), Resource::Nofile, original);
    }
}
