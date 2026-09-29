//! The `tsgo` worker (bin/tsgo.rs `launch`). A process is a worker only
//! when its parent is the launcher that `GOPORT_LAUNCHER_PID` names. A tsgo
//! that a worker starts inherits `GOPORT_WORKER_FD` and
//! `GOPORT_LAUNCHER_PID`, but it must run as a plain tsgo: give its own
//! output and exit code, and send no code on the pipe of that worker.
//!
//! This test process takes the place of the worker, and its parent the
//! place of the launcher. The tsgo gets the write end of a pipe at the
//! number that `GOPORT_WORKER_FD` names, as a worker's child does.
#![cfg(target_os = "linux")]

use std::io::Read;
use std::os::fd::AsRawFd;
use std::process::Command;

#[test]
fn a_tsgo_started_from_a_worker_is_not_a_worker() {
    let launcher = std::os::unix::process::parent_id();
    // `--version` exits 0 and an unknown option exits 1, so the exit code
    // of each run shows that it did the work.
    let cases: [(&[&str], i32); 2] = [(&["--version"], 0), (&["--noSuchOption"], 1)];
    for (args, code) in cases {
        // `GOPORT_LAUNCH=1`: the tsgo starts its own worker.
        for launch in ["0", "1"] {
            let case = format!("{args:?} GOPORT_LAUNCH={launch}");
            // `pipe` sets no close-on-exec flag, so the tsgo gets `write`.
            let (read, write) = rustix::pipe::pipe().unwrap();
            let output = Command::new(env!("CARGO_BIN_EXE_tsgo"))
                .args(args)
                .env("GOPORT_LAUNCH", launch)
                .env("GOPORT_WORKER_FD", write.as_raw_fd().to_string())
                .env("GOPORT_LAUNCHER_PID", launcher.to_string())
                .output()
                .unwrap();
            drop(write);
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert_eq!(output.status.code(), Some(code), "{case}: {stdout}");
            assert!(!stdout.is_empty(), "{case}: no output");
            // End of file comes when the tsgo and its own worker have ended.
            let mut sent = Vec::new();
            std::fs::File::from(read).read_to_end(&mut sent).unwrap();
            assert!(sent.is_empty(), "{case}: sent {sent:?} on the pipe");
        }
    }
}
