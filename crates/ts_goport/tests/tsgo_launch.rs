//! The `tsgo` worker check (bin/tsgo.rs `launch`, `worker` and
//! `send_code`). A process is a worker only when its `arg0` is
//! `tsgo-worker <launcher> <fd> <inode>` and its parent is that launcher.
//! A worker sends its exit code on the launcher's pipe, and only to a FIFO
//! with that inode. Any other tsgo, also one whose `arg0` names a launcher
//! that is not its parent, runs as a plain tsgo: it gives its own output
//! and exit code and sends nothing.
//!
//! This test process takes the place of the launcher: it holds the read
//! end of a pipe, which the tsgo opens through /proc as a worker does.
#![cfg(target_os = "linux")]

use std::io::Read;
use std::os::fd::AsRawFd;
use std::os::unix::process::CommandExt;
use std::process::Command;

#[test]
fn a_tsgo_started_from_a_worker_is_not_a_worker() {
    let this = std::process::id();
    let parent = std::os::unix::process::parent_id();
    // `--version` exits 0 and an unknown option exits 1, so the exit code
    // of each run shows that it did the work.
    let cases: [(&[&str], i32); 2] = [(&["--version"], 0), (&["--noSuchOption"], 1)];
    for (args, code) in cases {
        // `GOPORT_LAUNCH=1`: a tsgo that is not a worker starts its own.
        for launch in ["0", "1"] {
            // Both ends have a close-on-exec flag: the tsgo gets neither.
            let (read, write) = rustix::pipe::pipe_with(rustix::pipe::PipeFlags::CLOEXEC).unwrap();
            drop(write);
            let fd = read.as_raw_fd();
            let ino = rustix::fs::fstat(&read).unwrap().st_ino;
            // (arg0, whether the tsgo sends `code` on the pipe)
            let runs = [
                (format!("tsgo-worker {this} {fd} {ino}"), true),
                // The named launcher is not the parent.
                (format!("tsgo-worker {parent} {fd} {ino}"), false),
                // The file at the number is not the launcher's pipe.
                (format!("tsgo-worker {this} {fd} {}", ino + 1), false),
                (format!("tsgo-worker {this} {fd}"), false),
                ("tsgo".to_string(), false),
            ];
            for (arg0, sends) in runs {
                let case = format!("{args:?} GOPORT_LAUNCH={launch} arg0 {arg0:?}");
                let output = Command::new(env!("CARGO_BIN_EXE_tsgo"))
                    .arg0(&arg0)
                    .args(args)
                    .env("GOPORT_LAUNCH", launch)
                    .output()
                    .unwrap();
                let stdout = String::from_utf8_lossy(&output.stdout);
                assert_eq!(output.status.code(), Some(code), "{case}: {stdout}");
                assert!(!stdout.is_empty(), "{case}: no output");
                // The tsgo has ended and no process has the pipe open for
                // writing (a worker of the tsgo never opens it), so this
                // reads what the tsgo sent and then the end of file.
                let mut sent = Vec::new();
                let mut pipe = std::fs::File::from(read.try_clone().unwrap());
                pipe.read_to_end(&mut sent).unwrap();
                let expected = if sends {
                    code.to_le_bytes().to_vec()
                } else {
                    Vec::new()
                };
                assert_eq!(sent, expected, "{case}: sent on the pipe");
            }
        }
    }
}
