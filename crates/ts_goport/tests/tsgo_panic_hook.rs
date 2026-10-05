//! The tsgo panic hook (bin/tsgo.rs `install_panic_hook`) and the getwd
//! error of `new_os_system` write with stderr a pipe that has no reader, so
//! each write gets EPIPE. With `eprintln!` the hook panicked again, and a
//! panic inside the hook aborts the process (SIGABRT), also for a panic that
//! a caller catches (a resolve-ahead worker panic in `run_task`). The hook
//! must drop its write errors, and the run then ends as it does with a
//! reader. The getwd error and the bad flag text of `--lsp` and `--api` are
//! Go writes to `os.Stderr`, which end the process by SIGPIPE as in Go.
//!
//! The work thread failure write (bin/tsgo.rs `main`, "tsgo: work thread
//! failed") also drops its error. Its test needs a panic outside the
//! `catch_unwind` of `run_main`: at a low fd limit, `notify_context` cannot
//! make the signal-hook pipe and panics (a port gap: Go N needs no fd for
//! `signal.Notify` and runs).
//!
//! The panic of the hook test: tsgo reads the current directory again when it installs the
//! program (`execute_tsc::install_program`), and a removed directory panics
//! there ("cannot load program: getwd: ..."). Go reads it once, in
//! `newSystem`, so this is a port gap; the test uses it only as a panic that
//! the hook prints. The config is a FIFO: tsgo opens it after its first read
//! of the directory, and the test removes the directory before it writes the
//! config. When a change removes this panic, the control run fails: then use
//! another panic that the hook prints.
#![cfg(target_os = "linux")]

use std::io::Write;
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

use ts_goport::execute::tsc::EXIT_UNPORTED;

/// The longest wait for each step of a run.
const LIMIT: Duration = Duration::from_secs(60);

#[test]
fn a_printed_panic_with_no_stderr_reader_does_not_abort() {
    // Control: with a reader, the hook prints the panic and the run ends
    // with the unported exit code.
    let (status, stderr) = run("control", Stdio::piped(), false);
    let stderr = String::from_utf8_lossy(&stderr);
    assert_eq!(
        status.code(),
        Some(EXIT_UNPORTED),
        "control: {status} {stderr}"
    );
    assert!(
        stderr.starts_with("tsgo: panic at ") && stderr.contains("cannot load program"),
        "control: the hook must print the panic:\n{stderr}"
    );
    // No reader: the same exit, not SIGABRT. GOPORT_TRACE adds the
    // backtrace write.
    let (reader, writer) = std::io::pipe().unwrap();
    drop(reader);
    let (status, _) = run("closed", Stdio::from(writer), true);
    assert_eq!(status.signal(), None, "closed stderr: {status}");
    assert_eq!(
        status.code(),
        Some(EXIT_UNPORTED),
        "closed stderr: {status}"
    );
}

/// The getwd error of `new_os_system` (Go cmd/tsc/sys.go:127 `newSystem`)
/// with stderr a pipe that has no reader. Go N writes the error to
/// `os.Stderr`, gets EPIPE and ends by SIGPIPE (`os/file_unix.go`
/// `epipecheck`), also when SIGPIPE was ignored at start. The port wrote it
/// with `eprintln!`, which panicked outside the `catch_unwind` of
/// `run_main`: the work thread failed (bin/tsgo.rs `main`) and the run
/// exited 70. With a reader, both write the error and exit 3; the control
/// run checks that.
#[test]
fn a_getwd_error_with_no_stderr_reader_ends_by_sigpipe() {
    // Control: with a reader, the getwd error and exit code 3.
    let (status, stderr) = run_in_removed_cwd("wtcontrol", Stdio::piped());
    let stderr = String::from_utf8_lossy(&stderr);
    assert_eq!(status.code(), Some(3), "control: {status} {stderr}");
    assert!(
        stderr.starts_with("Error getting current directory: getwd: "),
        "control: {stderr}"
    );
    // No reader: SIGPIPE, as Go N (not exit code 70 or 101).
    let (reader, writer) = std::io::pipe().unwrap();
    drop(reader);
    let (status, _) = run_in_removed_cwd("wtclosed", Stdio::from(writer));
    assert_eq!(
        status.signal(),
        Some(rustix::process::Signal::PIPE.as_raw()),
        "closed stderr: {status}"
    );
}

/// A bad flag of `tsgo --lsp` and `tsgo --api` (Go cmd/tsc/lsp.go:20
/// runLSP and api.go runAPI, `flag.ContinueOnError`). Go flag.go:1050
/// `FlagSet.sprintf`, `defaultUsage` and `PrintDefaults` write to
/// `os.Stderr` (`FlagSet.Output`), one write each, with the raw bytes of
/// the argument. With a stderr pipe that has no reader, Go N
/// (tsgo-oracle-673a5f17d713) ends by SIGPIPE in both modes (followups24
/// flag-go.txt). The port wrote with `eprint!`, which panicked inside the
/// `catch_unwind` of the mode, so the run exited 70, and it wrote the port
/// form of a raw byte. With a reader, both write Go's text and exit 2.
#[test]
fn a_bad_server_flag_with_no_stderr_reader_ends_by_sigpipe() {
    for mode in ["--lsp", "--api"] {
        // Control: with a reader, Go's text and exit code 2.
        let (status, stderr) = run_with_flag(mode, Stdio::piped());
        let usage = format!("Usage of {}:\n", &mode[2..]);
        let mut want = b"flag provided but not defined: -x\xff\n".to_vec();
        want.extend_from_slice(usage.as_bytes());
        if mode == "--lsp" {
            for line in [
                "  -clientProcessId int\n    \tuse the given PID for the parent process watchdog\n",
                "  -pipe string\n    \tuse named pipe for communication\n",
                "  -pprofDir string\n    \tGenerate pprof CPU/memory profiles to the given directory.\n",
                "  -socket string\n    \tuse socket for communication\n",
                "  -stdio\n    \tuse stdio for communication\n",
            ] {
                want.extend_from_slice(line.as_bytes());
            }
            assert_eq!(stderr, want, "{mode} control: {status}");
        } else {
            assert!(stderr.starts_with(&want), "{mode} control: {status} {stderr:?}");
        }
        assert_eq!(status.code(), Some(2), "{mode} control: {status}");
        // No reader: SIGPIPE, as Go N (not exit code 70).
        let (reader, writer) = std::io::pipe().unwrap();
        drop(reader);
        let (status, _) = run_with_flag(mode, Stdio::from(writer));
        assert_eq!(
            status.signal(),
            Some(rustix::process::Signal::PIPE.as_raw()),
            "{mode} closed stderr: {status}"
        );
    }
}

/// Runs `tsgo <mode> -x<FF>` (a flag that is not defined, with a raw byte)
/// and returns the exit status and the stderr (empty when `stderr` is not a
/// pipe to this process).
fn run_with_flag(mode: &str, stderr: Stdio) -> (ExitStatus, Vec<u8>) {
    use std::os::unix::ffi::OsStrExt;
    let mut child = Command::new(env!("CARGO_BIN_EXE_tsgo"))
        .arg(mode)
        .arg(std::ffi::OsStr::from_bytes(b"-x\xff"))
        .env_remove("GOPORT_TRACE")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(stderr)
        .spawn()
        .unwrap();
    let status = wait(&mut child, mode);
    let mut out = Vec::new();
    if let Some(mut pipe) = child.stderr.take() {
        std::io::Read::read_to_end(&mut pipe, &mut out).unwrap();
    }
    (status, out)
}

/// A panic outside the `catch_unwind` of `run_main` ends the work thread,
/// and bin/tsgo.rs `main` writes "tsgo: work thread failed" and exits 70.
/// With stderr a pipe that has no reader, that write and the hook's drop
/// their errors: the same exit, not 101 (a panic of the main thread) or
/// SIGABRT. Go has no such path: a Go panic exits 2.
///
/// The panic: `notify_context` (`Signals::new`) cannot make its pipe at a
/// low fd limit. Go N (tsgo-oracle-673a5f17d713) needs no fd there and
/// prints its version at a limit of 4 (followups24 lowfd-go.txt), so this
/// is a port gap that the test only uses. The control finds the lowest
/// limit at which tsgo starts (the dynamic loader opens its libraries) and
/// the panic ends the work thread; an inherited fd only moves that limit.
/// When a change removes the panic, the control fails: then use another
/// panic outside the `catch_unwind`.
#[test]
fn a_panic_outside_catch_unwind_with_no_stderr_reader_exits_unported() {
    let limit = (3..=32)
        .find(|&limit| {
            let (status, stderr) = run_with_fd_limit(limit, Stdio::piped());
            let stderr = String::from_utf8_lossy(&stderr);
            if !stderr.contains("tsgo: work thread failed") {
                assert!(
                    !status.success(),
                    "control at fd limit {limit}: tsgo ran: {stderr}"
                );
                return false;
            }
            assert_eq!(
                status.code(),
                Some(EXIT_UNPORTED),
                "control at fd limit {limit}: {status} {stderr}"
            );
            assert!(
                stderr.starts_with("tsgo: panic at ")
                    && stderr.contains("signal.Notify: cannot register SIGINT and SIGTERM"),
                "control at fd limit {limit}: {stderr}"
            );
            true
        })
        .expect("control: no fd limit ends the work thread");
    // No reader: the same exit.
    let (reader, writer) = std::io::pipe().unwrap();
    drop(reader);
    let (status, _) = run_with_fd_limit(limit, Stdio::from(writer));
    assert_eq!(status.signal(), None, "closed stderr: {status}");
    assert_eq!(
        status.code(),
        Some(EXIT_UNPORTED),
        "closed stderr: {status}"
    );
}

/// Runs `tsgo --version` with the fd limit `limit` (soft and hard, `sh`
/// `ulimit -n`) and no launcher, and returns the exit status and the
/// stderr (empty when `stderr` is not a pipe to this process).
fn run_with_fd_limit(limit: u32, stderr: Stdio) -> (ExitStatus, Vec<u8>) {
    let case = format!("fd limit {limit}");
    let mut child = Command::new("sh")
        .arg("-c")
        .arg(r#"ulimit -n "$1" && exec "$2" --version"#)
        .arg("sh")
        .arg(limit.to_string())
        .arg(env!("CARGO_BIN_EXE_tsgo"))
        .env_remove("GOPORT_TRACE")
        .env("GOPORT_LAUNCH", "0")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(stderr)
        .spawn()
        .unwrap();
    let status = wait(&mut child, &case);
    let mut out = Vec::new();
    if let Some(mut pipe) = child.stderr.take() {
        std::io::Read::read_to_end(&mut pipe, &mut out).unwrap();
    }
    (status, out)
}

/// Runs `tsgo` with no arguments in a directory that `sh` removes before it
/// starts tsgo, with no `PWD`, and returns the exit status and the stderr
/// (empty when `stderr` is not a pipe to this process).
fn run_in_removed_cwd(case: &str, stderr: Stdio) -> (ExitStatus, Vec<u8>) {
    let dir = TempDir::new(
        std::env::temp_dir().join(format!("tsgo_panic_hook-{}-{case}", std::process::id())),
    );
    let cwd = dir.0.join("cwd");
    std::fs::create_dir(&cwd).unwrap();
    let mut child = Command::new("sh")
        .arg("-c")
        .arg(r#"cd "$1" && rmdir "$1" && unset PWD && exec "$2""#)
        .arg("sh")
        .arg(&cwd)
        .arg(env!("CARGO_BIN_EXE_tsgo"))
        .env_remove("GOPORT_TRACE")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(stderr)
        .spawn()
        .unwrap();
    let status = wait(&mut child, case);
    let mut out = Vec::new();
    if let Some(mut pipe) = child.stderr.take() {
        std::io::Read::read_to_end(&mut pipe, &mut out).unwrap();
    }
    (status, out)
}

/// Runs `tsgo -p <FIFO>` in a directory that the test removes while tsgo
/// waits on the config, and returns the exit status and the stderr (empty
/// when `stderr` is not a pipe to this process).
fn run(case: &str, stderr: Stdio, trace: bool) -> (ExitStatus, Vec<u8>) {
    let dir = TempDir::new(
        std::env::temp_dir().join(format!("tsgo_panic_hook-{}-{case}", std::process::id())),
    );
    let project = dir.0.join("p");
    let cwd = dir.0.join("cwd");
    std::fs::create_dir(&project).unwrap();
    std::fs::create_dir(&cwd).unwrap();
    std::fs::write(project.join("a.ts"), "export {};\n").unwrap();
    let config = project.join("tsconfig.json");
    let mode = rustix::fs::Mode::RUSR | rustix::fs::Mode::WUSR;
    rustix::fs::mkfifoat(rustix::fs::CWD, &config, mode).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_tsgo"));
    command
        .arg("-p")
        .arg(&config)
        .current_dir(&cwd)
        .env_remove("PWD")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(stderr);
    if trace {
        command.env("GOPORT_TRACE", "1");
    } else {
        command.env_remove("GOPORT_TRACE");
    }
    let mut child = command.spawn().unwrap();
    let mut fifo = open_fifo_writer(&config, &mut child, case);
    std::fs::remove_dir(&cwd).unwrap();
    fifo.write_all(br#"{"compilerOptions": {"noLib": true, "types": []}, "files": ["a.ts"]}"#)
        .unwrap();
    drop(fifo);
    let status = wait(&mut child, case);
    let mut out = Vec::new();
    if let Some(mut pipe) = child.stderr.take() {
        std::io::Read::read_to_end(&mut pipe, &mut out).unwrap();
    }
    (status, out)
}

/// Opens the FIFO `path` for writing once `child` has opened it for reading.
fn open_fifo_writer(path: &Path, child: &mut Child, case: &str) -> std::fs::File {
    let until = Instant::now() + LIMIT;
    loop {
        // Without a reader, a nonblocking open for writing fails with ENXIO.
        match std::fs::File::options()
            .write(true)
            .custom_flags(rustix::fs::OFlags::NONBLOCK.bits().cast_signed())
            .open(path)
        {
            Ok(file) => return file,
            Err(err) if err.raw_os_error() == Some(rustix::io::Errno::NXIO.raw_os_error()) => {}
            Err(err) => panic!("{case}: open the config FIFO: {err}"),
        }
        if let Some(status) = child.try_wait().unwrap() {
            panic!("{case}: tsgo ended before it read the config: {status}");
        }
        if Instant::now() > until {
            let _ = child.kill();
            panic!("{case}: tsgo did not open the config FIFO");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

/// Waits for `child`; a tsgo that has not ended after `LIMIT` fails the test.
fn wait(child: &mut Child, case: &str) -> ExitStatus {
    let until = Instant::now() + LIMIT;
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            return status;
        }
        if Instant::now() > until {
            let _ = child.kill();
            panic!("{case}: tsgo did not end");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

struct TempDir(PathBuf);

impl TempDir {
    fn new(path: PathBuf) -> Self {
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir(&path).unwrap();
        TempDir(path)
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
