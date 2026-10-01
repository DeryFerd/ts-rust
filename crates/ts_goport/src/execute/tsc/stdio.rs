//! Go `os.Stdin`, `os.Stdout` and `os.Stderr`: os/file.go `File.Read` and
//! `File.Write`, os/file_unix.go `NewFile` and `epipecheck`,
//! internal/poll/fd_unix.go `FD.Read` and `FD.Write`.
//!
//! Each read or write of these files:
//! - tries again after EINTR (internal/poll `ignoringEINTRIO`);
//! - waits in the poller on EAGAIN, so a non-blocking fd (a Node or libuv
//!   parent can set O_NONBLOCK on a shared pipe or tty) loses no output and
//!   a read does not fail;
//! - on EPIPE from a write to fd 1 or 2, ends the process by SIGPIPE with
//!   the default action (`epipecheck`, runtime/signal_unix.go `sigpipe` and
//!   `dieFromSignal`). Go does this also when SIGPIPE was ignored at start.
//!
//! PORT: Go waits on EAGAIN only for an fd that was non-blocking at start
//! (`NewFile` gives only such an fd to the poller). Here every EAGAIN waits,
//! also when a parent sets O_NONBLOCK later; Go then returns the EAGAIN
//! error, which `fmt.Fprint` ignores (`CliStdout` keeps the Go rule). Rust
//! ignores SIGPIPE, so a write here gets EPIPE and raises the signal as Go
//! does. A write that writes 0 bytes gives `WriteZero` (Go
//! `io.ErrUnexpectedEOF`). As in Go, none of these files has a buffer,
//! except `CliStdout` on a regular file (see `init`). On Windows these are
//! the std handles, as before.

use std::io;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, MutexGuard, PoisonError};

/// Go `os.Stdin`. Wrap it in a `BufReader` where Go wraps it in a
/// `bufio.Reader`.
pub struct Stdin;

/// Go `os.Stdout`, not buffered. The LSP and API servers use it under the
/// `bufio.Writer` of their base protocol.
pub struct Stdout;

/// Go `os.Stdout` as the tsc system writer uses it: each write is one
/// write of fd 1 (Go `fmt.Fprint` on the unbuffered `os.Stdout`; an empty
/// one too), so the output goes out in Go's pieces (the help, a
/// diagnostic). Only an fd 1 that was non-blocking at start waits on
/// EAGAIN; a later EAGAIN is the write's error, which the tsc writer
/// ignores as Go does. The trace output and the watch manager's lines
/// write here too. A write holds a lock for all of its partial writes, as
/// Go's `poll.FD.Write` holds the write lock of the file, so a line of
/// another thread never lands inside it.
///
/// PORT: when fd 1 is a regular file at start (`init`), the writes are
/// kept and go out together: at 64 KiB, at `flush`, before a write to
/// `Stderr`, at each turn of the watch loop and at exit
/// (`flush_cli_stdout_at_exit`). Only the system calls change: a file has
/// no reader that sees the pieces and cannot raise EPIPE. A write error
/// comes at the flush. A run that ends in `core::go_fatal_newosproc` (the
/// OS refuses a thread) loses the kept bytes.
pub struct CliStdout;

/// Go `os.Stderr`.
pub struct Stderr;

// Go: os/file.go:73 `Stdout = NewFile(...)`, at package init (go1.27.1)
/// Reads whether fd 1 is non-blocking (see `CliStdout`). tsgo calls it at
/// start, as Go makes `os.Stdout` before `main`; without the call the first
/// write of `CliStdout` reads it.
/// PORT: it also reads whether fd 1 is a regular file: then `CliStdout`
/// keeps its writes (see there). Only a bin that calls `init` (tsgo) gets
/// that, and it must flush at exit.
pub fn init() {
    sys::init();
    COALESCE.store(sys::stdout_is_regular_file(), Ordering::Relaxed);
}

/// `CliStdout` keeps its writes (see `init`).
static COALESCE: AtomicBool = AtomicBool::new(false);

/// The write lock of `CliStdout` (Go `poll.FD.writeLock`), with the bytes
/// that it keeps when `COALESCE` is set.
static CLI_STDOUT: Mutex<Vec<u8>> = Mutex::new(Vec::new());

/// The kept bytes of `CliStdout` go out at this size.
const COALESCE_LIMIT: usize = 64 << 10;

fn cli_stdout_lock() -> MutexGuard<'static, Vec<u8>> {
    CLI_STDOUT.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Writes the bytes that `CliStdout` keeps (see `init`).
fn write_kept(kept: &mut Vec<u8>) -> io::Result<()> {
    if kept.is_empty() {
        return Ok(());
    }
    let result = sys::write_cli_stdout(kept);
    kept.clear();
    result
}

/// Writes the bytes that `CliStdout` keeps, for a run that ends without its
/// `flush` (a thrown signal). It does not wait for a writer that holds the
/// lock: that writer can be the thread that the signal stops.
pub fn flush_cli_stdout_at_exit() {
    if let Ok(mut kept) = CLI_STDOUT.try_lock() {
        let _ = write_kept(&mut kept);
    }
}

impl io::Read for Stdin {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        sys::read_stdin(buf)
    }
}

impl io::Write for Stdout {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        sys::write_stdout(buf)?;
        Ok(buf.len())
    }

    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        sys::write_stdout(buf)
    }

    /// Go `fmt.Fprintf`: one write of the whole text.
    fn write_fmt(&mut self, args: std::fmt::Arguments<'_>) -> io::Result<()> {
        sys::write_stdout(std::fmt::format(args).as_bytes())
    }

    fn flush(&mut self) -> io::Result<()> {
        sys::flush_stdout()
    }
}

impl io::Write for CliStdout {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.write_all(buf)?;
        Ok(buf.len())
    }

    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        let mut kept = cli_stdout_lock();
        if !COALESCE.load(Ordering::Relaxed) {
            return sys::write_cli_stdout(buf);
        }
        kept.extend_from_slice(buf);
        if kept.len() < COALESCE_LIMIT {
            return Ok(());
        }
        write_kept(&mut kept)
    }

    fn flush(&mut self) -> io::Result<()> {
        write_kept(&mut cli_stdout_lock())?;
        sys::flush_cli_stdout()
    }
}

// PORT: each write first writes what `CliStdout` keeps (see `init`), so
// stdout and stderr keep their order in one file (`2>&1`).
impl io::Write for Stderr {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.write_all(buf)?;
        Ok(buf.len())
    }

    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        if COALESCE.load(Ordering::Relaxed) {
            let _ = write_kept(&mut cli_stdout_lock());
        }
        sys::write_stderr(buf)
    }

    /// Go `fmt.Fprintf`: one write of the whole text.
    fn write_fmt(&mut self, args: std::fmt::Arguments<'_>) -> io::Result<()> {
        self.write_all(std::fmt::format(args).as_bytes())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[cfg(unix)]
mod sys {
    use rustix::event::{PollFd, PollFlags, poll};
    use rustix::fd::BorrowedFd;
    use rustix::fs::OFlags;
    use rustix::io::Errno;
    use std::io;
    use std::sync::OnceLock;

    pub fn read_stdin(buf: &mut [u8]) -> io::Result<usize> {
        // Go: internal/poll/fd_unix.go FD.Read
        let fd = rustix::stdio::stdin();
        loop {
            match rustix::io::read(fd, &mut *buf) {
                Ok(n) => return Ok(n),
                Err(Errno::INTR) => {}
                Err(Errno::AGAIN) => wait(fd, PollFlags::IN)?,
                Err(err) => return Err(err.into()),
            }
        }
    }

    pub fn write_stdout(buf: &[u8]) -> io::Result<()> {
        write(rustix::stdio::stdout(), buf)
    }

    pub fn write_stderr(buf: &[u8]) -> io::Result<()> {
        write(rustix::stdio::stderr(), buf)
    }

    pub fn flush_stdout() -> io::Result<()> {
        Ok(())
    }

    // Go: internal/poll/fd_unix.go FD.Write
    fn write(fd: BorrowedFd<'static>, mut buf: &[u8]) -> io::Result<()> {
        while !buf.is_empty() {
            match rustix::io::write(fd, buf) {
                Ok(0) => return Err(io::ErrorKind::WriteZero.into()),
                Ok(n) => buf = &buf[n..],
                Err(err) => after_write_error(fd, err.into())?,
            }
        }
        Ok(())
    }

    pub fn init() {
        stdout_nonblocking();
    }

    pub fn stdout_is_regular_file() -> bool {
        rustix::fs::fstat(rustix::stdio::stdout()).is_ok_and(|stat| {
            rustix::fs::FileType::from_raw_mode(stat.st_mode) == rustix::fs::FileType::RegularFile
        })
    }

    /// Go `NewFile`: fd 1 was non-blocking at start (`init`), so its writes
    /// wait in the poller on EAGAIN.
    fn stdout_nonblocking() -> bool {
        static NONBLOCKING: OnceLock<bool> = OnceLock::new();
        *NONBLOCKING.get_or_init(|| {
            rustix::fs::fcntl_getfl(rustix::stdio::stdout())
                .is_ok_and(|flags| flags.contains(OFlags::NONBLOCK))
        })
    }

    // Go: internal/poll/fd_unix.go FD.Write and os/file.go File.Write
    // (`epipecheck`). The first write runs also for an empty `buf`. EAGAIN
    // waits only when fd 1 was non-blocking at start.
    pub fn write_cli_stdout(mut buf: &[u8]) -> io::Result<()> {
        let fd = rustix::stdio::stdout();
        loop {
            match rustix::io::write(fd, buf) {
                Ok(n) if n == buf.len() => return Ok(()),
                Ok(0) => return Err(io::ErrorKind::WriteZero.into()),
                Ok(n) => buf = &buf[n..],
                Err(Errno::AGAIN) if !stdout_nonblocking() => return Err(Errno::AGAIN.into()),
                Err(err) => after_write_error(fd, err.into())?,
            }
        }
    }

    pub fn flush_cli_stdout() -> io::Result<()> {
        Ok(())
    }

    /// Ok when the write to `fd` should be tried again (EINTR, or EAGAIN
    /// once `fd` is writable), else `err`. EPIPE (fd 1 or 2 only) ends the
    /// process: os/file_unix.go epipecheck.
    fn after_write_error(fd: BorrowedFd<'static>, err: io::Error) -> io::Result<()> {
        match Errno::from_io_error(&err) {
            Some(Errno::INTR) => Ok(()),
            Some(Errno::AGAIN) => wait(fd, PollFlags::OUT),
            Some(Errno::PIPE) => sigpipe(),
            _ => Err(err),
        }
    }

    /// Go: the poller's `waitRead` and `waitWrite`. The caller tries the
    /// read or write again, also after a signal or POLLHUP and POLLERR,
    /// which then give that call its error.
    fn wait(fd: BorrowedFd<'static>, events: PollFlags) -> io::Result<()> {
        match poll(&mut [PollFd::from_borrowed_fd(fd, events)], None) {
            Ok(_) | Err(Errno::INTR) => Ok(()),
            Err(err) => Err(err.into()),
        }
    }

    // Go: runtime/signal_unix.go sigpipe and dieFromSignal. tsgo neither
    // ignores nor catches SIGPIPE through os/signal, so this always ends
    // the process. `emulate_default_handler` sets the default action,
    // unblocks the signal and raises it (it aborts if that returns).
    fn sigpipe() -> ! {
        let _ = signal_hook::low_level::emulate_default_handler(signal_hook::consts::SIGPIPE);
        // PORT: not reached: for SIGPIPE `emulate_default_handler` does not
        // return. When the raised signal does not end the process, it
        // aborts (SIGABRT), where Go's `dieFromSignal` exits 2.
        std::process::exit(2)
    }
}

#[cfg(not(unix))]
mod sys {
    use std::io::{self, Read, Write};

    pub fn init() {}

    pub fn stdout_is_regular_file() -> bool {
        false
    }

    pub fn read_stdin(buf: &mut [u8]) -> io::Result<usize> {
        io::stdin().read(buf)
    }

    pub fn write_stdout(buf: &[u8]) -> io::Result<()> {
        io::stdout().write_all(buf)
    }

    pub fn flush_stdout() -> io::Result<()> {
        io::stdout().flush()
    }

    pub fn write_cli_stdout(buf: &[u8]) -> io::Result<()> {
        io::stdout().write_all(buf)
    }

    pub fn flush_cli_stdout() -> io::Result<()> {
        io::stdout().flush()
    }

    pub fn write_stderr(buf: &[u8]) -> io::Result<()> {
        io::stderr().write_all(buf)
    }
}
