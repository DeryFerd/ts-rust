//! Go `os.Stdin`, `os.Stdout` and `os.Stderr`: os/file.go `File.Read` and
//! `File.Write`, os/file_unix.go `NewFile` and `epipecheck`,
//! internal/poll/fd_unix.go `FD.Read` and `FD.Write`.
//!
//! Go does not buffer these files. Each read or write:
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
//! error, which `fmt.Fprint` ignores. Rust ignores SIGPIPE, so a write here
//! gets EPIPE and raises the signal as Go does. A write that writes 0 bytes
//! gives `WriteZero` (Go `io.ErrUnexpectedEOF`). On Windows these are the
//! std handles, as before.

use std::io;

/// Go `os.Stdin`. Wrap it in a `BufReader` where Go wraps it in a
/// `bufio.Reader`.
pub struct Stdin;

/// Go `os.Stdout`.
pub struct Stdout;

/// Go `os.Stderr`.
pub struct Stderr;

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

impl io::Write for Stderr {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        sys::write_stderr(buf)?;
        Ok(buf.len())
    }

    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        sys::write_stderr(buf)
    }

    /// Go `fmt.Fprintf`: one write of the whole text.
    fn write_fmt(&mut self, args: std::fmt::Arguments<'_>) -> io::Result<()> {
        sys::write_stderr(std::fmt::format(args).as_bytes())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

#[cfg(unix)]
mod sys {
    use rustix::event::{PollFd, PollFlags, poll};
    use rustix::fd::BorrowedFd;
    use rustix::io::Errno;
    use std::io;

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

    /// Nothing is buffered here. Other port code still writes whole lines
    /// through std's line-buffered stdout, so a flush flushes that too.
    pub fn flush_stdout() -> io::Result<()> {
        io::Write::flush(&mut io::stdout())
    }

    // Go: internal/poll/fd_unix.go FD.Write, then os/file_unix.go
    // epipecheck for fds 1 and 2.
    fn write(fd: BorrowedFd<'static>, mut buf: &[u8]) -> io::Result<()> {
        while !buf.is_empty() {
            match rustix::io::write(fd, buf) {
                Ok(0) => return Err(io::ErrorKind::WriteZero.into()),
                Ok(n) => buf = &buf[n..],
                Err(Errno::INTR) => {}
                Err(Errno::AGAIN) => wait(fd, PollFlags::OUT)?,
                Err(Errno::PIPE) => sigpipe(),
                Err(err) => return Err(err.into()),
            }
        }
        Ok(())
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
        // Go: exit(2) when the signal did not end the process.
        std::process::exit(2)
    }
}

#[cfg(not(unix))]
mod sys {
    use std::io::{self, Read, Write};

    pub fn read_stdin(buf: &mut [u8]) -> io::Result<usize> {
        io::stdin().read(buf)
    }

    pub fn write_stdout(buf: &[u8]) -> io::Result<()> {
        io::stdout().write_all(buf)
    }

    pub fn write_stderr(buf: &[u8]) -> io::Result<()> {
        io::stderr().write_all(buf)
    }

    pub fn flush_stdout() -> io::Result<()> {
        io::stdout().flush()
    }
}
