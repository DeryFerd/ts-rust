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
//! error, which `fmt.Fprint` ignores. Rust ignores SIGPIPE, so a write here
//! gets EPIPE and raises the signal as Go does. A write that writes 0 bytes
//! gives `WriteZero` (Go `io.ErrUnexpectedEOF`). Go does not buffer these
//! files; `LineStdout` keeps std's line buffer (see there). On Windows these
//! are the std handles, as before.

use std::io;

/// Go `os.Stdin`. Wrap it in a `BufReader` where Go wraps it in a
/// `bufio.Reader`.
pub struct Stdin;

/// Go `os.Stdout`, not buffered. The LSP and API servers use it under the
/// `bufio.Writer` of their base protocol.
pub struct Stdout;

/// Go `os.Stdout` through std's line-buffered stdout, with the error
/// handling of `Stdout`. The tsc system writer uses it.
/// PORT: Go writes each `fmt.Fprint` at once, and a pretty diagnostic is
/// many short pieces per line: in a run with 5,000 errors Go makes 37 writes
/// per diagnostic, this 8 (R149 5, through `write_all`, whose error does not
/// say how much it wrote). Other port code (the trace output, the watch
/// manager) writes whole lines to std's stdout, so both keep their order.
/// Text that has no newline yet at exit goes out in std's flush at exit,
/// which ignores errors; tsc output ends with a newline.
pub struct LineStdout;

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

impl io::Write for LineStdout {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        sys::write_line_stdout(buf)?;
        Ok(buf.len())
    }

    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        sys::write_line_stdout(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        sys::flush_line_stdout()
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
    use std::io::{self, Write};

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

    // A failed `write` of std's line writer consumed nothing of `buf`, and
    // a failed flush keeps the bytes it did not write, so both try again.
    pub fn write_line_stdout(mut buf: &[u8]) -> io::Result<()> {
        let mut out = io::stdout().lock();
        while !buf.is_empty() {
            match out.write(buf) {
                Ok(0) => return Err(io::ErrorKind::WriteZero.into()),
                Ok(n) => buf = &buf[n..],
                Err(err) => after_write_error(rustix::stdio::stdout(), err)?,
            }
        }
        Ok(())
    }

    pub fn flush_line_stdout() -> io::Result<()> {
        let mut out = io::stdout().lock();
        while let Err(err) = out.flush() {
            after_write_error(rustix::stdio::stdout(), err)?;
        }
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

    pub fn flush_stdout() -> io::Result<()> {
        io::stdout().flush()
    }

    pub fn write_line_stdout(buf: &[u8]) -> io::Result<()> {
        io::stdout().write_all(buf)
    }

    pub fn flush_line_stdout() -> io::Result<()> {
        io::stdout().flush()
    }

    pub fn write_stderr(buf: &[u8]) -> io::Result<()> {
        io::stderr().write_all(buf)
    }
}
