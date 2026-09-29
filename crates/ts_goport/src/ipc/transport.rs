//! Port of internal/ipc/transport.go, with internal/ipc/transport_windows.go
//! as a `cfg(windows)` stub at the end (internal/api before tsgo#4712).
//!
//! PORT: Go `io.ReadWriteCloser` (what `Transport.Accept` returns) is the
//! trait `ReadWriteCloser`. Go hands the same value to the protocol reader,
//! the protocol writer and the caller that may close it, so the connection
//! is an `Arc<dyn ReadWriteCloser>` and its methods take `&self`.
//! `ConnReader` and `ConnWriter` are the `std::io` views that the protocols
//! read and write through. Go `net.Listener` is the trait `NetListener`.

use crate::ipc::prelude::*;

use crate::gostd::{GoError, errors};
use std::io::{Read, Write};
use std::sync::{Arc, Mutex, MutexGuard};

/// Go `io.ReadWriteCloser` for an API connection.
pub trait ReadWriteCloser: Send + Sync {
    fn read(&self, buf: &mut [u8]) -> std::io::Result<usize>;
    fn write(&self, buf: &[u8]) -> std::io::Result<usize>;
    fn flush(&self) -> std::io::Result<()>;
    fn close(&self) -> Result<(), GoError>;
}

/// `std::io::Read` over a shared connection (Go passes the connection itself
/// as the `io.Reader`).
pub struct ConnReader(pub Arc<dyn ReadWriteCloser>);

impl Read for ConnReader {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        self.0.read(buf)
    }
}

/// `std::io::Write` over a shared connection (Go passes the connection
/// itself as the `io.Writer`).
pub struct ConnWriter(pub Arc<dyn ReadWriteCloser>);

impl Write for ConnWriter {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0.write(buf)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.0.flush()
    }
}

/// Go `net.Listener`, the part `PipeTransport` uses.
pub trait NetListener: Send + Sync {
    fn accept(&self) -> Result<Arc<dyn ReadWriteCloser>, GoError>;
    fn close(&self) -> Result<(), GoError>;
    /// Go `Addr().String()`.
    fn addr(&self) -> String;
}

// Go: ipc/transport.go:9 Transport
// Transport is an interface for accepting connections from API clients.
pub trait Transport {
    // Accept waits for and returns the next connection.
    fn accept(&mut self) -> Result<Arc<dyn ReadWriteCloser>, GoError>;
    // Close stops the transport from accepting new connections.
    fn close(&mut self) -> Result<(), GoError>;
}

// Go: ipc/transport.go:17 PipeTransport
// PipeTransport accepts connections on a Unix domain socket or Windows named pipe.
pub struct PipeTransport {
    listener: Box<dyn NetListener>,
}

// Go: ipc/transport.go:23 NewPipeTransport
// NewPipeTransport creates a new transport listening on the given path.
// On Unix, this creates a Unix domain socket. On Windows, this creates a named pipe.
pub fn new_pipe_transport(path: &str) -> Result<PipeTransport, GoError> {
    let listener = new_pipe_listener(path)?;
    Ok(PipeTransport { listener })
}

// PORT: the Go methods are also inherent methods, so callers need not
// import `Transport`.
impl PipeTransport {
    // Go: ipc/transport.go:32 Accept
    // Accept implements Transport.
    pub fn accept(&self) -> Result<Arc<dyn ReadWriteCloser>, GoError> {
        self.listener.accept()
    }

    // Go: ipc/transport.go:37 Close
    // Close implements Transport.
    pub fn close(&self) -> Result<(), GoError> {
        self.listener.close()
    }

    // Go: ipc/transport.go:42 Path
    // Path returns the path of the pipe/socket.
    pub fn path(&self) -> String {
        self.listener.addr()
    }
}

impl Transport for PipeTransport {
    fn accept(&mut self) -> Result<Arc<dyn ReadWriteCloser>, GoError> {
        PipeTransport::accept(self)
    }

    fn close(&mut self) -> Result<(), GoError> {
        PipeTransport::close(self)
    }
}

// Go: ipc/transport.go:48 StdioTransport
// StdioTransport wraps stdin/stdout as a single connection transport.
// It only accepts one connection.
// PORT: Go `io.ReadCloser` / `io.WriteCloser` are boxed `Read` / `Write`
// values; a nil one is `None`. Accept moves them into the connection
// (`used` already stops a second Accept).
pub struct StdioTransport {
    stdin: Option<Box<dyn Read + Send>>,
    stdout: Option<Box<dyn Write + Send>>,
    used: bool,
}

// Go: ipc/transport.go:55 NewStdioTransport
// NewStdioTransport creates a transport using the given stdin/stdout.
pub fn new_stdio_transport(
    stdin: Option<Box<dyn Read + Send>>,
    stdout: Option<Box<dyn Write + Send>>,
) -> StdioTransport {
    StdioTransport {
        stdin,
        stdout,
        used: false,
    }
}

impl StdioTransport {
    // Go: ipc/transport.go:63 Accept
    // Accept implements Transport.
    pub fn accept(&mut self) -> Result<Arc<dyn ReadWriteCloser>, GoError> {
        if self.used {
            return Err(errors::EOF.clone());
        }
        self.used = true;
        Ok(Arc::new(StdioConn {
            stdin: Mutex::new(self.stdin.take()),
            stdout: Mutex::new(self.stdout.take()),
        }))
    }

    // Go: ipc/transport.go:77 Close
    // Close implements Transport.
    pub fn close(&mut self) -> Result<(), GoError> {
        Ok(())
    }
}

impl Transport for StdioTransport {
    fn accept(&mut self) -> Result<Arc<dyn ReadWriteCloser>, GoError> {
        StdioTransport::accept(self)
    }

    fn close(&mut self) -> Result<(), GoError> {
        StdioTransport::close(self)
    }
}

// Go: ipc/transport.go:81 stdioConn
// PORT: Go embeds the reader and writer; here each sits behind a mutex so
// the connection can be shared (`ReadWriteCloser` takes `&self`).
struct StdioConn {
    stdin: Mutex<Option<Box<dyn Read + Send>>>,
    stdout: Mutex<Option<Box<dyn Write + Send>>>,
}

fn lock<T>(m: &Mutex<T>) -> MutexGuard<'_, T> {
    m.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
}

// Go reads or writes through a nil io.Reader / io.Writer and panics.
const NIL_DEREF: &str = "runtime error: invalid memory address or nil pointer dereference";

impl ReadWriteCloser for StdioConn {
    fn read(&self, buf: &mut [u8]) -> std::io::Result<usize> {
        lock(&self.stdin).as_mut().expect(NIL_DEREF).read(buf)
    }

    fn write(&self, buf: &[u8]) -> std::io::Result<usize> {
        lock(&self.stdout).as_mut().expect(NIL_DEREF).write(buf)
    }

    fn flush(&self) -> std::io::Result<()> {
        lock(&self.stdout).as_mut().expect(NIL_DEREF).flush()
    }

    // Go: ipc/transport.go:88 Close
    // PORT: Go closes both files. The port drops both handles; dropping
    // `std::io::Stdin` / `Stdout` leaves the process streams open, and a
    // drop reports no error.
    fn close(&self) -> Result<(), GoError> {
        let stdin = lock(&self.stdin).take();
        let stdout = lock(&self.stdout).take();
        drop(stdin);
        drop(stdout);
        Ok(())
    }
}

#[cfg(unix)]
use crate::ipc::transport_unix::new_pipe_listener;

// ---------------------------------------------------------------------------
// transport_windows.go (//go:build windows)
// ---------------------------------------------------------------------------

// Go: ipc/transport_windows.go:12 newPipeListener
// newPipeListener creates a Windows named pipe listener.
// PORT: Go uses `winio.ListenPipe`, which is not ported (Windows only). The
// port fails the way `ListenPipe` fails when named pipes are unavailable:
// it returns an error, and `runAPI` prints it and exits 1. The text is Go
// `errors.ErrUnsupported`, wrapped like a Go `net.OpError`.
#[cfg(windows)]
pub fn new_pipe_listener(path: &str) -> Result<Box<dyn NetListener>, GoError> {
    Err(errors::new(format!(
        "listen pipe {path}: unsupported operation"
    )))
}

// Go: ipc/transport_windows.go:17 GeneratePipePath
// GeneratePipePath returns a platform-appropriate pipe path for the given name.
#[cfg(windows)]
pub fn generate_pipe_path(name: &str) -> String {
    format!(r"\\.\pipe\{name}")
}
