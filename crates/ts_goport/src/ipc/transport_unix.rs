//! Port of internal/ipc/transport_unix.go (`//go:build !windows`;
//! internal/api/transport_unix.go before tsgo#4712).
//!
//! PORT: Go `net.Listen("unix", path)` and `net.UnixConn` are
//! `std::os::unix::net`. Errors are Go's `*net.OpError` texts ("op unix
//! addr: syscall: errno text").

use crate::ipc::prelude::*;

use crate::fswatch::syscall::io_error_text;
use crate::gostd::{GoError, errors};
use crate::ipc::transport::{NetListener, ReadWriteCloser};
use std::net::Shutdown;
use std::os::unix::net::{UnixListener, UnixStream};
use std::sync::{Arc, Mutex};

// Go: ipc/transport_unix.go:12 newPipeListener
// newPipeListener creates a Unix domain socket listener.
pub fn new_pipe_listener(path: &str) -> Result<Box<dyn NetListener>, GoError> {
    // Remove any existing socket file
    // PORT: Go `os.Remove` unlinks a file or removes an empty directory.
    if std::fs::remove_file(path).is_err() {
        let _ = std::fs::remove_dir(path);
    }
    match listen_unix(path) {
        Ok(listener) => Ok(Box::new(UnixPipeListener {
            listener: Mutex::new(Some(listener)),
            path: path.to_string(),
        })),
        // Go: net/sock_posix.go listenStream, `os.NewSyscallError("bind",
        // err)`, in `&OpError{Op: "listen", Net: "unix", Addr: laddr}`.
        // PORT: std checks the name length before the socket call and
        // fails with no errno, where Go's `syscall.Bind` gives EINVAL. A
        // `socket` or `listen` failure also prints "bind" here.
        Err(err) => {
            let text = match err.raw_os_error() {
                None if err.kind() == std::io::ErrorKind::InvalidInput => {
                    "invalid argument".to_string()
                }
                _ => io_error_text(&err),
            };
            Err(errors::new(format!("listen unix {path}: bind: {text}")))
        }
    }
}

/// Go `net.Listen("unix", path)`. On Linux a name that starts with '@' is
/// an abstract name, with no file (go1.26.4 syscall/syscall_linux.go
/// `SockaddrUnix.sockaddr`: the '@' becomes a NUL, and the address has no
/// trailing NUL). `from_abstract_name` makes the same address, and fails
/// with no errno where Go's name is longer than 108 bytes (EINVAL).
fn listen_unix(path: &str) -> std::io::Result<UnixListener> {
    #[cfg(target_os = "linux")]
    if let Some(name) = path.strip_prefix('@') {
        use std::os::linux::net::SocketAddrExt;
        let addr = std::os::unix::net::SocketAddr::from_abstract_name(name)?;
        return UnixListener::bind_addr(&addr);
    }
    UnixListener::bind(path)
}

// Go: ipc/transport_unix.go:19 GeneratePipePath
// GeneratePipePath returns a platform-appropriate pipe path for the given name.
pub fn generate_pipe_path(name: &str) -> String {
    path_join(&os_temp_dir(), name)
}

// Go `os.TempDir` on Unix: $TMPDIR, or "/tmp" when it is empty.
fn os_temp_dir() -> String {
    match std::env::var("TMPDIR") {
        Ok(dir) if !dir.is_empty() => dir,
        _ => "/tmp".to_string(),
    }
}

// Go `path.Join(dir, name)`: the non-empty elements joined by "/", then
// cleaned.
fn path_join(dir: &str, name: &str) -> String {
    let mut buf = String::new();
    for e in [dir, name] {
        if !buf.is_empty() || !e.is_empty() {
            if !buf.is_empty() {
                buf.push('/');
            }
            buf.push_str(e);
        }
    }
    if buf.is_empty() {
        return buf;
    }
    crate::frontend::vfs::filepath_clean(&buf)
}

// Go: internal/poll/sock_cloexec.go (accept4) and sys_cloexec.go (accept),
// the `errcall` of an accept error.
#[cfg(not(target_vendor = "apple"))]
const ACCEPT_CALL: &str = "accept4";
#[cfg(target_vendor = "apple")]
const ACCEPT_CALL: &str = "accept";

/// Go `*net.UnixListener` from `net.Listen("unix", path)`.
/// PORT: the listener sits in a mutex so `close` can drop it through `&self`.
struct UnixPipeListener {
    listener: Mutex<Option<UnixListener>>,
    path: String,
}

impl NetListener for UnixPipeListener {
    // Go net.UnixListener.Accept
    fn accept(&self) -> Result<Arc<dyn ReadWriteCloser>, GoError> {
        let guard = self
            .listener
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let Some(listener) = guard.as_ref() else {
            return Err(errors::new(format!(
                "accept unix {}: use of closed network connection",
                self.path
            )));
        };
        // Go: net/fd_unix.go accept, `wrapSyscallError(errcall, err)`: std
        // and Go call accept4 on Linux and the BSDs, accept on darwin.
        match listener.accept() {
            Ok((stream, _)) => Ok(Arc::new(UnixConn { stream })),
            Err(err) => Err(errors::new(format!(
                "accept unix {}: {ACCEPT_CALL}: {}",
                self.path,
                io_error_text(&err)
            ))),
        }
    }

    // Go net.UnixListener.Close: closes the socket and unlinks the socket
    // file (listeners made by `net.Listen` unlink on close; abstract names
    // starting with '@' have no file).
    fn close(&self) -> Result<(), GoError> {
        let listener = self
            .listener
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take();
        let Some(listener) = listener else {
            return Err(errors::new(format!(
                "close unix {}: use of closed network connection",
                self.path
            )));
        };
        drop(listener);
        if !self.path.starts_with('@') {
            let _ = std::fs::remove_file(&self.path);
        }
        Ok(())
    }

    // Go `l.Addr().String()`: the socket name.
    fn addr(&self) -> String {
        self.path.clone()
    }
}

/// Go `*net.UnixConn`.
struct UnixConn {
    stream: UnixStream,
}

impl ReadWriteCloser for UnixConn {
    fn read(&self, buf: &mut [u8]) -> std::io::Result<usize> {
        std::io::Read::read(&mut &self.stream, buf)
    }

    fn write(&self, buf: &[u8]) -> std::io::Result<usize> {
        std::io::Write::write(&mut &self.stream, buf)
    }

    fn flush(&self) -> std::io::Result<()> {
        std::io::Write::flush(&mut &self.stream)
    }

    // PORT: Go closes the file descriptor. The stream is shared, so the port
    // shuts both directions down; the descriptor closes with the last owner.
    // macOS reports ENOTCONN when the peer has closed, where Go's close
    // succeeds, so that is not an error. Go's error is "close unix
    // <laddr>-><raddr>: <err>". The port's text has no addresses; callers
    // ignore it.
    fn close(&self) -> Result<(), GoError> {
        match self.stream.shutdown(Shutdown::Both) {
            Err(err) if err.kind() != std::io::ErrorKind::NotConnected => {
                Err(errors::new(format!("close unix: {}", io_error_text(&err))))
            }
            _ => Ok(()),
        }
    }
}
