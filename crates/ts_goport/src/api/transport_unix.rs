//! Port of internal/api/transport_unix.go (`//go:build !windows`).
//!
//! PORT: Go `net.Listen("unix", path)` and `net.UnixConn` are
//! `std::os::unix::net`. Error texts are the `std::io::Error` texts, not the
//! Go `*net.OpError` texts.

use crate::api::prelude::*;

use crate::api::transport::{NetListener, ReadWriteCloser};
use crate::gostd::{GoError, errors};
use std::net::Shutdown;
use std::os::unix::net::{UnixListener, UnixStream};
use std::sync::{Arc, Mutex};

// Go: transport_unix.go:11 newPipeListener
// newPipeListener creates a Unix domain socket listener.
pub fn new_pipe_listener(path: &str) -> Result<Box<dyn NetListener>, GoError> {
    // Remove any existing socket file
    // PORT: Go `os.Remove` unlinks a file or removes an empty directory.
    if std::fs::remove_file(path).is_err() {
        let _ = std::fs::remove_dir(path);
    }
    match UnixListener::bind(path) {
        Ok(listener) => Ok(Box::new(UnixPipeListener {
            listener: Mutex::new(Some(listener)),
            path: path.to_string(),
        })),
        Err(err) => Err(errors::new(format!("listen unix {path}: {err}"))),
    }
}

// Go: transport_unix.go:19 GeneratePipePath
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
        match listener.accept() {
            Ok((stream, _)) => Ok(Arc::new(UnixConn { stream })),
            Err(err) => Err(errors::new(format!("accept unix {}: {err}", self.path))),
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
    fn close(&self) -> Result<(), GoError> {
        self.stream
            .shutdown(Shutdown::Both)
            .map_err(|err| errors::new(format!("close unix: {err}")))
    }
}
