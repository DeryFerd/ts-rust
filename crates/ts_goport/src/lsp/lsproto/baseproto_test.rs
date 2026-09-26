//! Port of internal/lsp/lsproto/baseproto_test.go.
//!
//! PORT: Go `t.Parallel()` is dropped (cargo runs tests in parallel). The Go
//! file is the external test package `lsproto_test` and calls
//! `lsproto.NewBaseReader`; the port reaches the same items through the
//! lsproto prelude. A Go table test is one `#[test]` with a loop that names
//! the case in every assert message. Go `bytes.NewReader` is `io::Cursor`.

use crate::lsp::lsproto::prelude::*;

use std::io::{self, Cursor, Read, Write};
use std::sync::Mutex;

// Go: baseproto_test.go:12 TestBaseReader
#[test]
fn test_base_reader() {
    struct Test {
        name: &'static str,
        input: &'static [u8],
        value: Option<&'static [u8]>,
        err: &'static str,
    }

    let tests: Vec<Test> = vec![
        Test {
            name: "empty",
            input: b"Content-Length: 0\r\n\r\n",
            value: None,
            err: "jsonrpc: no content length",
        },
        Test {
            name: "early end",
            input: b"oops",
            value: None,
            err: "EOF",
        },
        Test {
            name: "negative length",
            input: b"Content-Length: -1\r\n\r\n",
            value: None,
            err: "jsonrpc: invalid content length: negative value -1",
        },
        Test {
            name: "invalid content",
            input: b"Content-Length: 1\r\n\r\n{",
            value: Some(b"{".as_slice()),
            err: "",
        },
        Test {
            name: "valid content",
            input: b"Content-Length: 2\r\n\r\n{}",
            value: Some(b"{}".as_slice()),
            err: "",
        },
        Test {
            name: "extra header values",
            input: b"Content-Length: 2\r\nExtra: 1\r\n\r\n{}",
            value: Some(b"{}".as_slice()),
            err: "",
        },
        Test {
            name: "too long content length",
            input: b"Content-Length: 100\r\n\r\n{}",
            value: None,
            err: "jsonrpc: read content: unexpected EOF",
        },
        Test {
            name: "missing content length",
            input: b"Content-Length: \r\n\r\n{}",
            value: None,
            err: "jsonrpc: invalid content length: parse error: strconv.ParseInt: parsing \"\": invalid syntax",
        },
        Test {
            name: "invalid header",
            input: b"Nope\r\n\r\n{}",
            value: None,
            err: "jsonrpc: invalid header: \"Nope\\r\\n\"",
        },
    ];

    for tt in tests {
        let mut r = new_base_reader(Box::new(Cursor::new(tt.input)));

        // PORT: Go `out, err := r.Read()` gives a nil `out` with an error.
        let (out, err) = match r.read() {
            Ok(out) => (Some(out), None),
            Err(err) => (None, Some(err)),
        };
        if !tt.err.is_empty() {
            // gotest.tools assert.Error: a non-nil error with exactly this text.
            match &err {
                None => panic!("{}: expected error {:?}, got nil", tt.name, tt.err),
                Some(err) => assert_eq!(err.error(), tt.err, "{}", tt.name),
            }
        }
        assert_eq!(out.as_deref(), tt.value, "{}", tt.name);
    }
}

// Go: baseproto_test.go:81 TestBaseReaderMultipleReads
#[test]
fn test_base_reader_multiple_reads() {
    let data: &'static [u8] = concat!(
        "Content-Length: 4\r\n\r\n1234",
        "Content-Length: 2\r\n\r\n{}",
    )
    .as_bytes();
    let mut r = new_base_reader(Box::new(Cursor::new(data)));

    let v1 = r.read();
    if let Err(err) = &v1 {
        panic!("expected no error, got {err}");
    }
    assert_eq!(v1.unwrap(), b"1234".to_vec());

    let v2 = r.read();
    if let Err(err) = &v2 {
        panic!("expected no error, got {err}");
    }
    assert_eq!(v2.unwrap(), b"{}".to_vec());

    match r.read() {
        Ok(_) => panic!("expected error \"EOF\", got nil"),
        Err(err) => assert_eq!(err.error(), "EOF"),
    }
}

// Go: baseproto_test.go:102 errorReader
// PORT: Go declares it and never uses it; kept for a literal port.
#[allow(dead_code)]
struct ErrorReader;

impl Read for ErrorReader {
    // Go: baseproto_test.go:104 (*errorReader).Read
    fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
        Err(io::Error::other("test error"))
    }
}

// PORT: Go writes into `&b` (a `*bytes.Buffer`) and reads `b.Bytes()`
// after the write. The base writer owns its `Box<dyn Write + Send>`, so the
// test shares the bytes with the writer.
#[derive(Clone, Default)]
struct SharedBuffer(Arc<Mutex<Vec<u8>>>);

impl SharedBuffer {
    // Go: bytes.Buffer.Bytes
    fn bytes(&self) -> Vec<u8> {
        self.0.lock().unwrap().clone()
    }
}

impl Write for SharedBuffer {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.lock().unwrap().extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

// Go: baseproto_test.go:108 TestBaseWriter
#[test]
fn test_base_writer() {
    struct Test {
        name: &'static str,
        value: &'static [u8],
        input: &'static [u8],
    }

    let tests: Vec<Test> = vec![
        Test {
            name: "empty",
            value: b"{}",
            input: b"Content-Length: 2\r\n\r\n{}",
        },
        Test {
            name: "bigger object",
            value: b"{\"key\":\"value\"}",
            input: b"Content-Length: 15\r\n\r\n{\"key\":\"value\"}",
        },
    ];

    for tt in tests {
        let b = SharedBuffer::default();
        let mut w = new_base_writer(Box::new(b.clone()));
        let err = w.write(tt.value);
        if let Err(err) = &err {
            panic!("{}: expected no error, got {err}", tt.name);
        }
        assert_eq!(b.bytes(), tt.input.to_vec(), "{}", tt.name);
    }
}

// Go: baseproto_test.go:139 TestBaseWriterWriteError
#[test]
fn test_base_writer_write_error() {
    let mut w = new_base_writer(Box::new(ErrorWriter));
    let err = w.write(b"{}");
    match err {
        Ok(()) => panic!("expected error \"test error\", got nil"),
        Err(err) => assert_eq!(err.error(), "test error"),
    }
}

// Go: baseproto_test.go:147 errorWriter
struct ErrorWriter;

impl Write for ErrorWriter {
    // Go: baseproto_test.go:149 (*errorWriter).Write
    fn write(&mut self, _: &[u8]) -> io::Result<usize> {
        Err(io::Error::other("test error"))
    }

    // PORT: Go `io.Writer` has no Flush; the base writer flushes its
    // buffer through `write`, which fails.
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
