//! Port of internal/jsonrpc/baseproto.go.
//!
//! Base protocol for JSON-RPC with Content-Length headers (as used by LSP).
//! https://microsoft.github.io/language-server-protocol/specifications/base/0.9/specification/
//!
//! PORT: Go wraps an `io.Reader` / `io.Writer` in `bufio`. The Rust reader
//! takes a `BufRead` (the caller supplies the buffer); the writer wraps its
//! `Write` in a 4096-byte `BufWriter` (Go `bufio.NewWriter` size). An
//! `std::io::Error` becomes a `GoError` with the same text. Go `bufio.Writer`
//! keeps the first write error for later writes; `BufWriter` retries.

use crate::jsonrpc::prelude::*;

use crate::gostd::{GoError, errors, strconv};
use std::io::{BufRead, BufWriter, Read, Write};
use std::sync::LazyLock;

// Go: baseproto.go:16
pub static ERR_INVALID_HEADER: LazyLock<GoError> =
    LazyLock::new(|| errors::new("jsonrpc: invalid header"));
pub static ERR_INVALID_CONTENT_LENGTH: LazyLock<GoError> =
    LazyLock::new(|| errors::new("jsonrpc: invalid content length"));
pub static ERR_NO_CONTENT_LENGTH: LazyLock<GoError> =
    LazyLock::new(|| errors::new("jsonrpc: no content length"));

// Go: baseproto.go:22 Reader
/// Reader reads JSON-RPC messages with Content-Length framing.
pub struct Reader {
    r: Box<dyn BufRead + Send>,
}

// Go: baseproto.go:27 NewReader
// NewReader creates a new Reader.
pub fn new_reader(r: Box<dyn BufRead + Send>) -> Reader {
    Reader { r }
}

impl Reader {
    // Go: baseproto.go:34 Read
    // Read reads the next message payload.
    pub fn read(&mut self) -> Result<Vec<u8>, GoError> {
        let mut content_length: i64 = 0;

        loop {
            // Go bufio.Reader.ReadBytes('\n'): the line with its delimiter,
            // or io.EOF when the input ends first.
            let mut line = Vec::new();
            if let Err(err) = self.r.read_until(b'\n', &mut line) {
                let err = errors::new(err.to_string());
                return Err(errors::errorf(
                    format!("jsonrpc: read header: {}", err.error()),
                    vec![err],
                ));
            }
            if line.last() != Some(&b'\n') {
                return Err(errors::EOF.clone());
            }

            if line == b"\r\n" {
                break;
            }

            let Some(colon) = line.iter().position(|&c| c == b':') else {
                // PORT: `%q` of invalid UTF-8 bytes prints U+FFFD, not `\x..`.
                return Err(errors::errorf(
                    format!(
                        "{}: {}",
                        ERR_INVALID_HEADER.error(),
                        strconv::quote(&String::from_utf8_lossy(&line))
                    ),
                    vec![ERR_INVALID_HEADER.clone()],
                ));
            };
            let (key, value) = (&line[..colon], &line[colon + 1..]);

            if key == b"Content-Length" {
                // Go bytes.TrimSpace (Unicode White_Space at both ends).
                // PORT: invalid UTF-8 is trimmed as U+FFFD (not a space),
                // which is where Go's TrimFunc stops too.
                let value = String::from_utf8_lossy(value);
                match parse_int_10_64(value.trim()) {
                    Ok(v) => content_length = v,
                    Err(err) => {
                        let err = errors::new(err);
                        return Err(errors::errorf(
                            format!(
                                "{}: parse error: {}",
                                ERR_INVALID_CONTENT_LENGTH.error(),
                                err.error()
                            ),
                            vec![ERR_INVALID_CONTENT_LENGTH.clone(), err],
                        ));
                    }
                }
                if content_length < 0 {
                    return Err(errors::errorf(
                        format!(
                            "{}: negative value {}",
                            ERR_INVALID_CONTENT_LENGTH.error(),
                            content_length
                        ),
                        vec![ERR_INVALID_CONTENT_LENGTH.clone()],
                    ));
                }
            }
        }

        if content_length <= 0 {
            return Err(ERR_NO_CONTENT_LENGTH.clone());
        }

        let mut data = vec![0u8; content_length as usize];
        if let Err(err) = read_full(&mut self.r, &mut data) {
            return Err(errors::errorf(
                format!("jsonrpc: read content: {}", err.error()),
                vec![err],
            ));
        }

        Ok(data)
    }
}

// Go: io/io.go:353 ReadFull (ReadAtLeast with min = len(buf))
// PORT: `io.ErrUnexpectedEOF` is not a gostd sentinel; it is a plain error
// with the Go text.
fn read_full<R: Read + ?Sized>(r: &mut R, buf: &mut [u8]) -> Result<(), GoError> {
    let mut n = 0;
    while n < buf.len() {
        match r.read(&mut buf[n..]) {
            Ok(0) => break,
            Ok(nn) => n += nn,
            Err(err) if err.kind() == std::io::ErrorKind::Interrupted => {}
            Err(err) => return Err(errors::new(err.to_string())),
        }
    }
    if n >= buf.len() {
        return Ok(());
    }
    if n > 0 {
        return Err(errors::new("unexpected EOF"));
    }
    Err(errors::EOF.clone())
}

// Go: strconv/number.go:137 ParseInt(s, 10, 64) with
// internal/strconv/atoi.go:47 ParseUint and :171 ParseInt.
// Returns the `*strconv.NumError` text on error.
// PORT: only base 10 and 64 bits, the case baseproto uses.
fn parse_int_10_64(s: &str) -> Result<i64, String> {
    let num_error = |err: &str| format!("strconv.ParseInt: parsing {}: {}", strconv::quote(s), err);
    const ERR_SYNTAX: &str = "invalid syntax";
    const ERR_RANGE: &str = "value out of range";

    if s.is_empty() {
        return Err(num_error(ERR_SYNTAX));
    }

    // Pick off leading sign.
    let mut digits = s.as_bytes();
    let mut neg = false;
    match digits[0] {
        b'+' => digits = &digits[1..],
        b'-' => {
            digits = &digits[1..];
            neg = true;
        }
        _ => {}
    }

    // Convert unsigned and check range (ParseUint, base 10, 64 bits). On
    // ErrRange ParseUint returns maxVal and ParseInt's cutoff check below
    // reports the range error.
    if digits.is_empty() {
        return Err(num_error(ERR_SYNTAX));
    }
    // Cutoff is the smallest number such that cutoff*base > maxUint64.
    const CUTOFF: u64 = u64::MAX / 10 + 1;
    const MAX_VAL: u64 = u64::MAX;
    let mut un: u64 = 0;
    for &c in digits {
        let d = match c {
            b'0'..=b'9' => c - b'0',
            // Letters are digits >= 10, which base 10 rejects like any
            // other byte.
            _ => return Err(num_error(ERR_SYNTAX)),
        };
        if un >= CUTOFF {
            // n*base overflows
            un = MAX_VAL;
            break;
        }
        un *= 10;
        let n1 = un.wrapping_add(u64::from(d));
        // Go also checks `n1 > maxVal`, which cannot hold for 64 bits.
        if n1 < un {
            // n+d overflows
            un = MAX_VAL;
            break;
        }
        un = n1;
    }

    let cutoff: u64 = 1 << 63;
    if !neg && un >= cutoff {
        return Err(num_error(ERR_RANGE));
    }
    if neg && un > cutoff {
        return Err(num_error(ERR_RANGE));
    }
    let mut n = un as i64;
    if neg {
        n = n.wrapping_neg();
    }
    Ok(n)
}

// Go: baseproto.go:79 Writer
/// Writer writes JSON-RPC messages with Content-Length framing.
pub struct Writer {
    w: BufWriter<Box<dyn Write + Send>>,
}

// Go: baseproto.go:84 NewWriter
// NewWriter creates a new Writer.
pub fn new_writer(w: Box<dyn Write + Send>) -> Writer {
    Writer {
        w: BufWriter::with_capacity(4096, w),
    }
}

impl Writer {
    // Go: baseproto.go:91 Write
    // Write writes a message payload with Content-Length header.
    pub fn write(&mut self, data: &[u8]) -> Result<(), GoError> {
        if let Err(err) = write!(self.w, "Content-Length: {}\r\n\r\n", data.len()) {
            return Err(errors::new(err.to_string()));
        }
        if let Err(err) = self.w.write_all(data) {
            return Err(errors::new(err.to_string()));
        }
        self.w.flush().map_err(|err| errors::new(err.to_string()))
    }
}
