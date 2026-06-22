//! JSON-RPC 2.0 messages and synchronous LSP `Content-Length` transport.

use std::{error::Error, fmt, io};

use serde::{Deserialize, Deserializer, Serialize, Serializer, de};
use serde_json::Value;

/// The required JSON-RPC protocol version.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct JsonRpcVersion;

impl Serialize for JsonRpcVersion {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str("2.0")
    }
}

impl<'de> Deserialize<'de> for JsonRpcVersion {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = String::deserialize(deserializer)?;
        if value == "2.0" {
            Ok(Self)
        } else {
            Err(de::Error::custom("invalid JSON-RPC version"))
        }
    }
}

/// A JSON-RPC request/response identifier.
#[derive(Clone, Debug, Eq, Hash, PartialEq, Deserialize, Serialize)]
#[serde(untagged)]
pub enum Id {
    Integer(i64),
    String(String),
}

impl fmt::Display for Id {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Integer(value) => value.fmt(formatter),
            Self::String(value) => value.fmt(formatter),
        }
    }
}

impl From<i64> for Id {
    fn from(value: i64) -> Self {
        Self::Integer(value)
    }
}

impl From<String> for Id {
    fn from(value: String) -> Self {
        Self::String(value)
    }
}

impl From<&str> for Id {
    fn from(value: &str) -> Self {
        Self::String(value.to_owned())
    }
}

/// A typed JSON-RPC request.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct Request<P = Value> {
    pub jsonrpc: JsonRpcVersion,
    pub id: Id,
    pub method: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub params: Option<P>,
}

impl<P> Request<P> {
    #[must_use]
    pub fn new(id: impl Into<Id>, method: impl Into<String>, params: Option<P>) -> Self {
        Self {
            jsonrpc: JsonRpcVersion,
            id: id.into(),
            method: method.into(),
            params,
        }
    }
}

/// A typed JSON-RPC notification.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct Notification<P = Value> {
    pub jsonrpc: JsonRpcVersion,
    pub method: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub params: Option<P>,
}

impl<P> Notification<P> {
    #[must_use]
    pub fn new(method: impl Into<String>, params: Option<P>) -> Self {
        Self {
            jsonrpc: JsonRpcVersion,
            method: method.into(),
            params,
        }
    }
}

/// A standard JSON-RPC error object.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct ResponseError {
    pub code: i32,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub data: Option<Value>,
}

impl ResponseError {
    #[must_use]
    pub fn new(code: i32, message: impl Into<String>, data: Option<Value>) -> Self {
        Self {
            code,
            message: message.into(),
            data,
        }
    }
}

impl fmt::Display for ResponseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "[{}]: {}", self.code, self.message)?;
        if let Some(data) = &self.data {
            write!(formatter, "\n{data}")?;
        }
        Ok(())
    }
}

impl Error for ResponseError {}

pub const CODE_PARSE_ERROR: i32 = -32_700;
pub const CODE_INVALID_REQUEST: i32 = -32_600;
pub const CODE_METHOD_NOT_FOUND: i32 = -32_601;
pub const CODE_INVALID_PARAMS: i32 = -32_602;
pub const CODE_INTERNAL_ERROR: i32 = -32_603;

/// The mutually exclusive result or error member of a response.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
#[serde(untagged)]
pub enum ResponsePayload<R = Value> {
    Success { result: R },
    Error { error: ResponseError },
}

/// A typed JSON-RPC response. `id` is null for errors where the request ID
/// could not be recovered.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct Response<R = Value> {
    pub jsonrpc: JsonRpcVersion,
    pub id: Option<Id>,
    #[serde(flatten)]
    pub payload: ResponsePayload<R>,
}

impl<R> Response<R> {
    #[must_use]
    pub fn success(id: impl Into<Id>, result: R) -> Self {
        Self {
            jsonrpc: JsonRpcVersion,
            id: Some(id.into()),
            payload: ResponsePayload::Success { result },
        }
    }

    #[must_use]
    pub const fn failure(id: Option<Id>, error: ResponseError) -> Self {
        Self {
            jsonrpc: JsonRpcVersion,
            id,
            payload: ResponsePayload::Error { error },
        }
    }
}

/// Classification of a raw message.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MessageKind {
    Notification,
    Request,
    Response,
    Invalid,
}

/// A generic message retaining params/result as JSON values.
#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct Message {
    pub jsonrpc: JsonRpcVersion,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub id: Option<Id>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub method: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub params: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub result: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub error: Option<ResponseError>,
}

impl Message {
    #[must_use]
    pub fn kind(&self) -> MessageKind {
        match (self.id.is_some(), self.method.is_some()) {
            (false, true) => MessageKind::Notification,
            (true, true) => MessageKind::Request,
            (true, false) => MessageKind::Response,
            (false, false) => MessageKind::Invalid,
        }
    }
}

/// Synchronous transport/framing failure.
#[derive(Debug)]
pub enum ProtocolError {
    Io(io::Error),
    InvalidHeader(String),
    InvalidContentLength(String),
    MissingContentLength,
    InvalidPayload(serde_json::Error),
}

impl fmt::Display for ProtocolError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(error) => write!(formatter, "jsonrpc: {error}"),
            Self::InvalidHeader(header) => write!(formatter, "jsonrpc: invalid header: {header:?}"),
            Self::InvalidContentLength(value) => {
                write!(formatter, "jsonrpc: invalid content length: {value}")
            }
            Self::MissingContentLength => formatter.write_str("jsonrpc: no content length"),
            Self::InvalidPayload(error) => write!(formatter, "jsonrpc: invalid payload: {error}"),
        }
    }
}

impl Error for ProtocolError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            Self::InvalidPayload(error) => Some(error),
            _ => None,
        }
    }
}

impl From<io::Error> for ProtocolError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

/// Reads LSP-style `Content-Length` framed messages.
pub struct FramedReader<R> {
    reader: io::BufReader<R>,
}

impl<R: io::Read> FramedReader<R> {
    #[must_use]
    pub fn new(reader: R) -> Self {
        Self {
            reader: io::BufReader::new(reader),
        }
    }

    /// Reads the next payload. A clean EOF before a header returns `None`.
    ///
    /// # Errors
    ///
    /// Returns a framing or I/O error for malformed/truncated input.
    pub fn read_payload(&mut self) -> Result<Option<Vec<u8>>, ProtocolError> {
        use io::{BufRead, Read};

        let mut content_length = None;
        loop {
            let mut line = Vec::new();
            let bytes_read = self.reader.read_until(b'\n', &mut line)?;
            if bytes_read == 0 {
                return if content_length.is_none() {
                    Ok(None)
                } else {
                    Err(ProtocolError::Io(io::Error::new(
                        io::ErrorKind::UnexpectedEof,
                        "unexpected EOF while reading headers",
                    )))
                };
            }
            if !line.ends_with(b"\n") {
                return Err(ProtocolError::Io(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "unexpected EOF while reading headers",
                )));
            }
            if line == b"\r\n" {
                break;
            }
            let Some(colon) = line.iter().position(|byte| *byte == b':') else {
                return Err(ProtocolError::InvalidHeader(
                    String::from_utf8_lossy(&line).into_owned(),
                ));
            };
            let key = &line[..colon];
            if key == b"Content-Length" {
                let value = String::from_utf8_lossy(&line[colon + 1..]);
                let value = value.trim();
                let parsed = value.parse::<i64>().map_err(|error| {
                    ProtocolError::InvalidContentLength(format!("parse error: {error}"))
                })?;
                if parsed < 0 {
                    return Err(ProtocolError::InvalidContentLength(format!(
                        "negative value {parsed}"
                    )));
                }
                content_length = Some(parsed);
            }
        }
        let Some(content_length) = content_length.filter(|length| *length > 0) else {
            return Err(ProtocolError::MissingContentLength);
        };
        let length = usize::try_from(content_length).map_err(|_| {
            ProtocolError::InvalidContentLength("value exceeds platform limits".to_owned())
        })?;
        let mut payload = vec![0; length];
        self.reader.read_exact(&mut payload).map_err(|error| {
            ProtocolError::Io(io::Error::new(
                error.kind(),
                format!("read content: {error}"),
            ))
        })?;
        Ok(Some(payload))
    }

    /// Reads and deserializes the next framed JSON message.
    ///
    /// # Errors
    ///
    /// Returns a framing, I/O, or JSON deserialization error.
    pub fn read_message<T: for<'de> Deserialize<'de>>(
        &mut self,
    ) -> Result<Option<T>, ProtocolError> {
        self.read_payload()?
            .map(|payload| serde_json::from_slice(&payload).map_err(ProtocolError::InvalidPayload))
            .transpose()
    }
}

/// Writes LSP-style `Content-Length` framed messages.
pub struct FramedWriter<W: io::Write> {
    writer: io::BufWriter<W>,
}

impl<W: io::Write> FramedWriter<W> {
    #[must_use]
    pub fn new(writer: W) -> Self {
        Self {
            writer: io::BufWriter::new(writer),
        }
    }

    /// Writes and flushes one payload frame.
    ///
    /// # Errors
    ///
    /// Returns an I/O error if the frame cannot be written or flushed.
    pub fn write_payload(&mut self, payload: &[u8]) -> Result<(), ProtocolError> {
        use io::Write;

        write!(self.writer, "Content-Length: {}\r\n\r\n", payload.len())?;
        self.writer.write_all(payload)?;
        self.writer.flush()?;
        Ok(())
    }

    /// Serializes, writes, and flushes one JSON frame.
    ///
    /// # Errors
    ///
    /// Returns a JSON serialization or I/O error.
    pub fn write_message<T: Serialize>(&mut self, message: &T) -> Result<(), ProtocolError> {
        let payload = serde_json::to_vec(message).map_err(ProtocolError::InvalidPayload)?;
        self.write_payload(&payload)
    }

    /// Flushes pending bytes and returns the underlying writer.
    ///
    /// # Errors
    ///
    /// Returns an I/O error if buffered bytes cannot be flushed.
    pub fn into_inner(self) -> Result<W, ProtocolError> {
        self.writer
            .into_inner()
            .map_err(|error| ProtocolError::Io(error.into_error()))
    }
}

#[cfg(test)]
mod tests {
    use std::io::{Cursor, Read};

    use serde_json::json;

    use super::*;

    struct PartialReader<R> {
        inner: R,
        chunk: usize,
    }

    impl<R: Read> Read for PartialReader<R> {
        fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
            let length = buffer.len().min(self.chunk);
            self.inner.read(&mut buffer[..length])
        }
    }

    #[test]
    fn serializes_ids_requests_notifications_and_responses() {
        let request = Request::new(
            Id::String(String::new()),
            "workspace/test",
            Some(json!({"x": 1})),
        );
        assert_eq!(
            serde_json::to_string(&request).unwrap(),
            r#"{"jsonrpc":"2.0","id":"","method":"workspace/test","params":{"x":1}}"#
        );
        let notification = Notification::new("initialized", None::<Value>);
        assert_eq!(
            serde_json::to_string(&notification).unwrap(),
            r#"{"jsonrpc":"2.0","method":"initialized"}"#
        );
        let success = Response::success(7_i64, json!({"ok": true}));
        assert_eq!(
            serde_json::to_string(&success).unwrap(),
            r#"{"jsonrpc":"2.0","id":7,"result":{"ok":true}}"#
        );
        let failure = Response::<Value>::failure(
            None,
            ResponseError::new(CODE_PARSE_ERROR, "parse error", Some(json!({"line": 1}))),
        );
        assert_eq!(
            serde_json::to_string(&failure).unwrap(),
            r#"{"jsonrpc":"2.0","id":null,"error":{"code":-32700,"message":"parse error","data":{"line":1}}}"#
        );
        assert!(
            serde_json::from_str::<Request>(r#"{"jsonrpc":"1.0","id":1,"method":"x"}"#).is_err()
        );
        assert!(serde_json::from_str::<Id>("1.5").is_err());
    }

    #[test]
    fn classifies_raw_messages() {
        let cases = [
            (
                r#"{"jsonrpc":"2.0","method":"event"}"#,
                MessageKind::Notification,
            ),
            (
                r#"{"jsonrpc":"2.0","id":"a","method":"call"}"#,
                MessageKind::Request,
            ),
            (
                r#"{"jsonrpc":"2.0","id":1,"result":null}"#,
                MessageKind::Response,
            ),
            (
                r#"{"jsonrpc":"2.0","id":1,"error":{"code":-32603,"message":"bad"}}"#,
                MessageKind::Response,
            ),
        ];
        for (text, kind) in cases {
            assert_eq!(serde_json::from_str::<Message>(text).unwrap().kind(), kind);
        }
    }

    #[test]
    fn reads_partial_and_multiple_frames() {
        let input = b"Content-Length: 4\r\nExtra: 1\r\n\r\n1234Content-Length: 2\r\n\r\n{}";
        let reader = PartialReader {
            inner: Cursor::new(input),
            chunk: 1,
        };
        let mut reader = FramedReader::new(reader);
        assert_eq!(reader.read_payload().unwrap().unwrap(), b"1234");
        assert_eq!(reader.read_payload().unwrap().unwrap(), b"{}");
        assert!(reader.read_payload().unwrap().is_none());
    }

    #[test]
    fn rejects_malformed_headers_payloads_and_truncation() {
        let cases = [
            (b"Content-Length: 0\r\n\r\n".as_slice(), "no content length"),
            (b"Content-Length: -1\r\n\r\n", "negative value -1"),
            (b"Content-Length: nope\r\n\r\n", "parse error"),
            (b"Nope\r\n\r\n", "invalid header"),
            (b"Content-Length: 5\r\n\r\n{}", "read content"),
        ];
        for (input, message) in cases {
            let error = FramedReader::new(Cursor::new(input))
                .read_payload()
                .unwrap_err();
            assert!(error.to_string().contains(message), "{error}");
        }

        let mut reader = FramedReader::new(Cursor::new(b"Content-Length: 1\r\n\r\n{".as_slice()));
        assert!(matches!(
            reader.read_message::<Message>(),
            Err(ProtocolError::InvalidPayload(_))
        ));
    }

    #[test]
    fn writes_exact_frames_and_roundtrips_messages() {
        let mut writer = FramedWriter::new(Vec::new());
        let notification = Notification::new("ready", Some(json!([1, 2])));
        writer.write_message(&notification).unwrap();
        let bytes = writer.into_inner().unwrap();
        let expected_payload = br#"{"jsonrpc":"2.0","method":"ready","params":[1,2]}"#;
        let mut expected =
            format!("Content-Length: {}\r\n\r\n", expected_payload.len()).into_bytes();
        expected.extend_from_slice(expected_payload);
        assert_eq!(bytes, expected);

        let mut reader = FramedReader::new(Cursor::new(bytes));
        let decoded: Notification = reader.read_message().unwrap().unwrap();
        assert_eq!(decoded, notification);
    }
}
