//! Port of internal/ipc/protocol_jsonrpc.go (internal/api/protocol_jsonrpc.go
//! before tsgo#4712).

use crate::ipc::prelude::*;

use crate::frontend::json::{json_marshal, json_unmarshal};
use crate::frontend::json_ext::{AnyValue, JsonValue};
use crate::gostd::{GoError, errors};
use crate::ipc::protocol::{Message, Protocol};
use crate::ipc::transport::{ConnReader, ConnWriter, ReadWriteCloser};
use crate::jsonrpc;
use std::io::BufReader;
use std::sync::Arc;

// Go: ipc/protocol_jsonrpc.go:12 JSONRPCProtocol
// JSONRPCProtocol implements the Protocol interface using JSON-RPC 2.0
// with the LSP base protocol framing (Content-Length headers).
pub struct JSONRPCProtocol {
    reader: jsonrpc::Reader,
    writer: jsonrpc::Writer,
}

// Go: ipc/protocol_jsonrpc.go:17
// var _ Protocol = (*JSONRPCProtocol)(nil) is the `impl Protocol` below.

// Go: ipc/protocol_jsonrpc.go:20 NewJSONRPCProtocol
// NewJSONRPCProtocol creates a new JSON-RPC protocol handler.
// PORT: Go takes an `io.ReadWriter`; the port takes the shared connection.
// Go `jsonrpc.NewReader` adds a 4096-byte `bufio.Reader`; the Rust reader
// takes the buffered reader from the caller.
pub fn new_jsonrpc_protocol(rw: Arc<dyn ReadWriteCloser>) -> JSONRPCProtocol {
    JSONRPCProtocol {
        reader: jsonrpc::new_reader(Box::new(BufReader::with_capacity(
            4096,
            ConnReader(rw.clone()),
        ))),
        writer: jsonrpc::new_writer(Box::new(ConnWriter(rw))),
    }
}

impl Protocol for JSONRPCProtocol {
    // Go: ipc/protocol_jsonrpc.go:28 ReadMessage
    // ReadMessage implements Protocol.
    fn read_message(&mut self) -> Result<Message, GoError> {
        let data = self.reader.read()?;

        let mut msg = Message::default();
        if let Err(err) = json_unmarshal(&data, &mut msg, &[]) {
            return Err(errors::from_value(err));
        }

        Ok(msg)
    }

    // Go: ipc/protocol_jsonrpc.go:43 WriteRequest
    // WriteRequest implements Protocol.
    fn write_request(
        &mut self,
        id: Option<&jsonrpc::ID>,
        method: &str,
        params: Option<Box<dyn AnyValue>>,
    ) -> Result<(), GoError> {
        let msg = jsonrpc::RequestMessage {
            id: id.cloned(),
            method: method.to_string(),
            params,
            ..Default::default()
        };
        let data = match json_marshal(&msg, &[]) {
            Ok(data) => data,
            Err(err) => return Err(errors::from_value(err)),
        };
        self.writer.write(data.as_bytes())
    }

    // Go: ipc/protocol_jsonrpc.go:57 WriteNotification
    // WriteNotification implements Protocol.
    fn write_notification(
        &mut self,
        method: &str,
        params: Option<Box<dyn AnyValue>>,
    ) -> Result<(), GoError> {
        let msg = jsonrpc::RequestMessage {
            method: method.to_string(),
            params,
            ..Default::default()
        };
        let data = match json_marshal(&msg, &[]) {
            Ok(data) => data,
            Err(err) => return Err(errors::from_value(err)),
        };
        self.writer.write(data.as_bytes())
    }

    // Go: ipc/protocol_jsonrpc.go:70 WriteResponse
    // WriteResponse implements Protocol.
    fn write_response(
        &mut self,
        id: Option<&jsonrpc::ID>,
        result: Option<Box<dyn AnyValue>>,
    ) -> Result<(), GoError> {
        let mut result = result;
        if result.is_none() {
            result = Some(Box::new(JsonValue(b"null".to_vec())));
        }
        let msg = jsonrpc::ResponseMessage {
            id: id.cloned(),
            result,
            ..Default::default()
        };
        let data = match json_marshal(&msg, &[]) {
            Ok(data) => data,
            Err(err) => return Err(errors::from_value(err)),
        };
        self.writer.write(data.as_bytes())
    }

    // Go: ipc/protocol_jsonrpc.go:86 WriteError
    // WriteError implements Protocol.
    fn write_error(
        &mut self,
        id: Option<&jsonrpc::ID>,
        resp_err: &jsonrpc::ResponseError,
    ) -> Result<(), GoError> {
        let msg = jsonrpc::ResponseMessage {
            id: id.cloned(),
            error: Some(resp_err.clone()),
            ..Default::default()
        };
        let data = match json_marshal(&msg, &[]) {
            Ok(data) => data,
            Err(err) => return Err(errors::from_value(err)),
        };
        self.writer.write(data.as_bytes())
    }
}
