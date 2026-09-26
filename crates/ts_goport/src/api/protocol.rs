//! Port of internal/api/protocol.go.

use crate::api::prelude::*;

use crate::frontend::json_ext::AnyValue;
use crate::gostd::GoError;
use crate::jsonrpc;

// Go: protocol.go:8 Message
// Message is an alias for jsonrpc.Message for convenience.
pub type Message = jsonrpc::Message;

// Go: protocol.go:11 Protocol
// Protocol defines the interface for reading and writing API messages.
// PORT: Go `*jsonrpc.ID` parameters are `Option<&jsonrpc::ID>` (nil is
// `None`); Go `any` params and results are `Option<Box<dyn AnyValue>>`
// (nil is `None`). The methods take `&mut self` because the reader and
// writer buffers change; the connections keep the protocol in a `RefCell`.
pub trait Protocol {
    // ReadMessage reads the next message from the connection.
    fn read_message(&mut self) -> Result<Message, GoError>;
    // WriteRequest writes a request message.
    fn write_request(
        &mut self,
        id: Option<&jsonrpc::ID>,
        method: &str,
        params: Option<Box<dyn AnyValue>>,
    ) -> Result<(), GoError>;
    // WriteNotification writes a notification message (no ID).
    fn write_notification(
        &mut self,
        method: &str,
        params: Option<Box<dyn AnyValue>>,
    ) -> Result<(), GoError>;
    // WriteResponse writes a successful response.
    fn write_response(
        &mut self,
        id: Option<&jsonrpc::ID>,
        result: Option<Box<dyn AnyValue>>,
    ) -> Result<(), GoError>;
    // WriteError writes an error response.
    fn write_error(
        &mut self,
        id: Option<&jsonrpc::ID>,
        err: &jsonrpc::ResponseError,
    ) -> Result<(), GoError>;
}
