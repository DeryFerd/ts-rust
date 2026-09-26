//! Port of internal/jsonrpc/jsonrpc.go.
//!
//! Package jsonrpc provides generic JSON-RPC 2.0 types and utilities
//! that can be shared between LSP and other JSON-RPC based protocols.
//!
//! PORT: Go marshals the tagged structs by reflection (JSON v2 default
//! rules); each one has a hand-written `MarshalerTo` / `UnmarshalerFrom`
//! here. Go `MarshalJSON` / `UnmarshalJSON` methods are kept as
//! `marshal_json` / `unmarshal_json` and the trait impls call them.

use crate::jsonrpc::prelude::*;

use crate::frontend::json::{
    JsonDecoder, JsonError, MarshalerTo, UnmarshalerFrom, json_marshal, json_unmarshal,
    json_unmarshal_decode,
};
use crate::frontend::json_ext::{
    AnyValue, JsonValue, LspAny, marshal_field, marshal_field_omitzero, marshal_opt_field,
    unmarshal_any_interface, unmarshal_struct_fields, write_object_end, write_object_start,
    write_value,
};
use crate::gostd::{GoError, errors};
use std::sync::LazyLock;

// Go: jsonrpc.go:14 JSONRPCVersion
/// JSONRPCVersion represents the JSON-RPC version field, always "2.0".
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct JSONRPCVersion;

// Go: jsonrpc.go:16 jsonRPCVersion
const JSON_RPC_VERSION: &str = "\"2.0\"";

impl JSONRPCVersion {
    // Go: jsonrpc.go:18 MarshalJSON
    pub fn marshal_json(&self) -> Result<Vec<u8>, GoError> {
        Ok(JSON_RPC_VERSION.as_bytes().to_vec())
    }

    // Go: jsonrpc.go:24 UnmarshalJSON
    pub fn unmarshal_json(&mut self, data: &[u8]) -> Result<(), GoError> {
        if data != JSON_RPC_VERSION.as_bytes() {
            return Err(ERR_INVALID_JSONRPC_VERSION.clone());
        }
        Ok(())
    }
}

// Go: jsonrpc.go:22 ErrInvalidJSONRPCVersion
pub static ERR_INVALID_JSONRPC_VERSION: LazyLock<GoError> =
    LazyLock::new(|| errors::new("invalid JSON-RPC version"));

// Go v2 calls MarshalJSON and writes its output with WriteValue.
impl MarshalerTo for JSONRPCVersion {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        let data = self
            .marshal_json()
            .map_err(|e| JsonError { message: e.error() })?;
        write_value(enc, &data)
    }
}

// Go v2 calls UnmarshalJSON with the raw value (`null` included).
impl UnmarshalerFrom for JSONRPCVersion {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let data = dec.read_value()?;
        self.unmarshal_json(data)
            .map_err(|e| JsonError { message: e.error() })
    }
}

// Go: jsonrpc.go:32 ID
/// ID represents a JSON-RPC message ID, which can be either a string or integer.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct ID {
    str: String,
    int: i32,
}

// Go: jsonrpc.go:38 NewID
// NewID creates an ID from an IntegerOrString value.
// PORT: Go returns `*ID`; it is never nil, so the Rust result is the value.
pub fn new_id(raw_value: &IntegerOrString) -> ID {
    if let Some(s) = &raw_value.string {
        return ID {
            str: s.clone(),
            ..ID::default()
        };
    }
    ID {
        int: raw_value
            .integer
            .expect("invalid memory address or nil pointer dereference"),
        ..ID::default()
    }
}

// Go: jsonrpc.go:46 NewIDString
// NewIDString creates a string ID.
pub fn new_id_string(str: &str) -> ID {
    ID {
        str: str.to_string(),
        ..ID::default()
    }
}

// Go: jsonrpc.go:51 NewIDInt
// NewIDInt creates an integer ID.
pub fn new_id_int(i: i32) -> ID {
    ID {
        int: i,
        ..ID::default()
    }
}

impl ID {
    // Go: jsonrpc.go:55 String
    pub fn string(&self) -> String {
        if !self.str.is_empty() {
            return self.str.clone();
        }
        self.int.to_string()
    }

    // Go: jsonrpc.go:62 MarshalJSON
    pub fn marshal_json(&self) -> Result<Vec<u8>, GoError> {
        let out = if !self.str.is_empty() {
            json_marshal(&self.str, &[])
        } else {
            json_marshal(&self.int, &[])
        };
        out.map(String::into_bytes).map_err(errors::from_value)
    }

    // Go: jsonrpc.go:69 UnmarshalJSON
    pub fn unmarshal_json(&mut self, data: &[u8]) -> Result<(), GoError> {
        *self = ID::default();
        if !data.is_empty() && data[0] == b'"' {
            return json_unmarshal(data, &mut self.str, &[]).map_err(errors::from_value);
        }
        json_unmarshal(data, &mut self.int, &[]).map_err(errors::from_value)
    }

    // Go: jsonrpc.go:77 TryInt
    // PORT: the Go method checks a nil receiver, so the Rust receiver is an
    // `Option` (`None` is nil).
    pub fn try_int(id: Option<&ID>) -> (i32, bool) {
        match id {
            Some(id) if id.str.is_empty() => (id.int, true),
            _ => (0, false),
        }
    }

    // Go: jsonrpc.go:84 MustInt
    pub fn must_int(&self) -> i32 {
        if !self.str.is_empty() {
            panic!("ID is not an integer");
        }
        self.int
    }
}

// Go `%s` / `%v` of an `*ID` calls String().
impl std::fmt::Display for ID {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string())
    }
}

// Go v2 calls MarshalJSON and writes its output with WriteValue.
impl MarshalerTo for ID {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        let data = self
            .marshal_json()
            .map_err(|e| JsonError { message: e.error() })?;
        write_value(enc, &data)
    }
}

// Go v2 calls UnmarshalJSON with the raw value. A `*ID` field handles
// `null` in the pointer arshaler (`Option<ID>`).
impl UnmarshalerFrom for ID {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let data = dec.read_value()?;
        self.unmarshal_json(data)
            .map_err(|e| JsonError { message: e.error() })
    }
}

// Go: jsonrpc.go:92 IntegerOrString
/// IntegerOrString is a helper type for creating IDs.
/// PORT: Go never marshals it (no JSON tags), so it has no JSON impls.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct IntegerOrString {
    pub integer: Option<i32>,
    pub string: Option<String>,
}

// Go: jsonrpc.go:98 ResponseError
/// ResponseError represents a JSON-RPC error response.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ResponseError {
    pub code: i32,
    pub message: String,
    pub data: Option<LspAny>,
}

impl ResponseError {
    // Go: jsonrpc.go:104 String
    // PORT: the Go method checks a nil receiver, so the Rust receiver is an
    // `Option` (`None` is nil).
    pub fn string(r: Option<&ResponseError>) -> String {
        let Some(r) = r else {
            return String::new();
        };
        let mut data = String::new();
        if r.data.marshal_json_to(&mut data).is_err() {
            // Go `%v` of a []byte prints the byte values of the partial
            // output of the failed marshal.
            let bytes: Vec<String> = data.bytes().map(|b| b.to_string()).collect();
            return format!("[{}]: {}\n[{}]", r.code, r.message, bytes.join(" "));
        }
        format!("[{}]: {}", r.code, r.message)
    }

    // Go: jsonrpc.go:115 Error
    pub fn error(r: Option<&ResponseError>) -> String {
        ResponseError::string(r)
    }
}

// Go: `*ResponseError` is an `error`; `errors::from_value` wraps it.
impl std::fmt::Display for ResponseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&ResponseError::error(Some(self)))
    }
}

impl MarshalerTo for ResponseError {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        let mut first = true;
        marshal_field(enc, &mut first, "code", &self.code)?;
        marshal_field(enc, &mut first, "message", &self.message)?;
        marshal_opt_field(enc, &mut first, "data", &self.data)?;
        write_object_end(enc);
        Ok(())
    }
}

impl UnmarshalerFrom for ResponseError {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let is_object = unmarshal_struct_fields(dec, "jsonrpc.ResponseError", |name, dec| {
            match name {
                "code" => json_unmarshal_decode(dec, &mut self.code)?,
                "message" => json_unmarshal_decode(dec, &mut self.message)?,
                "data" => json_unmarshal_decode(dec, &mut self.data)?,
                _ => return Ok(false),
            }
            Ok(true)
        })?;
        if !is_object {
            *self = ResponseError::default();
        }
        Ok(())
    }
}

// Go: jsonrpc.go:120
// Standard JSON-RPC error codes.
pub const CODE_PARSE_ERROR: i32 = -32700;
pub const CODE_INVALID_REQUEST: i32 = -32600;
pub const CODE_METHOD_NOT_FOUND: i32 = -32601;
pub const CODE_INVALID_PARAMS: i32 = -32602;
pub const CODE_INTERNAL_ERROR: i32 = -32603;

// Go: jsonrpc.go:129 MessageKind
/// MessageKind indicates what type of message this is.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct MessageKind(pub i32);

// Go: jsonrpc.go:131
impl MessageKind {
    pub const NOTIFICATION: MessageKind = MessageKind(0);
    pub const REQUEST: MessageKind = MessageKind(1);
    pub const RESPONSE: MessageKind = MessageKind(2);
}

// Go: jsonrpc.go:139 Message
/// Message represents a raw JSON-RPC message that can be a request, notification, or response.
/// Unlike lsproto.Message, this keeps params/result as raw JSON for generic handling.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Message {
    pub jsonrpc: JSONRPCVersion,
    pub id: Option<ID>,
    pub method: String,
    pub params: JsonValue,
    pub result: JsonValue,
    pub error: Option<ResponseError>,
}

impl Message {
    // Go: jsonrpc.go:149 Kind
    // Kind returns the kind of message this is.
    pub fn kind(&self) -> MessageKind {
        if self.id.is_some() && self.method.is_empty() {
            return MessageKind::RESPONSE;
        }
        if self.id.is_none() {
            return MessageKind::NOTIFICATION;
        }
        MessageKind::REQUEST
    }

    // Go: jsonrpc.go:160 IsRequest
    // IsRequest returns true if this message is a request (has ID and method).
    pub fn is_request(&self) -> bool {
        self.id.is_some() && !self.method.is_empty()
    }

    // Go: jsonrpc.go:165 IsNotification
    // IsNotification returns true if this message is a notification (has method but no ID).
    pub fn is_notification(&self) -> bool {
        self.id.is_none() && !self.method.is_empty()
    }

    // Go: jsonrpc.go:170 IsResponse
    // IsResponse returns true if this message is a response (has ID but no method).
    pub fn is_response(&self) -> bool {
        self.id.is_some() && self.method.is_empty()
    }
}

impl MarshalerTo for Message {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        let mut first = true;
        marshal_field(enc, &mut first, "jsonrpc", &self.jsonrpc)?;
        marshal_opt_field(enc, &mut first, "id", &self.id)?;
        marshal_field_omitzero(enc, &mut first, "method", &self.method)?;
        marshal_field_omitzero(enc, &mut first, "params", &self.params)?;
        marshal_field_omitzero(enc, &mut first, "result", &self.result)?;
        marshal_opt_field(enc, &mut first, "error", &self.error)?;
        write_object_end(enc);
        Ok(())
    }
}

impl UnmarshalerFrom for Message {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let is_object = unmarshal_struct_fields(dec, "jsonrpc.Message", |name, dec| {
            match name {
                "jsonrpc" => json_unmarshal_decode(dec, &mut self.jsonrpc)?,
                "id" => json_unmarshal_decode(dec, &mut self.id)?,
                "method" => json_unmarshal_decode(dec, &mut self.method)?,
                "params" => json_unmarshal_decode(dec, &mut self.params)?,
                "result" => json_unmarshal_decode(dec, &mut self.result)?,
                "error" => json_unmarshal_decode(dec, &mut self.error)?,
                _ => return Ok(false),
            }
            Ok(true)
        })?;
        if !is_object {
            *self = Message::default();
        }
        Ok(())
    }
}

// Go: jsonrpc.go:175 RequestMessage
/// RequestMessage is a convenience type for creating request/notification messages.
/// PORT: Go `Params any` is `Option<Box<dyn AnyValue>>` (`None` is nil).
#[derive(Debug, Default)]
pub struct RequestMessage {
    pub jsonrpc: JSONRPCVersion,
    pub id: Option<ID>,
    pub method: String,
    pub params: Option<Box<dyn AnyValue>>,
}

impl MarshalerTo for RequestMessage {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        let mut first = true;
        marshal_field(enc, &mut first, "jsonrpc", &self.jsonrpc)?;
        marshal_opt_field(enc, &mut first, "id", &self.id)?;
        marshal_field(enc, &mut first, "method", &self.method)?;
        marshal_opt_field(enc, &mut first, "params", &self.params)?;
        write_object_end(enc);
        Ok(())
    }
}

impl UnmarshalerFrom for RequestMessage {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let is_object = unmarshal_struct_fields(dec, "jsonrpc.RequestMessage", |name, dec| {
            match name {
                "jsonrpc" => json_unmarshal_decode(dec, &mut self.jsonrpc)?,
                "id" => json_unmarshal_decode(dec, &mut self.id)?,
                "method" => json_unmarshal_decode(dec, &mut self.method)?,
                "params" => unmarshal_any_interface(dec, &mut self.params)?,
                _ => return Ok(false),
            }
            Ok(true)
        })?;
        if !is_object {
            *self = RequestMessage::default();
        }
        Ok(())
    }
}

// Go: jsonrpc.go:183 ResponseMessage
/// ResponseMessage is a convenience type for creating response messages.
/// PORT: Go `Result any` is `Option<Box<dyn AnyValue>>` (`None` is nil).
#[derive(Debug, Default)]
pub struct ResponseMessage {
    pub jsonrpc: JSONRPCVersion,
    pub id: Option<ID>,
    pub result: Option<Box<dyn AnyValue>>,
    pub error: Option<ResponseError>,
}

impl MarshalerTo for ResponseMessage {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        let mut first = true;
        marshal_field(enc, &mut first, "jsonrpc", &self.jsonrpc)?;
        marshal_opt_field(enc, &mut first, "id", &self.id)?;
        marshal_opt_field(enc, &mut first, "result", &self.result)?;
        marshal_opt_field(enc, &mut first, "error", &self.error)?;
        write_object_end(enc);
        Ok(())
    }
}

impl UnmarshalerFrom for ResponseMessage {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let is_object = unmarshal_struct_fields(dec, "jsonrpc.ResponseMessage", |name, dec| {
            match name {
                "jsonrpc" => json_unmarshal_decode(dec, &mut self.jsonrpc)?,
                "id" => json_unmarshal_decode(dec, &mut self.id)?,
                "result" => unmarshal_any_interface(dec, &mut self.result)?,
                "error" => json_unmarshal_decode(dec, &mut self.error)?,
                _ => return Ok(false),
            }
            Ok(true)
        })?;
        if !is_object {
            *self = ResponseMessage::default();
        }
        Ok(())
    }
}
