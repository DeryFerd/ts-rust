//! Go JSON v2 default arshalers that `frontend/json.rs` lacks, for the
//! language-service port (plan contract C2).
//!
//! Behavior reference: `github.com/go-json-experiment/json`
//! v0.0.0-20260601182631-00ed12fed2a6 (`arshal_default.go`,
//! `arshal_any.go`, `jsontext/encode.go`, `jsontext/state.go`,
//! `internal/jsonwire`). Go reflects over types; each Rust type here has a
//! hand-written `MarshalerTo` / `UnmarshalerFrom` with the same default rules.
//!
//! Impls that already exist and are not added again: `json.rs` (String,
//! bool, f64 unmarshal; `FxHashMap<String, V>` unmarshal; str, String, bool,
//! `[T]`, `Vec<T>`, `IndexMap<String, V>` marshal) and `packagejson.rs`
//! (`IndexMap<String, V>` unmarshal, Go `collections.OrderedMap` rules).
//! `IndexMap<DocumentUri, V>` lives in `lsp/lsproto/lsp.rs`.
//!
//! PORT: error texts follow `json.rs` (no `json: ` prefix, no JSON pointer),
//! not the exact v2 texts. Integer arshalers do not port the stringified
//! form that v2 uses for integer map keys (no LSP type has integer keys).

use crate::frontend::prelude::*;

use std::any::Any;

/// Go `any` holding a value that the LSP layer can marshal
/// (`RequestMessage.Params`, `ResponseMessage.Result`, `Message.msg`).
/// Read it with `downcast_ref::<HoverParams>()`.
///
/// Never box a `Box<dyn AnyValue>` again: the blanket impl makes the box
/// itself an `AnyValue`, and a downcast of the outer box fails.
pub trait AnyValue: Any + MarshalerTo + std::fmt::Debug + Send {
    fn as_any(&self) -> &dyn Any;
}

impl<T: Any + MarshalerTo + std::fmt::Debug + Send> AnyValue for T {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl dyn AnyValue {
    /// Go type assertion `v.(T)` for a non-nil `any`.
    pub fn downcast_ref<T: 'static>(&self) -> Option<&T> {
        self.as_any().downcast_ref::<T>()
    }
}

/// Go `any` decoded from JSON (LSPAny): nil, `bool`, `float64`, `string`,
/// `[]any` and `map[string]any`.
/// PORT: `Object` keeps insertion order; Go map order is random.
#[derive(Clone, Debug, Default, PartialEq)]
pub enum LspAny {
    #[default]
    Null,
    Bool(bool),
    Number(f64),
    String(String),
    Array(Vec<LspAny>),
    Object(IndexMap<String, LspAny>),
}

/// Go `json.Value` (`jsontext.Value`): raw JSON bytes.
/// PORT: Go nil and empty are both an empty `Vec`.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct JsonValue(pub Vec<u8>);

impl AsRef<[u8]> for JsonValue {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

/// Go `omitzero` test (`reflect.Value.IsZero`, or a type's `IsZero`
/// method).
pub trait IsZero {
    fn is_zero(&self) -> bool;
}

impl IsZero for String {
    fn is_zero(&self) -> bool {
        self.is_empty()
    }
}

impl IsZero for bool {
    fn is_zero(&self) -> bool {
        !*self
    }
}

impl IsZero for i32 {
    fn is_zero(&self) -> bool {
        *self == 0
    }
}

impl IsZero for u32 {
    fn is_zero(&self) -> bool {
        *self == 0
    }
}

impl IsZero for u64 {
    fn is_zero(&self) -> bool {
        *self == 0
    }
}

// Go reflect: a float is zero only when all bits are zero, so -0 is not.
impl IsZero for f64 {
    fn is_zero(&self) -> bool {
        self.to_bits() == 0
    }
}

// PORT: Go omits only a nil slice; Rust cannot tell nil from empty.
impl<T> IsZero for Vec<T> {
    fn is_zero(&self) -> bool {
        self.is_empty()
    }
}

impl<T> IsZero for Option<T> {
    fn is_zero(&self) -> bool {
        self.is_none()
    }
}

// PORT: Go omits only a nil map; Rust cannot tell nil from empty.
impl<K, V, S> IsZero for IndexMap<K, V, S> {
    fn is_zero(&self) -> bool {
        self.is_empty()
    }
}

// Go: a nil `any` is zero; a non-nil `any` is not.
impl IsZero for LspAny {
    fn is_zero(&self) -> bool {
        matches!(self, LspAny::Null)
    }
}

impl IsZero for JsonValue {
    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

// Go jsontext `Kind.normalize`.
fn normalize_kind(c: u8) -> u8 {
    match c {
        b'-' | b'0'..=b'9' => b'0',
        _ => c,
    }
}

// The JSON kind word of a v2 `SemanticError`.
fn kind_name(k: u8) -> &'static str {
    match k {
        b'n' => "null",
        b'f' | b't' => "boolean",
        b'"' => "string",
        b'0' => "number",
        b'{' | b'}' => "object",
        b'[' | b']' => "array",
        _ => "value",
    }
}

// Go `newUnmarshalErrorAfter(dec, t, nil)`.
fn unmarshal_kind_error(k: u8, go_type: &str) -> JsonError {
    JsonError {
        message: format!("cannot unmarshal JSON {} into Go {go_type}", kind_name(k)),
    }
}

// Go `newUnmarshalErrorAfterWithValue(dec, t, err)`: the JSON value is part
// of the text when it is shorter than 100 bytes.
fn unmarshal_value_error(val: &[u8], go_type: &str, detail: &str) -> JsonError {
    let k = val.first().map_or(0, |&c| normalize_kind(c));
    let mut message = format!("cannot unmarshal JSON {}", kind_name(k));
    if !val.is_empty() && val.len() < 100 {
        message.push(' ');
        message.push_str(&String::from_utf8_lossy(val));
    }
    message.push_str(&format!(" into Go {go_type}: {detail}"));
    JsonError { message }
}

// Go `newUnmarshalErrorAfterWithSkipping`: after the first token of a value
// of the wrong kind was read, skip the rest of that value.
fn skip_rest_of_value(dec: &mut JsonDecoder<'_>, tok: &JsonToken) -> Result<(), JsonError> {
    let end = match tok {
        JsonToken::BeginObject => b'}',
        JsonToken::BeginArray => b']',
        _ => return Ok(()),
    };
    while dec.peek_kind() != end {
        dec.skip_value()?;
    }
    dec.read_token()?;
    Ok(())
}

// Go: jsonwire/decode.go:593 ParseUint
// ParseUint parses b as a decimal unsigned integer according to
// a strict subset of the JSON number grammar, returning the value if valid.
// It returns (0, false) if there is a syntax error and
// returns (math.MaxUint64, false) if there is an overflow.
fn parse_uint(b: &[u8]) -> (u64, bool) {
    const UNSAFE_WIDTH: usize = 20; // len(fmt.Sprint(uint64(math.MaxUint64)))
    let mut v: u64 = 0;
    let mut n = 0;
    while b.len() > n && b[n].is_ascii_digit() {
        v = v.wrapping_mul(10).wrapping_add(u64::from(b[n] - b'0'));
        n += 1;
    }
    if n == 0 || b.len() != n || (b[0] == b'0' && b != b"0") {
        return (0, false);
    }
    if n >= UNSAFE_WIDTH && (b[0] != b'1' || v < 10_000_000_000_000_000_000 || n > UNSAFE_WIDTH) {
        return (u64::MAX, false);
    }
    (v, true)
}

// Go: arshal_default.go:492 makeIntArshaler (unmarshal)
// Returns the value to store. `null` stores 0. A JSON string is an error
// (not stringified), and so is a number with a fraction or exponent.
fn unmarshal_int(dec: &mut JsonDecoder<'_>, bits: u32, go_type: &str) -> Result<i64, JsonError> {
    let val = dec.read_value()?;
    let k = val.first().map_or(0, |&c| normalize_kind(c));
    match k {
        b'n' => Ok(0),
        b'0' => {
            let neg = val[0] == b'-';
            let neg_offset = usize::from(neg);
            let (n, ok) = parse_uint(&val[neg_offset..]);
            let max_int = 1u64 << (bits - 1);
            let mut overflow = (neg && n > max_int) || (!neg && n > max_int - 1);
            if !ok {
                if n != u64::MAX {
                    return Err(unmarshal_value_error(val, go_type, "invalid syntax"));
                }
                overflow = true;
            }
            if overflow {
                return Err(unmarshal_value_error(val, go_type, "value out of range"));
            }
            if neg {
                Ok((n as i64).wrapping_neg())
            } else {
                Ok(n as i64)
            }
        }
        _ => Err(unmarshal_kind_error(k, go_type)),
    }
}

// Go: arshal_default.go:591 makeUintArshaler (unmarshal)
fn unmarshal_uint(dec: &mut JsonDecoder<'_>, bits: u32, go_type: &str) -> Result<u64, JsonError> {
    let val = dec.read_value()?;
    let k = val.first().map_or(0, |&c| normalize_kind(c));
    match k {
        b'n' => Ok(0),
        b'0' => {
            let (n, ok) = parse_uint(val);
            // Go `uint64(1) << bits` is 0 for 64 bits, so `maxUint-1` wraps.
            let max_uint = 1u64.checked_shl(bits).unwrap_or(0);
            let mut overflow = n > max_uint.wrapping_sub(1);
            if !ok {
                if n != u64::MAX {
                    return Err(unmarshal_value_error(val, go_type, "invalid syntax"));
                }
                overflow = true;
            }
            if overflow {
                return Err(unmarshal_value_error(val, go_type, "value out of range"));
            }
            Ok(n)
        }
        _ => Err(unmarshal_kind_error(k, go_type)),
    }
}

// Go: jsonwire/encode.go:213 AppendFloat (bits == 64)
// Go formats with strconv 'f' or 'e' and precision -1 (shortest digits that
// round-trip). Rust `{}` and `{:e}` print the same shortest digits.
fn append_float(dst: &mut String, src: f64) {
    let abs = src.abs();
    let mut fmt_e = false;
    if abs != 0.0 && (abs < 1e-6 || abs >= 1e21) {
        fmt_e = true;
    }
    if !fmt_e {
        dst.push_str(&format!("{src}"));
        return;
    }
    // Go 'e' writes the exponent sign and at least two digits; then
    // "e-09" is cleaned up to "e-9".
    let s = format!("{src:e}");
    let (mantissa, exp) = s.split_once('e').expect("LowerExp output has an exponent");
    let exp: i32 = exp.parse().expect("LowerExp exponent is an integer");
    dst.push_str(mantissa);
    dst.push('e');
    if exp < 0 {
        dst.push('-');
    } else {
        dst.push('+');
        if exp < 10 {
            dst.push('0');
        }
    }
    dst.push_str(&exp.unsigned_abs().to_string());
}

// ---------------------------------------------------------------------------
// Numbers
// ---------------------------------------------------------------------------

// Go: arshal_default.go:470 makeIntArshaler (marshal)
impl MarshalerTo for i32 {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        enc.push_str(&self.to_string());
        Ok(())
    }
}

// Go: arshal_default.go:569 makeUintArshaler (marshal)
impl MarshalerTo for u32 {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        enc.push_str(&self.to_string());
        Ok(())
    }
}

// Go: arshal_default.go:569 makeUintArshaler (marshal)
impl MarshalerTo for u64 {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        enc.push_str(&self.to_string());
        Ok(())
    }
}

// Go: arshal_default.go:659 makeFloatArshaler (marshal)
// NaN and infinities are an error ("nonfinite" format is not used).
impl MarshalerTo for f64 {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        let fv = *self;
        if fv.is_nan() || fv.is_infinite() {
            // Go `%v` of a float: NaN, +Inf, -Inf.
            let v = if fv.is_nan() {
                "NaN"
            } else if fv > 0.0 {
                "+Inf"
            } else {
                "-Inf"
            };
            return Err(JsonError {
                message: format!("cannot marshal from Go float64: unsupported value: {v}"),
            });
        }
        append_float(enc, fv);
        Ok(())
    }
}

// Go: arshal_default.go:492 makeIntArshaler (unmarshal)
impl UnmarshalerFrom for i32 {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        *self = unmarshal_int(dec, 32, "int32")? as i32;
        Ok(())
    }
}

// Go: arshal_default.go:591 makeUintArshaler (unmarshal)
impl UnmarshalerFrom for u32 {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        *self = unmarshal_uint(dec, 32, "uint32")? as u32;
        Ok(())
    }
}

// Go: arshal_default.go:591 makeUintArshaler (unmarshal)
impl UnmarshalerFrom for u64 {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        *self = unmarshal_uint(dec, 64, "uint64")?;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Pointers, slices, arrays
// ---------------------------------------------------------------------------

// Go: arshal_default.go:1714 makePointerArshaler (marshal): nil writes null.
impl<T: MarshalerTo> MarshalerTo for Option<T> {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        match self {
            None => {
                enc.push_str("null");
                Ok(())
            }
            Some(v) => v.marshal_json_to(enc),
        }
    }
}

// Go: arshal_default.go:1742 makePointerArshaler (unmarshal): null sets nil;
// otherwise a nil pointer gets a new zero value and the value decodes into
// the pointee (merging into an existing one).
impl<T: UnmarshalerFrom + Default> UnmarshalerFrom for Option<T> {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        if dec.peek_kind() == b'n' {
            dec.read_token()?;
            *self = None;
            return Ok(());
        }
        let v = self.get_or_insert_with(T::default);
        json_unmarshal_decode(dec, v)
    }
}

// PORT: `Box<T>` is a Go pointer on a type cycle. `null` is handled by the
// enclosing `Option`, so the box only forwards.
impl<T: MarshalerTo + ?Sized> MarshalerTo for Box<T> {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        (**self).marshal_json_to(enc)
    }
}

impl<T: UnmarshalerFrom + ?Sized> UnmarshalerFrom for Box<T> {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        (**self).unmarshal_json_from(dec)
    }
}

// Go: arshal_default.go:1528 makeSliceArshaler (unmarshal): null sets nil,
// each element starts from its zero value, `[]` sets an empty slice.
// PORT: nil and empty are both an empty `Vec`.
impl<T: UnmarshalerFrom + Default> UnmarshalerFrom for Vec<T> {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let tok = dec.read_token()?;
        match tok {
            JsonToken::Null => {
                self.clear();
                Ok(())
            }
            JsonToken::BeginArray => {
                self.clear();
                while dec.peek_kind() != b']' {
                    self.push(T::default());
                    let v = self.last_mut().expect("element was just pushed");
                    json_unmarshal_decode(dec, v)?;
                }
                dec.read_token()?;
                Ok(())
            }
            _ => {
                skip_rest_of_value(dec, &tok)?;
                Err(unmarshal_kind_error(tok.kind(), "slice"))
            }
        }
    }
}

// Go: arshal_default.go:1612 makeArrayArshaler (marshal)
impl MarshalerTo for [u32; 2] {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        self.as_slice().marshal_json_to(enc)
    }
}

// Go: arshal_default.go:1640 makeArrayArshaler (unmarshal): null sets the
// zero array; the JSON array must have exactly 2 elements.
impl UnmarshalerFrom for [u32; 2] {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let tok = dec.read_token()?;
        match tok {
            JsonToken::Null => {
                *self = [0, 0];
                Ok(())
            }
            JsonToken::BeginArray => {
                let n = self.len();
                let mut i = 0;
                let mut err: Option<&str> = None;
                while dec.peek_kind() != b']' {
                    if i >= n {
                        dec.skip_value()?;
                        err = Some("too many array elements");
                        continue;
                    }
                    self[i] = 0;
                    json_unmarshal_decode(dec, &mut self[i])?;
                    i += 1;
                }
                while i < n {
                    self[i] = 0;
                    err = Some("too few array elements");
                    i += 1;
                }
                dec.read_token()?;
                if let Some(err) = err {
                    return Err(JsonError {
                        message: format!("cannot unmarshal JSON array into Go [2]uint32: {err}"),
                    });
                }
                Ok(())
            }
            _ => {
                skip_rest_of_value(dec, &tok)?;
                Err(unmarshal_kind_error(tok.kind(), "[2]uint32"))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// any (LspAny)
// ---------------------------------------------------------------------------

// Go: arshal_any.go:32 marshalValueAny
// PORT: objects write in insertion order (Go map order is random).
impl MarshalerTo for LspAny {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        match self {
            LspAny::Null => {
                enc.push_str("null");
                Ok(())
            }
            LspAny::Bool(v) => v.marshal_json_to(enc),
            LspAny::String(v) => v.marshal_json_to(enc),
            LspAny::Number(v) => v.marshal_json_to(enc),
            LspAny::Object(v) => v.marshal_json_to(enc),
            LspAny::Array(v) => v.marshal_json_to(enc),
        }
    }
}

// Go: arshal_default.go:1847 makeInterfaceArshaler (unmarshal, `any`)
// `null` sets nil. A nil `any` decodes a fresh value (`unmarshalValueAny`,
// or the typed arshalers when duplicate names are allowed). A non-nil `any`
// decodes into a copy of its dynamic value.
// PORT: `IndexMap<String, V>` decodes with the `packagejson.rs` impl
// (OrderedMap rules), so merging into an existing object with
// `AllowDuplicateNames` replaces values instead of merging them.
impl UnmarshalerFrom for LspAny {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        if dec.peek_kind() == b'n' {
            dec.read_token()?;
            *self = LspAny::Null;
            return Ok(());
        }
        if matches!(self, LspAny::Null) {
            if !dec.options.allow_duplicate_names {
                *self = unmarshal_value_any(dec)?;
                return Ok(());
            }
            *self = match dec.peek_kind() {
                b'f' | b't' => LspAny::Bool(false),
                b'"' => LspAny::String(String::new()),
                b'0' => LspAny::Number(0.0),
                b'{' => LspAny::Object(IndexMap::new()),
                b'[' => LspAny::Array(Vec::new()),
                _ => {
                    // An invalid kind: ReadValue reports the error.
                    dec.read_value()?;
                    return Ok(());
                }
            };
        }
        match self {
            LspAny::Null => unreachable!("null was replaced above"),
            LspAny::Bool(v) => v.unmarshal_json_from(dec),
            LspAny::String(v) => v.unmarshal_json_from(dec),
            LspAny::Number(v) => v.unmarshal_json_from(dec),
            LspAny::Object(v) => v.unmarshal_json_from(dec),
            LspAny::Array(v) => v.unmarshal_json_from(dec),
        }
    }
}

// Go: arshal_any.go:64 unmarshalValueAny
// PORT: Go also returns the partial value with an error; callers here stop
// on the first error, so only the error is returned.
pub fn unmarshal_value_any(dec: &mut JsonDecoder<'_>) -> Result<LspAny, JsonError> {
    match dec.peek_kind() {
        b'{' => unmarshal_object_any(dec).map(LspAny::Object),
        b'[' => unmarshal_array_any(dec).map(LspAny::Array),
        _ => match dec.read_token()? {
            JsonToken::Null => Ok(LspAny::Null),
            JsonToken::False => Ok(LspAny::Bool(false)),
            JsonToken::True => Ok(LspAny::Bool(true)),
            JsonToken::String(s) => Ok(LspAny::String(s)),
            JsonToken::Number(raw) => {
                // The strict JSON grammar is a subset of the Rust float
                // syntax; both round to nearest, like strconv.ParseFloat.
                let fv: f64 = raw.parse().map_err(|_| JsonError {
                    message: "invalid number".to_string(),
                })?;
                if fv.is_infinite() {
                    return Err(JsonError {
                        message: format!(
                            "cannot unmarshal JSON number {raw} into Go float64: value out of range"
                        ),
                    });
                }
                Ok(LspAny::Number(fv))
            }
            tok => panic!("BUG: invalid kind: {}", char::from(tok.kind())),
        },
    }
}

// Go: arshal_any.go:177 unmarshalObjectAny
fn unmarshal_object_any(dec: &mut JsonDecoder<'_>) -> Result<IndexMap<String, LspAny>, JsonError> {
    let tok = dec.read_token()?;
    if tok != JsonToken::BeginObject {
        panic!("BUG: invalid kind: {}", char::from(tok.kind()));
    }
    let mut obj = IndexMap::new();
    // A Go map guarantees that each entry has a unique key.
    // The only possibility of duplicates is due to invalid UTF-8.
    if !dec.options.allow_invalid_utf8 {
        dec.disable_namespace();
    }
    while dec.peek_kind() != b'}' {
        let JsonToken::String(name) = dec.read_token()? else {
            unreachable!("object member names are strings")
        };

        // Manually check for duplicate names.
        if obj.contains_key(&name) {
            return Err(JsonError {
                message: format!("duplicate object member name {name:?}"),
            });
        }

        let val = unmarshal_value_any(dec)?;
        obj.insert(name, val);
    }
    dec.read_token()?;
    Ok(obj)
}

// Go: arshal_any.go:266 unmarshalArrayAny
fn unmarshal_array_any(dec: &mut JsonDecoder<'_>) -> Result<Vec<LspAny>, JsonError> {
    let tok = dec.read_token()?;
    if tok != JsonToken::BeginArray {
        panic!("BUG: invalid kind: {}", char::from(tok.kind()));
    }
    let mut arr = Vec::new();
    while dec.peek_kind() != b']' {
        let val = unmarshal_value_any(dec)?;
        arr.push(val);
    }
    dec.read_token()?;
    Ok(arr)
}

// Go: arshal_default.go:1847 makeInterfaceArshaler (unmarshal) for a Go
// `any` field held as `Option<Box<dyn AnyValue>>` (`RequestMessage.Params`,
// `ResponseMessage.Result`). `null` sets nil; a nil `any` gets a fresh
// `LspAny`; an existing `LspAny` decodes in place.
pub fn unmarshal_any_interface(
    dec: &mut JsonDecoder<'_>,
    va: &mut Option<Box<dyn AnyValue>>,
) -> Result<(), JsonError> {
    if dec.peek_kind() == b'n' {
        dec.read_token()?;
        *va = None;
        return Ok(());
    }
    if let Some(existing) = va {
        let existing: &mut dyn Any = &mut **existing;
        return match existing.downcast_mut::<LspAny>() {
            Some(v) => v.unmarshal_json_from(dec),
            None => unported!("json.Unmarshal into a non-nil any of a typed value"),
        };
    }
    let mut v = LspAny::Null;
    v.unmarshal_json_from(dec)?;
    *va = Some(Box::new(v));
    Ok(())
}

// ---------------------------------------------------------------------------
// json.Value
// ---------------------------------------------------------------------------

// Go: jsontext/value.go:238 Value.MarshalJSON, then the encoder writes the
// value with `WriteValue` (compact, canonical strings).
impl MarshalerTo for JsonValue {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        // NOTE: This matches the behavior of v1 json.RawMessage.MarshalJSON.
        if self.0.is_empty() {
            enc.push_str("null");
            return Ok(());
        }
        write_value(enc, &self.0)
    }
}

// Go: jsontext/value.go:248 Value.UnmarshalJSON: a copy of the raw input,
// `null` included.
impl UnmarshalerFrom for JsonValue {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let val = dec.read_value()?;
        self.0.clear();
        self.0.extend_from_slice(val);
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Encoder whitespace (compact and multiline)
// ---------------------------------------------------------------------------

// Go jsontext encoder state for `WriteToken` / `reformatValue`: one entry
// per open object or array (is object, number of names and values).
struct TokenWriter<'i> {
    stack: Vec<(bool, usize)>,
    top_len: usize,
    // Some((prefix, indent)) when `Multiline` is set.
    multiline: Option<(&'i str, &'i str)>,
}

impl TokenWriter<'_> {
    fn last(&self) -> (bool, usize) {
        self.stack.last().copied().unwrap_or((false, self.top_len))
    }

    fn increment(&mut self) {
        match self.stack.last_mut() {
            Some(e) => e.1 += 1,
            None => self.top_len += 1,
        }
    }

    // Go: jsontext/state.go:372 NeedIndent
    fn need_indent(&self, next: u8) -> usize {
        let will_end = next == b'}' || next == b']';
        let depth = self.stack.len() + 1;
        let (is_object, len) = self.last();
        let need_object_value = is_object && len % 2 == 1;
        let need_implicit_comma = !need_object_value && len > 0 && !will_end;
        if depth == 1 {
            0 // top-level values are never indented
        } else if len == 0 && will_end {
            0 // an empty object or array is never indented
        } else if len == 0 || need_implicit_comma {
            depth
        } else if will_end {
            depth - 1
        } else {
            0
        }
    }

    // Go: jsontext/encode.go:346 WriteToken with MayAppendDelim
    // (state.go:389), appendWhitespace (encode.go:634) and AppendIndent
    // (encode.go:652).
    fn write_token(&mut self, out: &mut String, tok: &JsonToken) -> Result<(), JsonError> {
        let k = tok.kind();
        let will_end = k == b'}' || k == b']';
        let (is_object, len) = self.last();
        let need_colon = is_object && len % 2 == 1;
        let need_comma = !need_colon && len > 0 && !will_end && !self.stack.is_empty();
        if need_colon {
            out.push(':');
        } else if need_comma {
            out.push(',');
        }
        if let Some((prefix, indent)) = self.multiline {
            if need_colon {
                // SpaceAfterColon is implied by Multiline.
                out.push(' ');
            } else {
                let n = self.need_indent(k);
                if n > 0 {
                    out.push('\n');
                    out.push_str(prefix);
                    for _ in 1..n {
                        out.push_str(indent);
                    }
                }
            }
        }
        match tok {
            JsonToken::Null => out.push_str("null"),
            JsonToken::False => out.push_str("false"),
            JsonToken::True => out.push_str("true"),
            JsonToken::String(s) => s.marshal_json_to(out)?,
            JsonToken::Number(raw) => out.push_str(raw),
            JsonToken::BeginObject => out.push('{'),
            JsonToken::EndObject => out.push('}'),
            JsonToken::BeginArray => out.push('['),
            JsonToken::EndArray => out.push(']'),
        }
        match tok {
            JsonToken::BeginObject | JsonToken::BeginArray => {
                self.increment();
                self.stack.push((k == b'{', 0));
            }
            JsonToken::EndObject | JsonToken::EndArray => {
                self.stack.pop();
            }
            _ => self.increment(),
        }
        Ok(())
    }

    // Reads one complete value from `dec` and writes it.
    fn write_value_from(
        &mut self,
        out: &mut String,
        dec: &mut JsonDecoder<'_>,
    ) -> Result<(), JsonError> {
        let depth = self.stack.len();
        loop {
            let tok = dec.read_token()?;
            self.write_token(out, &tok)?;
            if self.stack.len() == depth {
                return Ok(());
            }
        }
    }
}

// Go: jsontext/encode.go:526 WriteValue (compact output)
// Writes one raw JSON value: whitespace is removed, names must be unique,
// strings are re-quoted in canonical form (invalid UTF-8 becomes U+FFFD, as
// `internal/json.Marshal` sets AllowInvalidUTF8), numbers are copied
// verbatim, and only whitespace may follow the value.
pub fn write_value(enc: &mut String, raw: &[u8]) -> Result<(), JsonError> {
    let mut dec = JsonDecoder::new(
        raw,
        JsonOptions {
            allow_duplicate_names: false,
            allow_invalid_utf8: true,
            port_form: false,
        },
    );
    let mut w = TokenWriter {
        stack: Vec::new(),
        top_len: 0,
        multiline: None,
    };
    w.write_value_from(enc, &mut dec)?;
    dec.check_eof()
}

// Go: jsonwire/wire.go:62 QuoteRune
// QuoteRune quotes the first rune in the input.
pub fn quote_rune(b: &[u8]) -> String {
    // Go utf8.DecodeRune: (RuneError, 0) for empty input, (RuneError, 1)
    // for an invalid or truncated sequence.
    let Some(&first) = b.first() else {
        return crate::gostd::strconv::quote_rune('\u{FFFD}');
    };
    let n = match first {
        0x00..=0x7F => 1,
        0xC2..=0xDF => 2,
        0xE0..=0xEF => 3,
        0xF0..=0xF4 => 4,
        _ => 0,
    };
    let r = b
        .get(..n)
        .and_then(|s| std::str::from_utf8(s).ok())
        .and_then(|s| s.chars().next());
    match r {
        Some(r) => crate::gostd::strconv::quote_rune(r),
        None => format!("'\\x{first:x}'"),
    }
}

// ---------------------------------------------------------------------------
// Struct helpers (for hand-written and generated arshalers)
// ---------------------------------------------------------------------------

/// Go v2 struct marshal: `{`.
pub fn write_object_start(enc: &mut String) {
    enc.push('{');
}

/// Go v2 struct marshal: `}`.
pub fn write_object_end(enc: &mut String) {
    enc.push('}');
}

/// Writes one struct field (`"name":value`), with a comma before every
/// field but the first.
pub fn marshal_field<T: MarshalerTo + ?Sized>(
    enc: &mut String,
    first: &mut bool,
    name: &str,
    value: &T,
) -> Result<(), JsonError> {
    if !*first {
        enc.push(',');
    }
    *first = false;
    name.marshal_json_to(enc)?;
    enc.push(':');
    value.marshal_json_to(enc)
}

/// A field with Go `omitzero`: skipped when the value is zero.
pub fn marshal_field_omitzero<T: MarshalerTo + IsZero>(
    enc: &mut String,
    first: &mut bool,
    name: &str,
    value: &T,
) -> Result<(), JsonError> {
    if value.is_zero() {
        return Ok(());
    }
    marshal_field(enc, first, name, value)
}

/// An optional field (Go `*T` with `omitzero`): skipped when `None`.
pub fn marshal_opt_field<T: MarshalerTo>(
    enc: &mut String,
    first: &mut bool,
    name: &str,
    value: &Option<T>,
) -> Result<(), JsonError> {
    match value {
        None => Ok(()),
        Some(v) => marshal_field(enc, first, name, v),
    }
}

/// Go v2 default struct unmarshal (arshal_default.go:1283
/// makeStructArshaler) without reflection. `null` returns `Ok(false)` and
/// the caller sets the zero value. An object calls `field` for each member
/// name in input order; `field` decodes the value and returns `true`, or
/// returns `false` for an unknown name, which is then skipped. Names match
/// exactly. Any other kind is an error after the value is skipped.
pub fn unmarshal_struct_fields(
    dec: &mut JsonDecoder<'_>,
    go_type: &str,
    mut field: impl FnMut(&str, &mut JsonDecoder<'_>) -> Result<bool, JsonError>,
) -> Result<bool, JsonError> {
    let tok = dec.read_token()?;
    match tok {
        JsonToken::Null => Ok(false),
        JsonToken::BeginObject => {
            while dec.peek_kind() != b'}' {
                let JsonToken::String(name) = dec.read_token()? else {
                    unreachable!("object member names are strings")
                };
                if !field(&name, dec)? {
                    dec.skip_value()?;
                }
            }
            dec.read_token()?;
            Ok(true)
        }
        _ => {
            skip_rest_of_value(dec, &tok)?;
            Err(unmarshal_kind_error(tok.kind(), go_type))
        }
    }
}

// Go: internal/json/json.go:41 MarshalIndent with
// jsontext.WithIndentPrefix(prefix) and jsontext.WithIndent(indent):
// multiline output, a space after each colon, no space after commas, no
// newline inside an empty object or array, no trailing newline.
pub fn marshal_indent<T: MarshalerTo + ?Sized>(
    value: &T,
    prefix: &str,
    indent: &str,
) -> Result<String, JsonError> {
    if prefix.is_empty() && indent.is_empty() {
        // WithIndentPrefix and WithIndent imply multiline output, so skip them.
        return json_marshal(value, &[]);
    }
    // Go: jsontext/options.go:265 WithIndentPrefix, :232 WithIndent.
    let s = prefix.trim_matches(|c| c == ' ' || c == '\t');
    if !s.is_empty() {
        panic!(
            "json: invalid character {} in indent prefix",
            quote_rune(s.as_bytes())
        );
    }
    let s = indent.trim_matches(|c| c == ' ' || c == '\t');
    if !s.is_empty() {
        panic!(
            "json: invalid character {} in indent",
            quote_rune(s.as_bytes())
        );
    }
    let compact = json_marshal(value, &[])?;
    let mut dec = JsonDecoder::new(
        compact.as_bytes(),
        JsonOptions {
            allow_duplicate_names: false,
            allow_invalid_utf8: true,
            port_form: false,
        },
    );
    let mut w = TokenWriter {
        stack: Vec::new(),
        top_len: 0,
        multiline: Some((prefix, indent)),
    };
    let mut out = String::with_capacity(compact.len() * 2);
    w.write_value_from(&mut out, &mut dec)?;
    dec.check_eof()?;
    Ok(out)
}
