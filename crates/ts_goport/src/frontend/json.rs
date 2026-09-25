//! Port of json/json.go.
//!
//! Go `internal/json` is a thin wrapper over `github.com/go-json-experiment/json`
//! (JSON v2) and its `jsontext` package. This crate has no JSON dependency, so
//! the parts of v2 that the compiler reads through are ported here by hand:
//!
//! - `JsonDecoder` is the `jsontext.Decoder` token state machine: strict RFC
//!   8259 grammar, `:` and `,` checks in `PeekKind`, a trailing comma is an
//!   error, strings reject control characters and lone surrogates, and object
//!   names are checked for duplicates unless `AllowDuplicateNames` is set or
//!   the arshaler disabled the namespace.
//! - `UnmarshalerFrom` stands in for both Go `json.UnmarshalerFrom` and the
//!   v2 default arshalers. The impls for `String`, `bool`, `f64` and
//!   `FxHashMap<String, V>` follow the v2 default arshalers (null gives the
//!   zero value, a kind mismatch is an error, maps merge into the existing map).
//! - `MarshalerTo` stands in for the v2 default marshalers of the value kinds
//!   the compiler marshals (strings, booleans, slices and ordered maps).
//!
//! PORT: without legacy flags every v2 unmarshal error is fatal
//! (`isFatalError`), so every impl returns the first error. Error messages are
//! not the v2 texts; no caller shows them.

use crate::frontend::prelude::*;

/// Go JSON v2 `*json.SemanticError` / `*jsontext.SyntacticError`.
/// PORT: one error type with a message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JsonError {
    pub message: String,
}

impl JsonError {
    fn new(message: impl Into<String>) -> JsonError {
        JsonError { message: message.into() }
    }
}

impl std::fmt::Display for JsonError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

/// Go `json.Options` values that the compiler passes.
/// PORT: Go options are opaque values; this enum lists the ones used here.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JsonOption {
    AllowDuplicateNames(bool),
    AllowInvalidUtf8(bool),
}

/// Resolved decoder and encoder flags.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct JsonOptions {
    pub allow_duplicate_names: bool,
    pub allow_invalid_utf8: bool,
}

impl JsonOptions {
    fn from_options(opts: &[JsonOption]) -> JsonOptions {
        let mut o = JsonOptions::default();
        for opt in opts {
            match *opt {
                JsonOption::AllowDuplicateNames(v) => o.allow_duplicate_names = v,
                JsonOption::AllowInvalidUtf8(v) => o.allow_invalid_utf8 = v,
            }
        }
        o
    }
}

/// Go `jsontext.Token`, as returned by `Decoder.ReadToken`.
#[derive(Clone, Debug, PartialEq)]
pub enum JsonToken {
    Null,
    False,
    True,
    String(String),
    /// The raw number text.
    Number(String),
    BeginObject,
    EndObject,
    BeginArray,
    EndArray,
}

impl JsonToken {
    /// Go `jsontext.Token.Kind`.
    #[must_use]
    pub fn kind(&self) -> u8 {
        match self {
            JsonToken::Null => b'n',
            JsonToken::False => b'f',
            JsonToken::True => b't',
            JsonToken::String(_) => b'"',
            JsonToken::Number(_) => b'0',
            JsonToken::BeginObject => b'{',
            JsonToken::EndObject => b'}',
            JsonToken::BeginArray => b'[',
            JsonToken::EndArray => b']',
        }
    }
}

// Go jsontext `maxNestingDepth`.
const MAX_NESTING_DEPTH: usize = 10000;

// One open JSON object or array (Go jsontext `stateEntry` plus the
// namespace of seen object names).
struct Frame {
    is_object: bool,
    len: usize,
    // `None` when duplicate names are allowed or the namespace is disabled.
    names: Option<FxHashSet<String>>,
}

/// Go `jsontext.Decoder` over a complete input buffer.
pub struct JsonDecoder<'a> {
    buf: &'a [u8],
    // Go `prevEnd`: the end of the last read token or value.
    pos: usize,
    // Open containers. The top-level virtual array is `top_len`.
    stack: Vec<Frame>,
    top_len: usize,
    pub options: JsonOptions,
}

fn is_ws(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\r' | b'\n')
}

// Go `jsontext.Kind.normalize`.
fn normalize_kind(c: u8) -> u8 {
    match c {
        b'-' | b'0'..=b'9' => b'0',
        _ => c,
    }
}

fn hex_val(c: u8) -> Option<u32> {
    match c {
        b'0'..=b'9' => Some(u32::from(c - b'0')),
        b'a'..=b'f' => Some(u32::from(c - b'a' + 10)),
        b'A'..=b'F' => Some(u32::from(c - b'A' + 10)),
        _ => None,
    }
}

// Decodes one UTF-8 character at the start of `b`.
fn decode_utf8(b: &[u8]) -> Option<(char, usize)> {
    let n = match b.first()? {
        0x00..=0x7F => 1,
        0xC2..=0xDF => 2,
        0xE0..=0xEF => 3,
        0xF0..=0xF4 => 4,
        _ => return None,
    };
    let s = std::str::from_utf8(b.get(..n)?).ok()?;
    s.chars().next().map(|c| (c, n))
}

impl<'a> JsonDecoder<'a> {
    #[must_use]
    pub fn new(buf: &'a [u8], options: JsonOptions) -> JsonDecoder<'a> {
        JsonDecoder { buf, pos: 0, stack: Vec::new(), top_len: 0, options }
    }

    fn skip_ws(&self, mut p: usize) -> usize {
        while p < self.buf.len() && is_ws(self.buf[p]) {
            p += 1;
        }
        p
    }

    fn last_len(&self) -> usize {
        self.stack.last().map_or(self.top_len, |f| f.len)
    }

    fn last_is_object(&self) -> bool {
        self.stack.last().is_some_and(|f| f.is_object)
    }

    fn need_object_value(&self) -> bool {
        self.last_is_object() && self.last_len() % 2 == 1
    }

    fn need_object_name(&self) -> bool {
        self.last_is_object() && self.last_len().is_multiple_of(2)
    }

    fn increment(&mut self) {
        match self.stack.last_mut() {
            Some(f) => f.len += 1,
            None => self.top_len += 1,
        }
    }

    // Go jsontext `stateMachine.needDelim`.
    fn need_delim(&self, next: u8) -> u8 {
        if self.need_object_value() {
            b':'
        } else if self.last_len() > 0 && next != b'}' && next != b']' && !self.stack.is_empty() {
            b','
        } else {
            0
        }
    }

    // Go jsontext `decoderState.PeekKind` without the cache: the position and
    // normalized kind of the next token, after whitespace and one delimiter.
    fn peek_pos(&self) -> Result<(usize, u8), JsonError> {
        let mut p = self.skip_ws(self.pos);
        if p >= self.buf.len() {
            return Err(JsonError::new("unexpected EOF"));
        }
        let mut delim = 0;
        let c = self.buf[p];
        if c == b':' || c == b',' {
            delim = c;
            p = self.skip_ws(p + 1);
            if p >= self.buf.len() {
                return Err(JsonError::new("unexpected EOF"));
            }
        }
        let next = normalize_kind(self.buf[p]);
        if self.need_delim(next) != delim {
            return Err(JsonError::new(format!("invalid character {:?} at offset {p}", char::from(self.buf[p]))));
        }
        Ok((p, next))
    }

    /// Go `jsontext.Decoder.PeekKind`. Returns 0 on error.
    #[must_use]
    pub fn peek_kind(&self) -> u8 {
        self.peek_pos().map_or(0, |(_, k)| k)
    }

    /// Go `jsontext.Decoder.DisableNamespace` (the export helper
    /// `Tokens.Last.DisableNamespace`): stop duplicate-name checks for the
    /// innermost open object.
    pub fn disable_namespace(&mut self) {
        if let Some(f) = self.stack.last_mut() {
            f.names = None;
        }
    }

    /// Go `jsontext.Decoder.StackDepth` plus the length of the innermost
    /// container. Used to check that an unmarshaler reads exactly one value.
    fn depth_length(&self) -> (usize, usize) {
        (self.stack.len(), self.last_len())
    }

    fn append_value(&mut self) -> Result<(), JsonError> {
        if self.need_object_name() {
            return Err(JsonError::new("object member name must be a string"));
        }
        self.increment();
        Ok(())
    }

    /// Go `jsontext.Decoder.ReadToken`.
    pub fn read_token(&mut self) -> Result<JsonToken, JsonError> {
        let (p, _) = self.peek_pos()?;
        let c = self.buf[p];
        match c {
            b'n' | b't' | b'f' => {
                let (lit, tok): (&[u8], JsonToken) = match c {
                    b'n' => (b"null", JsonToken::Null),
                    b't' => (b"true", JsonToken::True),
                    _ => (b"false", JsonToken::False),
                };
                if !self.buf[p..].starts_with(lit) {
                    return Err(JsonError::new(format!("invalid literal at offset {p}")));
                }
                self.append_value()?;
                self.pos = p + lit.len();
                Ok(tok)
            }
            b'"' => {
                let (end, s) = self.consume_string(p)?;
                if self.need_object_name() {
                    let dup = match &mut self.stack.last_mut().expect("object frame").names {
                        Some(names) => !names.insert(s.clone()),
                        None => false,
                    };
                    if dup {
                        return Err(JsonError::new(format!("duplicate object member name {s:?}")));
                    }
                }
                self.increment();
                self.pos = end;
                Ok(JsonToken::String(s))
            }
            b'-' | b'0'..=b'9' => {
                let end = self.consume_number(p)?;
                self.append_value()?;
                self.pos = end;
                let raw = std::str::from_utf8(&self.buf[p..end]).expect("number is ASCII");
                Ok(JsonToken::Number(raw.to_string()))
            }
            b'{' | b'[' => {
                if self.need_object_name() {
                    return Err(JsonError::new("object member name must be a string"));
                }
                if self.stack.len() == MAX_NESTING_DEPTH {
                    return Err(JsonError::new("exceeded max depth"));
                }
                self.increment();
                let is_object = c == b'{';
                let names = if is_object && !self.options.allow_duplicate_names { Some(FxHashSet::default()) } else { None };
                self.stack.push(Frame { is_object, len: 0, names });
                self.pos = p + 1;
                Ok(if is_object { JsonToken::BeginObject } else { JsonToken::BeginArray })
            }
            b'}' => {
                if !self.last_is_object() {
                    return Err(JsonError::new("mismatching structural token for object"));
                }
                if self.need_object_value() {
                    return Err(JsonError::new("missing value after object name"));
                }
                self.stack.pop();
                self.pos = p + 1;
                Ok(JsonToken::EndObject)
            }
            b']' => {
                if self.stack.is_empty() || self.last_is_object() {
                    return Err(JsonError::new("mismatching structural token for array"));
                }
                self.stack.pop();
                self.pos = p + 1;
                Ok(JsonToken::EndArray)
            }
            _ => Err(JsonError::new(format!("invalid character {:?} at offset {p}", char::from(c)))),
        }
    }

    /// Go `jsontext.Decoder.ReadValue`: the raw bytes of the next complete
    /// value (or object name).
    pub fn read_value(&mut self) -> Result<&'a [u8], JsonError> {
        let (start, _) = self.peek_pos()?;
        let depth = self.stack.len();
        let tok = self.read_token()?;
        if matches!(tok, JsonToken::BeginObject | JsonToken::BeginArray) {
            while self.stack.len() > depth {
                self.read_token()?;
            }
        }
        Ok(&self.buf[start..self.pos])
    }

    /// Go `jsontext.Decoder.SkipValue`.
    pub fn skip_value(&mut self) -> Result<(), JsonError> {
        self.read_value().map(|_| ())
    }

    /// Go `jsontext` `decoderState.CheckEOF`: only whitespace may follow the
    /// top-level value.
    pub fn check_eof(&self) -> Result<(), JsonError> {
        let p = self.skip_ws(self.pos);
        if p < self.buf.len() {
            return Err(JsonError::new(format!(
                "invalid character {:?} after top-level value",
                char::from(self.buf[p])
            )));
        }
        Ok(())
    }

    // Go `jsonwire.ConsumeString` plus unquoting. Returns the end offset and
    // the unquoted text.
    fn consume_string(&self, p: usize) -> Result<(usize, String), JsonError> {
        let b = self.buf;
        let mut out = String::new();
        let mut i = p + 1;
        loop {
            let Some(&c) = b.get(i) else {
                return Err(JsonError::new("unexpected EOF within string"));
            };
            match c {
                b'"' => return Ok((i + 1, out)),
                b'\\' => {
                    let Some(&e) = b.get(i + 1) else {
                        return Err(JsonError::new("unexpected EOF within string"));
                    };
                    i += 2;
                    match e {
                        b'"' => out.push('"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\u{8}'),
                        b'f' => out.push('\u{C}'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let v1 = self.parse_hex4(i)?;
                            i += 4;
                            if (0xD800..0xE000).contains(&v1) {
                                // A surrogate must be a high surrogate followed by
                                // an escaped low surrogate.
                                let mut decoded = None;
                                if v1 < 0xDC00 && b.get(i) == Some(&b'\\') && b.get(i + 1) == Some(&b'u') {
                                    let v2 = self.parse_hex4(i + 2)?;
                                    if (0xDC00..0xE000).contains(&v2) {
                                        decoded = char::from_u32(0x10000 + ((v1 - 0xD800) << 10) + (v2 - 0xDC00));
                                        if decoded.is_some() {
                                            i += 6;
                                        }
                                    }
                                }
                                match decoded {
                                    Some(ch) => out.push(ch),
                                    None if self.options.allow_invalid_utf8 => out.push('\u{FFFD}'),
                                    None => return Err(JsonError::new("invalid surrogate in string escape")),
                                }
                            } else {
                                out.push(char::from_u32(v1).expect("non-surrogate BMP code point"));
                            }
                        }
                        _ => return Err(JsonError::new("invalid escape sequence in string")),
                    }
                }
                0x00..=0x1F => return Err(JsonError::new("invalid control character in string")),
                0x20..=0x7F => {
                    out.push(char::from(c));
                    i += 1;
                }
                _ => match decode_utf8(&b[i..]) {
                    Some((ch, n)) => {
                        out.push(ch);
                        i += n;
                    }
                    None if self.options.allow_invalid_utf8 => {
                        out.push('\u{FFFD}');
                        i += 1;
                    }
                    None => return Err(JsonError::new("invalid UTF-8 within string")),
                },
            }
        }
    }

    fn parse_hex4(&self, i: usize) -> Result<u32, JsonError> {
        let mut v = 0;
        for k in 0..4 {
            let Some(d) = self.buf.get(i + k).copied().and_then(hex_val) else {
                return Err(JsonError::new("invalid escape sequence in string"));
            };
            v = v * 16 + d;
        }
        Ok(v)
    }

    // Go `jsonwire.ConsumeNumber`: `-?(0|[1-9]\d*)(\.\d+)?([eE][+-]?\d+)?`.
    fn consume_number(&self, p: usize) -> Result<usize, JsonError> {
        let b = self.buf;
        let digits = |mut i: usize| {
            let s = i;
            while i < b.len() && b[i].is_ascii_digit() {
                i += 1;
            }
            (i, i - s)
        };
        let invalid = || JsonError::new(format!("invalid number at offset {p}"));
        let mut i = p;
        if b.get(i) == Some(&b'-') {
            i += 1;
        }
        match b.get(i) {
            Some(b'0') => i += 1,
            Some(b'1'..=b'9') => i = digits(i).0,
            _ => return Err(invalid()),
        }
        if b.get(i) == Some(&b'.') {
            let (j, n) = digits(i + 1);
            if n == 0 {
                return Err(invalid());
            }
            i = j;
        }
        if matches!(b.get(i), Some(b'e' | b'E')) {
            i += 1;
            if matches!(b.get(i), Some(b'+' | b'-')) {
                i += 1;
            }
            let (j, n) = digits(i);
            if n == 0 {
                return Err(invalid());
            }
            i = j;
        }
        Ok(i)
    }
}

/// Go `json.UnmarshalerFrom` and the JSON v2 default unmarshalers.
pub trait UnmarshalerFrom {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError>;
}

/// Go `json.MarshalerTo` and the JSON v2 default marshalers.
/// PORT: the encoder is the output string. Output is compact.
pub trait MarshalerTo {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError>;
}

// Go v2 string arshaler: null gives "", a string sets the value, any other
// kind is an error after the value is read.
impl UnmarshalerFrom for String {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        match dec.peek_kind() {
            b'n' => {
                dec.read_token()?;
                self.clear();
                Ok(())
            }
            b'"' => {
                let JsonToken::String(s) = dec.read_token()? else {
                    unreachable!("peeked a string")
                };
                *self = s;
                Ok(())
            }
            _ => {
                dec.skip_value()?;
                Err(JsonError::new("cannot unmarshal JSON value into Go string"))
            }
        }
    }
}

// Go v2 bool arshaler.
impl UnmarshalerFrom for bool {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        match dec.peek_kind() {
            b'n' | b't' | b'f' => {
                *self = dec.read_token()? == JsonToken::True;
                Ok(())
            }
            _ => {
                dec.skip_value()?;
                Err(JsonError::new("cannot unmarshal JSON value into Go bool"))
            }
        }
    }
}

// Go v2 float64 arshaler. An out-of-range number sets ±Inf and is an error,
// like Go `strconv.ParseFloat`.
impl UnmarshalerFrom for f64 {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        match dec.peek_kind() {
            b'n' => {
                dec.read_token()?;
                *self = 0.0;
                Ok(())
            }
            b'0' => {
                let JsonToken::Number(raw) = dec.read_token()? else {
                    unreachable!("peeked a number")
                };
                // The strict JSON grammar is a subset of the Rust float syntax,
                // and both round to nearest.
                let v: f64 = raw.parse().map_err(|_| JsonError::new("invalid number"))?;
                *self = v;
                if v.is_infinite() {
                    return Err(JsonError::new(format!("cannot unmarshal JSON number {raw} into Go float64: value out of range")));
                }
                Ok(())
            }
            _ => {
                dec.skip_value()?;
                Err(JsonError::new("cannot unmarshal JSON value into Go float64"))
            }
        }
    }
}

// Go v2 map arshaler for `map[string]V`. The map merges into the existing
// map. A name that is already in the map is a duplicate only if it came from
// this JSON object (the `seen` set), unless `AllowDuplicateNames` is set.
impl<V: UnmarshalerFrom + Default + Clone> UnmarshalerFrom for FxHashMap<String, V> {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let tok = dec.read_token()?;
        match tok {
            JsonToken::Null => {
                // PORT: Go sets a nil map. An empty map is the Rust zero value.
                self.clear();
                Ok(())
            }
            JsonToken::BeginObject => {
                // String keys have a unique representation unless invalid
                // UTF-8 is allowed, so the map does its own duplicate check.
                if !dec.options.allow_invalid_utf8 {
                    dec.disable_namespace();
                }
                let allow_dup = dec.options.allow_duplicate_names;
                let mut seen: Option<FxHashSet<String>> =
                    if !allow_dup && !self.is_empty() { Some(FxHashSet::default()) } else { None };
                while dec.peek_kind() != b'}' {
                    let mut k = String::new();
                    json_unmarshal_decode(dec, &mut k)?;
                    let mut v = V::default();
                    if let Some(existing) = self.get(&k) {
                        if !allow_dup && seen.as_ref().is_none_or(|s| s.contains(&k)) {
                            return Err(JsonError::new(format!("duplicate object member name {k:?}")));
                        }
                        v = existing.clone();
                    }
                    let err = json_unmarshal_decode(dec, &mut v);
                    if let Some(s) = &mut seen {
                        s.insert(k.clone());
                    }
                    self.insert(k, v);
                    err?;
                }
                dec.read_token()?;
                Ok(())
            }
            _ => {
                if tok == JsonToken::BeginArray {
                    // Go `newUnmarshalErrorAfterWithSkipping`.
                    while dec.peek_kind() != b']' {
                        dec.skip_value()?;
                    }
                    dec.read_token()?;
                }
                Err(JsonError::new("cannot unmarshal JSON value into Go map"))
            }
        }
    }
}

// Go v2 string marshaler: escapes `"`, `\` and control characters only.
impl MarshalerTo for str {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        const HEX: &[u8; 16] = b"0123456789abcdef";
        enc.push('"');
        for c in self.chars() {
            match c {
                '"' => enc.push_str("\\\""),
                '\\' => enc.push_str("\\\\"),
                '\u{8}' => enc.push_str("\\b"),
                '\u{C}' => enc.push_str("\\f"),
                '\n' => enc.push_str("\\n"),
                '\r' => enc.push_str("\\r"),
                '\t' => enc.push_str("\\t"),
                c if (c as u32) < 0x20 => {
                    let b = c as usize;
                    enc.push_str("\\u00");
                    enc.push(char::from(HEX[b >> 4]));
                    enc.push(char::from(HEX[b & 0xF]));
                }
                c => enc.push(c),
            }
        }
        enc.push('"');
        Ok(())
    }
}

impl MarshalerTo for String {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        self.as_str().marshal_json_to(enc)
    }
}

impl MarshalerTo for bool {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        enc.push_str(if *self { "true" } else { "false" });
        Ok(())
    }
}

// Go v2 slice marshaler. PORT: Go marshals a nil slice as `[]` in v2 too
// (`FormatNilSliceAsNull` is off by default), so there is no null case.
impl<T: MarshalerTo> MarshalerTo for [T] {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        enc.push('[');
        for (i, v) in self.iter().enumerate() {
            if i > 0 {
                enc.push(',');
            }
            v.marshal_json_to(enc)?;
        }
        enc.push(']');
        Ok(())
    }
}

impl<T: MarshalerTo> MarshalerTo for Vec<T> {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        self.as_slice().marshal_json_to(enc)
    }
}

// Go `collections.OrderedMap.MarshalJSONTo`: members in insertion order.
impl<V: MarshalerTo> MarshalerTo for IndexMap<String, V> {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        enc.push('{');
        for (i, (k, v)) in self.iter().enumerate() {
            if i > 0 {
                enc.push(',');
            }
            k.marshal_json_to(enc)?;
            enc.push(':');
            v.marshal_json_to(enc)?;
        }
        enc.push('}');
        Ok(())
    }
}

impl<T: MarshalerTo + ?Sized> MarshalerTo for &T {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        (**self).marshal_json_to(enc)
    }
}

// Go: json/json.go:12 allowInvalid
// PORT: the Go slice of options is a constant list.
const ALLOW_INVALID: &[JsonOption] = &[JsonOption::AllowInvalidUtf8(true)];

// Go: json/json.go:14 Marshal
// PORT: named `json_marshal` so the glob export stays unambiguous. Go returns
// bytes; the output here is always UTF-8 text. Rust strings are always valid
// UTF-8, so `AllowInvalidUTF8` has no effect on output.
pub fn json_marshal<T: MarshalerTo + ?Sized>(input: &T, opts: &[JsonOption]) -> Result<String, JsonError> {
    let mut all: Vec<JsonOption> = ALLOW_INVALID.to_vec();
    all.extend_from_slice(opts);
    let _ = JsonOptions::from_options(&all);
    let mut out = String::new();
    input.marshal_json_to(&mut out)?;
    Ok(out)
}

// Go: json/json.go:23 MarshalEncode
// Go: json/json.go:32 MarshalWrite
// PORT: not ported. Only the LSP, API and build-info writers use them.

// Go: json/json.go:41 MarshalIndent
pub fn json_marshal_indent<T: MarshalerTo + ?Sized>(input: &T, prefix: &str, indent: &str) -> Result<String, JsonError> {
    if prefix.is_empty() && indent.is_empty() {
        // WithIndentPrefix and WithIndent imply multiline output, so skip them.
        return json_marshal(input, &[]);
    }
    unported!("json.MarshalIndent with jsontext.WithIndentPrefix/WithIndent")
}

// Go: json/json.go:49 MarshalIndentWrite
// PORT: not ported. Only test baselines use it.

// Go: json/json.go:57 Unmarshal
// PORT: `out` implements `UnmarshalerFrom` in place of Go reflection. Like
// Go, `out` is not reset on error, and the input must hold exactly one value.
pub fn json_unmarshal<T: UnmarshalerFrom + ?Sized>(input: &[u8], out: &mut T, opts: &[JsonOption]) -> Result<(), JsonError> {
    let mut dec = JsonDecoder::new(input, JsonOptions::from_options(opts));
    json_unmarshal_decode(&mut dec, out)?;
    dec.check_eof()
}

// Go: json/json.go:61 UnmarshalDecode
// PORT: Go merges `opts` into the decoder options; callers here pass none,
// so the decoder options apply. The v2 check that an `UnmarshalerFrom`
// reads exactly one value is kept.
pub fn json_unmarshal_decode<T: UnmarshalerFrom + ?Sized>(dec: &mut JsonDecoder<'_>, out: &mut T) -> Result<(), JsonError> {
    let (prev_depth, prev_len) = dec.depth_length();
    out.unmarshal_json_from(dec)?;
    let (curr_depth, curr_len) = dec.depth_length();
    if prev_depth != curr_depth || prev_len + 1 != curr_len {
        return Err(JsonError::new("must read exactly one JSON value"));
    }
    Ok(())
}

// Go: json/json.go:65 UnmarshalRead
// PORT: not ported. Only the LSP and API readers use it.

// Go: json/json.go:69 AllowDuplicateNames
#[must_use]
pub fn json_allow_duplicate_names(allow: bool) -> JsonOption {
    JsonOption::AllowDuplicateNames(allow)
}

// Go: json/json.go:73 Deterministic
// Go: json/json.go:77 WithIndent
// PORT: not ported. Map output order is only needed by build-info and
// baseline writers, and indentation is not ported (see MarshalIndent).

// Go: json/json.go:81 NewDecoder
// PORT: Go reads from an `io.Reader`; the Rust decoder reads a complete
// buffer with default options.
#[must_use]
pub fn json_new_decoder(r: &[u8]) -> JsonDecoder<'_> {
    JsonDecoder::new(r, JsonOptions::default())
}

// Go: json/json.go:85 type aliases (Value, Kind, UnmarshalerFrom,
// MarshalerTo, Decoder, Encoder) and json/json.go:94 token values
// (BeginObject, EndObject, Null, BeginArray, EndArray).
// PORT: `JsonToken` variants and `JsonToken::kind` stand in for the token
// values. `Value` is `&[u8]`, `Kind` is `u8`, `Decoder` is `JsonDecoder`.
