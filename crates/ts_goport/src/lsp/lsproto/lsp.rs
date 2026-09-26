//! Port of internal/lsp/lsproto/lsp.go.
//!
//! PORT: `DocumentUri`, `URI` and `Method` are Go string types; their JSON
//! impls are the v2 string arshaler. `IndexMap<DocumentUri, V>` (Go
//! `map[DocumentUri]V`) gets the v2 map arshaler here.

use crate::lsp::lsproto::prelude::*;

use crate::frontend::bundled::is_bundled;
use std::marker::PhantomData;

// Go: lsp.go:17 DocumentUri
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DocumentUri(pub String); // !!!

impl DocumentUri {
    // Go: lsp.go:19 FileName
    pub fn file_name(&self) -> String {
        let uri = self.0.as_str();
        if is_bundled(uri) {
            return uri.to_string();
        }
        if uri.starts_with("file://") {
            let parsed = match gostd::url::parse(uri) {
                Ok(parsed) => parsed,
                Err(_) => panic!("invalid file URI: {uri}"),
            };
            if !parsed.host.is_empty() {
                return format!("//{}{}", parsed.host, parsed.path);
            }
            return fix_windows_uri_path(&parsed.path);
        }

        // Leave all other URIs escaped so we can round-trip them.

        let Some((scheme, mut path)) = uri.split_once(':') else {
            panic!("invalid URI: {uri}");
        };

        let mut authority = "ts-nul-authority";
        if let Some(rest) = path.strip_prefix("//") {
            let Some((a, p)) = rest.split_once('/') else {
                panic!("invalid URI: {uri}");
            };
            authority = a;
            path = p;
        }

        format!("^/{scheme}/{authority}/{path}")
    }

    // Go: lsp.go:52 Path
    pub fn path(&self, use_case_sensitive_file_names: bool) -> tspath::Path {
        let file_name = self.file_name();
        tspath::to_path(&file_name, "", use_case_sensitive_file_names)
    }
}

// Go: lsp.go:57 fixWindowsURIPath
pub fn fix_windows_uri_path(path: &str) -> String {
    if let Some(rest) = path.strip_prefix('/') {
        let (volume, rest, ok) = tspath::split_volume_path(rest);
        if ok {
            return volume + rest;
        }
    }
    path.to_string()
}

// Go: lsp.go:66 HasTextDocumentURI
pub trait HasTextDocumentURI {
    fn text_document_uri(&self) -> DocumentUri;
}

// Go: lsp.go:70 HasTextDocumentPosition
pub trait HasTextDocumentPosition: HasTextDocumentURI {
    fn text_document_position(&self) -> Position;
}

// Go: lsp.go:75 HasLocations
pub trait HasLocations {
    fn get_locations(&self) -> Option<&Vec<Location>>;
}

// Go: lsp.go:79 HasLocation
pub trait HasLocation {
    fn get_location(&self) -> Location;
}

// Go: lsp.go:83 URI
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct URI(pub String); // !!!

// Go: lsp.go:85 Method
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Method(pub Cow<'static, str>);

// Go `%s` / `%v` of a string type prints the string.
impl std::fmt::Display for DocumentUri {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::fmt::Display for URI {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::fmt::Display for Method {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

// Go v2 string arshaler for the three string types.
impl MarshalerTo for DocumentUri {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        self.0.marshal_json_to(enc)
    }
}

impl UnmarshalerFrom for DocumentUri {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        self.0.unmarshal_json_from(dec)
    }
}

impl IsZero for DocumentUri {
    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
}

impl MarshalerTo for URI {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        self.0.marshal_json_to(enc)
    }
}

impl UnmarshalerFrom for URI {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        self.0.unmarshal_json_from(dec)
    }
}

impl IsZero for URI {
    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
}

impl MarshalerTo for Method {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        self.0.as_ref().marshal_json_to(enc)
    }
}

impl UnmarshalerFrom for Method {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let mut v = self.0.to_string();
        v.unmarshal_json_from(dec)?;
        self.0 = Cow::Owned(v);
        Ok(())
    }
}

impl IsZero for Method {
    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
}

// Go v2 map arshaler (arshal_default.go:794) for `map[DocumentUri]V`.
// PORT: members write in insertion order; Go map order is random.
impl<V: MarshalerTo> MarshalerTo for IndexMap<DocumentUri, V> {
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

// Go v2 map arshaler (arshal_default.go:955) for `map[DocumentUri]V`: null
// sets nil; an object merges into the existing map (a value for a key that
// is already present decodes into a copy of the old value); a name repeated
// in this object is an error unless duplicates are allowed.
// PORT: Go sets a nil map for null; the Rust zero value is an empty map.
impl<V: UnmarshalerFrom + Default + Clone> UnmarshalerFrom for IndexMap<DocumentUri, V> {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let tok = dec.read_token()?;
        match tok {
            JsonToken::Null => {
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
                let mut seen: Option<FxHashMap<DocumentUri, ()>> = if !allow_dup && !self.is_empty()
                {
                    Some(FxHashMap::default())
                } else {
                    None
                };
                while dec.peek_kind() != b'}' {
                    let mut k = DocumentUri::default();
                    json_unmarshal_decode(dec, &mut k)?;
                    let mut v = V::default();
                    if let Some(existing) = self.get(&k) {
                        if !allow_dup && seen.as_ref().is_none_or(|s| s.contains_key(&k)) {
                            return Err(JsonError {
                                message: format!("duplicate object member name {:?}", k.0),
                            });
                        }
                        v = existing.clone();
                    }
                    let err = json_unmarshal_decode(dec, &mut v);
                    if let Some(s) = &mut seen {
                        s.insert(k.clone(), ());
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
                Err(JsonError {
                    message: "cannot unmarshal JSON value into Go map".to_string(),
                })
            }
        }
    }
}

// Go `%T` of `(*T)(nil)` prints `*lsproto.Name`.
// PORT: the Rust type name without module paths; types from lsproto get
// the `lsproto.` package prefix, other types (`Vec<..>`) print as Rust.
fn go_type_name<T: ?Sized>() -> String {
    let full = std::any::type_name::<T>();
    let mut out = String::new();
    let mut ident = String::new();
    for c in full.chars() {
        if c.is_alphanumeric() || c == '_' || c == ':' {
            ident.push(c);
        } else {
            out.push_str(ident.rsplit("::").next().unwrap_or(""));
            ident.clear();
            out.push(c);
        }
    }
    out.push_str(ident.rsplit("::").next().unwrap_or(""));
    if full.contains("::lsproto::") && !full.contains('<') {
        return format!("lsproto.{out}");
    }
    out
}

// Go: lsp.go:87 unmarshalPtrTo
pub fn unmarshal_ptr_to<T: UnmarshalerFrom + Default>(data: &[u8]) -> Result<Box<T>, GoError> {
    let mut v = T::default();
    if let Err(err) = json_unmarshal(data, &mut v, &[]) {
        let err = gostd::errors::from_value(err);
        return Err(gostd::errors::errorf(
            format!(
                "failed to unmarshal *{}: {}",
                go_type_name::<T>(),
                err.error()
            ),
            vec![err],
        ));
    }
    Ok(Box::new(v))
}

// Go: lsp.go:95 unmarshalValue
pub fn unmarshal_value<T: UnmarshalerFrom + Default>(data: &[u8]) -> Result<T, GoError> {
    let mut v = T::default();
    if let Err(err) = json_unmarshal(data, &mut v, &[]) {
        let err = gostd::errors::from_value(err);
        return Err(gostd::errors::errorf(
            format!(
                "failed to unmarshal *{}: {}",
                go_type_name::<T>(),
                err.error()
            ),
            vec![err],
        ));
    }
    Ok(v)
}

// Go: lsp.go:103 unmarshalAny
// PORT: Go `any` is `Option<Box<dyn AnyValue>>`; a JSON null leaves it nil
// (`None`), any other value is a boxed `LspAny`.
pub fn unmarshal_any(data: &[u8]) -> Result<Option<Box<dyn AnyValue>>, GoError> {
    let mut v = LspAny::Null;
    if let Err(err) = json_unmarshal(data, &mut v, &[]) {
        let err = gostd::errors::from_value(err);
        return Err(gostd::errors::errorf(
            format!("failed to unmarshal any: {}", err.error()),
            vec![err],
        ));
    }
    if v == LspAny::Null {
        return Ok(None);
    }
    Ok(Some(Box::new(v)))
}

// Go: lsp.go:111 unmarshalEmpty
pub fn unmarshal_empty(data: &[u8]) -> Result<Option<Box<dyn AnyValue>>, GoError> {
    if !data.is_empty() {
        return Err(gostd::errors::new(format!(
            "expected empty, got: {}",
            String::from_utf8_lossy(data)
        )));
    }
    Ok(None)
}

// Go: lsp.go:118 boolToInt
pub fn bool_to_int(b: bool) -> i32 {
    if b {
        return 1;
    }
    0
}

// Go `%v` of a `jsontext.Kind` (jsontext/token.go:643 Kind.String).
fn json_kind_string(k: u8) -> String {
    match k {
        0 => "invalid".to_string(),
        b'n' => "null".to_string(),
        b'f' => "false".to_string(),
        b't' => "true".to_string(),
        b'"' => "string".to_string(),
        b'0' => "number".to_string(),
        b'{' => "{".to_string(),
        b'}' => "}".to_string(),
        b'[' => "[".to_string(),
        b']' => "]".to_string(),
        _ => format!("<invalid jsontext.Kind: {}>", quote_rune(&[k])),
    }
}

// Go: lsp.go:125 errNotObject
pub fn err_not_object(k: u8) -> JsonError {
    JsonError {
        message: format!(
            "expected object start, but encountered {}",
            json_kind_string(k)
        ),
    }
}

// Go: lsp.go:129 errNull
pub fn err_null(field: &str) -> JsonError {
    JsonError {
        message: format!(
            "null value is not allowed for field {}",
            gostd::strconv::quote(field)
        ),
    }
}

// Go: lsp.go:133 errMissing
pub fn err_missing<I, S>(props: I) -> JsonError
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    let props: Vec<String> = props.into_iter().map(|p| p.as_ref().to_string()).collect();
    JsonError {
        message: format!("missing required properties: {}", props.join(", ")),
    }
}

// Go: lsp.go:137 errInvalidKind
pub fn err_invalid_kind(type_name: &str, got: u8) -> JsonError {
    JsonError {
        message: format!("invalid {}: got {}", type_name, json_kind_string(got)),
    }
}

// Go: lsp.go:141 errInvalidValue
pub fn err_invalid_value(type_name: &str, data: impl AsRef<[u8]>) -> JsonError {
    JsonError {
        message: format!(
            "invalid {}: {}",
            type_name,
            String::from_utf8_lossy(data.as_ref())
        ),
    }
}

// Go: lsp.go:145 errLiteralMismatch
pub fn err_literal_mismatch(type_name: &str, expected: &str, got: impl AsRef<[u8]>) -> JsonError {
    JsonError {
        message: format!(
            "expected {} value {}, got {}",
            type_name,
            expected,
            String::from_utf8_lossy(got.as_ref())
        ),
    }
}

// Go: lsp.go:149 assertOnlyOne
pub fn assert_only_one(message: &str, count: i32) {
    if count != 1 {
        panic!("{message}");
    }
}

// Go: lsp.go:155 assertAtMostOne
pub fn assert_at_most_one(message: &str, count: i32) {
    if count > 1 {
        panic!("{message}");
    }
}

// Go: lsp.go:162 jsonKeyCheck
// jsonKeyCheck compares a raw JSON key token (including quotes) against a Go string.
pub fn json_key_check(name: &[u8], key: &str) -> bool {
    name.len() == key.len() + 2 && name[0] == b'"' && &name[1..name.len() - 1] == key.as_bytes()
}

// Go: lsp.go:169 jsonObjectRawField
// jsonObjectRawField scans the top-level keys of a JSON object looking for the
// given field name, and returns its raw JSON value (e.g. `"full"` with quotes).
// Returns nil if the field is not found.
pub fn json_object_raw_field(data: &[u8], field: &str) -> JsonValue {
    let mut dec = json_new_decoder(data);
    if dec.peek_kind() != b'{' {
        return JsonValue::default();
    }
    if dec.read_token().is_err() {
        return JsonValue::default();
    }
    while dec.peek_kind() != b'}' {
        let Ok(name) = dec.read_value() else {
            return JsonValue::default();
        };
        if json_key_check(name, field) {
            let Ok(val) = dec.read_value() else {
                return JsonValue::default();
            };
            return JsonValue(val.to_vec());
        }
        if dec.skip_value().is_err() {
            return JsonValue::default();
        }
    }
    JsonValue::default()
}

// Go: lsp.go:199 jsonObjectHasKey
// jsonObjectHasKey scans the top-level keys of a JSON object looking for any of the
// given keys. Returns the index of the first key found, or -1 if none match.
// Bails early on first match without decoding any values.
pub fn json_object_has_key(data: &[u8], keys: &[&str]) -> i32 {
    let mut dec = json_new_decoder(data);
    if dec.peek_kind() != b'{' {
        return -1;
    }
    if dec.read_token().is_err() {
        return -1;
    }
    while dec.peek_kind() != b'}' {
        let Ok(name) = dec.read_value() else {
            return -1;
        };
        for (i, key) in keys.iter().enumerate() {
            if json_key_check(name, key) {
                return i as i32;
            }
        }
        if dec.skip_value().is_err() {
            return -1;
        }
    }
    -1
}

// Inspired by https://www.youtube.com/watch?v=dab3I-HcTVk

// Go: lsp.go:226 RequestInfo
// PORT: Go `_ [0]Params` / `_ [0]Resp` are `PhantomData`. Go builds the
// value with a struct literal; `new` is the const constructor the
// generated `*_INFO` consts use.
pub struct RequestInfo<P, R> {
    _params: PhantomData<fn() -> P>,
    _resp: PhantomData<fn() -> R>,
    pub method: Method,
}

impl<P, R> RequestInfo<P, R> {
    pub const fn new(method: Method) -> RequestInfo<P, R> {
        RequestInfo {
            _params: PhantomData,
            _resp: PhantomData,
            method,
        }
    }
}

impl<P, R: 'static> RequestInfo<P, R> {
    // Go: lsp.go:232 UnmarshalResult
    // PORT: Go type assertions on `any`. `None` is a nil `any`. `%T` in the
    // error prints the Rust debug value.
    pub fn unmarshal_result(&self, result: Option<Box<dyn AnyValue>>) -> Result<R, GoError> {
        let Some(result) = result else {
            return Err(gostd::errors::new("expected json.Value, got <nil>"));
        };
        if result.downcast_ref::<R>().is_some() {
            let result: Box<dyn std::any::Any> = result;
            return Ok(*result.downcast::<R>().expect("checked by downcast_ref"));
        }

        let Some(raw) = result.downcast_ref::<JsonValue>() else {
            return Err(gostd::errors::new(format!(
                "expected json.Value, got {result:?}"
            )));
        };

        let r = unmarshal_result(&self.method, &raw.0)?;
        let Some(r) = r else {
            panic!(
                "interface conversion: interface {{}} is nil, not {}",
                std::any::type_name::<R>()
            );
        };
        let r: Box<dyn std::any::Any> = r;
        match r.downcast::<R>() {
            Ok(r) => Ok(*r),
            Err(_) => panic!(
                "interface conversion: interface {{}} is not {}",
                std::any::type_name::<R>()
            ),
        }
    }
}

impl<P: AnyValue, R> RequestInfo<P, R> {
    // Go: lsp.go:249 NewRequestMessage
    pub fn new_request_message(&self, id: Option<crate::jsonrpc::ID>, params: P) -> RequestMessage {
        RequestMessage {
            id,
            method: self.method.clone(),
            params: Some(Box::new(params)),
            ..RequestMessage::default()
        }
    }
}

impl<P, R> Clone for RequestInfo<P, R> {
    fn clone(&self) -> Self {
        RequestInfo::new(self.method.clone())
    }
}

impl<P, R> std::fmt::Debug for RequestInfo<P, R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RequestInfo")
            .field("method", &self.method)
            .finish()
    }
}

// Go: lsp.go:257 NotificationInfo
pub struct NotificationInfo<P> {
    _params: PhantomData<fn() -> P>,
    pub method: Method,
}

impl<P> NotificationInfo<P> {
    pub const fn new(method: Method) -> NotificationInfo<P> {
        NotificationInfo {
            _params: PhantomData,
            method,
        }
    }
}

impl<P: AnyValue> NotificationInfo<P> {
    // Go: lsp.go:262 NewNotificationMessage
    pub fn new_notification_message(&self, params: P) -> RequestMessage {
        RequestMessage {
            method: self.method.clone(),
            params: Some(Box::new(params)),
            ..RequestMessage::default()
        }
    }
}

impl<P> Clone for NotificationInfo<P> {
    fn clone(&self) -> Self {
        NotificationInfo::new(self.method.clone())
    }
}

impl<P> std::fmt::Debug for NotificationInfo<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NotificationInfo")
            .field("method", &self.method)
            .finish()
    }
}

// Go: lsp.go:269 Null
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Null;

// Go: lsp.go:271 (Null) UnmarshalJSONFrom
impl UnmarshalerFrom for Null {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let data = dec.read_value()?;
        if data != b"null" {
            return Err(JsonError {
                message: format!("expected null, got {}", String::from_utf8_lossy(data)),
            });
        }
        Ok(())
    }
}

// Go: lsp.go:282 (Null) MarshalJSONTo
impl MarshalerTo for Null {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        enc.push_str("null");
        Ok(())
    }
}

// Go reflect: an empty struct is always zero.
impl IsZero for Null {
    fn is_zero(&self) -> bool {
        true
    }
}

// Go: lsp.go:286 NoParams
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NoParams;

// Go: lsp.go:288 (NoParams) IsZero
impl IsZero for NoParams {
    fn is_zero(&self) -> bool {
        true
    }
}

// Go v2 default struct arshaler for `struct{}`: `{}`.
impl MarshalerTo for NoParams {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        write_object_end(enc);
        Ok(())
    }
}

// Go v2 default struct arshaler for `struct{}`: null or an object (members
// skipped); any other kind is an error.
impl UnmarshalerFrom for NoParams {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        unmarshal_struct_fields(dec, "lsproto.NoParams", |_, _| Ok(false))?;
        Ok(())
    }
}

// Go: lsp.go:290 clientCapabilitiesKey
static CLIENT_CAPABILITIES_KEY: gostd::context::ContextKey<Arc<ResolvedClientCapabilities>> =
    gostd::context::ContextKey::new("clientCapabilitiesKey");

// Go: lsp.go:292 WithClientCapabilities
// PORT: Go stores the `*ResolvedClientCapabilities` pointer; the context
// holds an `Arc` to it.
pub fn with_client_capabilities(ctx: &Context, caps: Arc<ResolvedClientCapabilities>) -> Context {
    gostd::context::with_value(ctx, &CLIENT_CAPABILITIES_KEY, caps)
}

// Go: lsp.go:296 GetClientCapabilities
pub fn get_client_capabilities(ctx: &Context) -> Arc<ResolvedClientCapabilities> {
    if let Some(caps) = ctx.value(&CLIENT_CAPABILITIES_KEY) {
        return (*caps).clone();
    }
    Arc::new(ResolvedClientCapabilities::default())
}

// Go: lsp.go:305 PreferredMarkupKind
// PreferredMarkupKind returns the first (most preferred) markup kind from the given formats,
// or MarkupKindPlainText if the slice is empty.
pub fn preferred_markup_kind(formats: &[MarkupKind]) -> MarkupKind {
    if !formats.is_empty() {
        return formats[0].clone();
    }
    MarkupKind::PLAIN_TEXT
}

// Go: lsp.go:312
impl CodeActionKind {
    pub const SOURCE_REMOVE_UNUSED_IMPORTS: CodeActionKind =
        CodeActionKind(Cow::Borrowed("source.removeUnusedImports"));
    pub const SOURCE_SORT_IMPORTS: CodeActionKind =
        CodeActionKind(Cow::Borrowed("source.sortImports"));
}
