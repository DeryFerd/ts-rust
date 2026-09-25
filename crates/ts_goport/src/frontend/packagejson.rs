//! Port of packagejson/jsonvalue.go, expected.go, exportsorimports.go,
//! validated.go, packagejson.go and cache.go.
//!
//! PORT: Go decodes package.json with JSON v2 reflection. Here each Go type
//! implements `UnmarshalerFrom` (see `json.rs`) with the same v2 semantics:
//! - `Parse` sets `AllowDuplicateNames(true)`, so for a duplicate member the
//!   field is decoded again into the same Go value (the last one wins, with
//!   the Go merge quirks kept: `Expected.Valid` is never reset, and a scalar
//!   `JSONValue` of a different JSON kind is a fatal error).
//! - Every v2 error is fatal. `Parse` then returns zero `Fields` and the
//!   error. The resolver stores such a file with `Parseable == false` and
//!   empty fields, so an invalid file acts like a file with no fields.
//! - Go `any` in `JSONValue.Value` is the `JsonAny` enum.
//! - Go `*collections.OrderedMap` is `Rc<IndexMap>`. Go slices and pointers
//!   share their data on copy, so `Rc` keeps that.

use crate::frontend::prelude::*;
use std::cell::OnceCell;
use std::sync::LazyLock;
use ts_diagnostics::Message;

// ---------------------------------------------------------------------------
// jsonvalue.go
// ---------------------------------------------------------------------------

// Go: jsonvalue.go:10 JSONValueType
// PORT: a newtype with associated consts so it works in `match` patterns.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct JSONValueType(pub i8);

impl JSONValueType {
    pub const NOT_PRESENT: JSONValueType = JSONValueType(0);
    pub const NULL: JSONValueType = JSONValueType(1);
    pub const STRING: JSONValueType = JSONValueType(2);
    pub const NUMBER: JSONValueType = JSONValueType(3);
    pub const BOOLEAN: JSONValueType = JSONValueType(4);
    pub const ARRAY: JSONValueType = JSONValueType(5);
    pub const OBJECT: JSONValueType = JSONValueType(6);

    // Go: jsonvalue.go:22 String
    #[must_use]
    pub fn string(self) -> String {
        match self {
            JSONValueType::NULL => "null".to_string(),
            JSONValueType::STRING => "string".to_string(),
            JSONValueType::NUMBER => "number".to_string(),
            JSONValueType::BOOLEAN => "boolean".to_string(),
            JSONValueType::ARRAY => "array".to_string(),
            JSONValueType::OBJECT => "object".to_string(),
            JSONValueType(t) => format!("unknown({t})"),
        }
    }
}

// PORT: Go `fmt.Stringer`, so `args!` can format the type.
impl std::fmt::Display for JSONValueType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.string())
    }
}

/// Go `any` stored in `JSONValue.Value`.
/// PORT: `Array` and `Object` hold `[]JSONValue` and
/// `*OrderedMap[string, JSONValue]`. `ExportsArray` and `ExportsObject` hold
/// the `ExportsOrImports` forms that `unmarshalJSONValueV2[ExportsOrImports]`
/// stores.
#[derive(Clone, Debug, Default)]
pub enum JsonAny {
    #[default]
    Nil,
    String(String),
    Number(f64),
    Bool(bool),
    Array(Rc<Vec<JSONValue>>),
    Object(Rc<IndexMap<String, JSONValue>>),
    ExportsArray(Rc<Vec<ExportsOrImports>>),
    ExportsObject(Rc<IndexMap<String, ExportsOrImports>>),
}

// Go: jsonvalue.go:41 JSONValue
#[derive(Clone, Debug, Default)]
pub struct JSONValue {
    pub type_: JSONValueType,
    pub value: JsonAny,
}

impl JSONValue {
    // Go: jsonvalue.go:46 IsPresent
    #[must_use]
    pub fn is_present(&self) -> bool {
        self.type_ != JSONValueType::NOT_PRESENT
    }

    // Go: jsonvalue.go:50 IsFalsy
    #[must_use]
    pub fn is_falsy(&self) -> bool {
        match self.type_ {
            JSONValueType::NOT_PRESENT | JSONValueType::NULL => true,
            JSONValueType::STRING => matches!(&self.value, JsonAny::String(s) if s.is_empty()),
            // PORT: Go `v.Value == 0` compares `any(float64)` with `any(int)`.
            // The dynamic types differ, so a number is never falsy in Go.
            JSONValueType::NUMBER => false,
            JSONValueType::BOOLEAN => match &self.value {
                JsonAny::Bool(b) => !b,
                _ => panic!("interface conversion: interface {{}} is not bool"),
            },
            _ => false,
        }
    }

    // Go: jsonvalue.go:65 AsObject
    #[must_use]
    pub fn as_object(&self) -> &IndexMap<String, JSONValue> {
        if self.type_ != JSONValueType::OBJECT {
            panic!("expected object, got {}", self.type_.string());
        }
        match &self.value {
            JsonAny::Object(o) => o,
            _ => panic!("interface conversion: value is not *OrderedMap[string, JSONValue]"),
        }
    }

    // Go: jsonvalue.go:72 AsArray
    #[must_use]
    pub fn as_array(&self) -> &[JSONValue] {
        if self.type_ != JSONValueType::ARRAY {
            panic!("expected array, got {}", self.type_.string());
        }
        match &self.value {
            JsonAny::Array(a) => a,
            _ => panic!("interface conversion: value is not []JSONValue"),
        }
    }

    // Go: jsonvalue.go:79 AsString
    #[must_use]
    pub fn as_string(&self) -> &str {
        if self.type_ != JSONValueType::STRING {
            panic!("expected string, got {}", self.type_.string());
        }
        match &self.value {
            JsonAny::String(s) => s,
            _ => panic!("interface conversion: value is not string"),
        }
    }
}

// Go: jsonvalue.go:88 UnmarshalJSONFrom
impl UnmarshalerFrom for JSONValue {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        unmarshal_json_value_v2::<JSONValue>(self, dec)
    }
}

// Go: jsonvalue.go:92 unmarshalJSONValue
// PORT: not ported. It has no callers in Go; only the v2 form is used.

/// Element types of `unmarshalJSONValueV2[T]`.
/// PORT: stands in for storing `[]T` and `*OrderedMap[string, T]` in `any`.
pub trait JsonValueElement: UnmarshalerFrom + Default + Sized {
    fn wrap_array(elements: Vec<Self>) -> JsonAny;
    fn wrap_object(object: IndexMap<String, Self>) -> JsonAny;
}

impl JsonValueElement for JSONValue {
    fn wrap_array(elements: Vec<Self>) -> JsonAny {
        JsonAny::Array(Rc::new(elements))
    }
    fn wrap_object(object: IndexMap<String, Self>) -> JsonAny {
        JsonAny::Object(Rc::new(object))
    }
}

impl JsonValueElement for ExportsOrImports {
    fn wrap_array(elements: Vec<Self>) -> JsonAny {
        JsonAny::ExportsArray(Rc::new(elements))
    }
    fn wrap_object(object: IndexMap<String, Self>) -> JsonAny {
        JsonAny::ExportsObject(Rc::new(object))
    }
}

// Go: jsonvalue.go:125 unmarshalJSONValueV2
fn unmarshal_json_value_v2<T: JsonValueElement>(v: &mut JSONValue, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
    match dec.peek_kind() {
        b'n' => {
            // json.Null.Kind()
            dec.read_token()?;
            v.value = JsonAny::Nil;
            v.type_ = JSONValueType::NULL;
            return Ok(());
        }
        b'"' => {
            v.type_ = JSONValueType::STRING;
            unmarshal_any(dec, &mut v.value)?;
        }
        b'[' => {
            dec.read_token()?;
            let mut elements: Vec<T> = Vec::new();
            while dec.peek_kind() != b']' {
                let mut element = T::default();
                json_unmarshal_decode(dec, &mut element)?;
                elements.push(element);
            }
            dec.read_token()?;
            v.type_ = JSONValueType::ARRAY;
            v.value = T::wrap_array(elements);
        }
        b'{' => {
            let mut object: IndexMap<String, T> = IndexMap::new();
            json_unmarshal_decode(dec, &mut object)?;
            v.type_ = JSONValueType::OBJECT;
            v.value = T::wrap_object(object);
        }
        b't' | b'f' => {
            // json.True.Kind(), json.False.Kind()
            v.type_ = JSONValueType::BOOLEAN;
            unmarshal_any(dec, &mut v.value)?;
        }
        _ => {
            v.type_ = JSONValueType::NUMBER;
            unmarshal_any(dec, &mut v.value)?;
        }
    }
    Ok(())
}

// PORT: the JSON v2 interface arshaler for `json.UnmarshalDecode(dec, &v.Value)`
// with `v.Value` of type `any`. `unmarshalJSONValueV2` handles null, objects
// and arrays itself, so only scalars reach here. A nil value picks the Go
// type from the JSON kind. A non-nil value (from an earlier duplicate
// member) keeps its Go type, so a different JSON kind is an error.
fn unmarshal_any(dec: &mut JsonDecoder<'_>, value: &mut JsonAny) -> Result<(), JsonError> {
    if dec.peek_kind() == b'n' {
        dec.read_token()?;
        *value = JsonAny::Nil;
        return Ok(());
    }
    match value {
        JsonAny::Nil => match dec.peek_kind() {
            b't' | b'f' => {
                let mut b = false;
                let err = b.unmarshal_json_from(dec);
                *value = JsonAny::Bool(b);
                err
            }
            b'"' => {
                let mut s = String::new();
                let err = s.unmarshal_json_from(dec);
                *value = JsonAny::String(s);
                err
            }
            b'0' => {
                let mut n = 0.0;
                let err = n.unmarshal_json_from(dec);
                *value = JsonAny::Number(n);
                err
            }
            b'{' | b'[' => unreachable!("unmarshalJSONValueV2 decodes objects and arrays itself"),
            _ => {
                // An invalid kind: ReadValue reports the syntax error.
                dec.read_value()?;
                Err(JsonError { message: "invalid JSON value".to_string() })
            }
        },
        JsonAny::String(s) => s.unmarshal_json_from(dec),
        JsonAny::Bool(b) => b.unmarshal_json_from(dec),
        JsonAny::Number(n) => n.unmarshal_json_from(dec),
        JsonAny::Array(_) | JsonAny::ExportsArray(_) | JsonAny::Object(_) | JsonAny::ExportsObject(_) => {
            // The slice arshaler and `OrderedMap.UnmarshalJSONFrom` both
            // reject a scalar after they consume it.
            dec.skip_value()?;
            Err(JsonError { message: "cannot unmarshal JSON scalar into existing array or object".to_string() })
        }
    }
}

// Go: collections/ordered_map.go:263 (*OrderedMap).UnmarshalJSONFrom
// PORT: Go `collections.OrderedMap` is `IndexMap`. `IndexMap::insert` keeps
// the first position and replaces the value, like `OrderedMap.Set`. This
// impl lives here because packagejson is its only decode user.
impl<V: UnmarshalerFrom + Default> UnmarshalerFrom for IndexMap<String, V> {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let token = dec.read_token()?;
        if token.kind() == b'n' {
            // By convention, to approximate the behavior of Unmarshal itself,
            // Unmarshalers implement UnmarshalJSON([]byte("null")) as a no-op.
            return Ok(());
        }
        if token.kind() != b'{' {
            return Err(JsonError { message: "cannot unmarshal non-object JSON value into Map".to_string() });
        }
        while dec.peek_kind() != b'}' {
            let mut key = String::new();
            let mut value = V::default();
            json_unmarshal_decode(dec, &mut key)?;
            json_unmarshal_decode(dec, &mut value)?;
            self.insert(key, value);
        }
        dec.read_token()?;
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// expected.go
// ---------------------------------------------------------------------------

/// The Go `reflect.Kind` of `T` in `Expected[T].ExpectedJSONType`.
/// PORT: a trait in place of reflection.
pub trait ExpectedJsonKind {
    const JSON_TYPE: &'static str;
}

impl ExpectedJsonKind for String {
    const JSON_TYPE: &'static str = "string";
}
impl ExpectedJsonKind for bool {
    const JSON_TYPE: &'static str = "boolean";
}
impl<T> ExpectedJsonKind for Vec<T> {
    const JSON_TYPE: &'static str = "array";
}
impl<V> ExpectedJsonKind for FxHashMap<String, V> {
    const JSON_TYPE: &'static str = "object";
}
impl ExpectedJsonKind for i32 {
    const JSON_TYPE: &'static str = "number";
}
impl ExpectedJsonKind for i64 {
    const JSON_TYPE: &'static str = "number";
}
impl ExpectedJsonKind for u32 {
    const JSON_TYPE: &'static str = "number";
}
impl ExpectedJsonKind for u64 {
    const JSON_TYPE: &'static str = "number";
}
// Go `reflect.Float64` falls to the "unknown" default.
impl ExpectedJsonKind for f64 {
    const JSON_TYPE: &'static str = "unknown";
}

// Go: expected.go:9 Expected
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Expected<T> {
    // PORT: Go `string`; every value is a literal.
    actual_json_type: &'static str,
    pub null: bool,
    pub valid: bool,
    pub value: T,
}

impl<T: UnmarshalerFrom + ExpectedJsonKind + Default + Clone> Expected<T> {
    // Go: expected.go:16 UnmarshalJSON
    // PORT: never fails, like Go. `data` is one complete JSON value.
    pub fn unmarshal_json(&mut self, data: &[u8]) {
        if data == b"null" {
            *self = Expected { null: true, actual_json_type: "null", valid: false, value: T::default() };
            return;
        }
        if json_unmarshal(data, &mut self.value, &[]).is_ok() {
            self.valid = true;
        }
        self.actual_json_type = match data[0] {
            b'"' => "string",
            b't' | b'f' => "boolean",
            b'[' => "array",
            b'{' => "object",
            _ => "number",
        };
    }

    // Go: expected.go:39 IsPresent
    #[must_use]
    pub fn is_present(&self) -> bool {
        !self.actual_json_type.is_empty()
    }

    // Go: expected.go:43 GetValue
    #[must_use]
    pub fn get_value(&self) -> (T, bool) {
        (self.value.clone(), self.valid)
    }

    // Go: expected.go:47 IsValid
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.valid
    }

    // Go: expected.go:51 ExpectedJSONType
    #[must_use]
    pub fn expected_json_type(&self) -> &'static str {
        T::JSON_TYPE
    }

    // Go: expected.go:69 ActualJSONType
    #[must_use]
    pub fn actual_json_type(&self) -> &'static str {
        self.actual_json_type
    }
}

// PORT: JSON v2 calls a v1 `UnmarshalJSON` method with the raw bytes of the
// next value.
impl<T: UnmarshalerFrom + ExpectedJsonKind + Default + Clone> UnmarshalerFrom for Expected<T> {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        let data = dec.read_value()?;
        self.unmarshal_json(data);
        Ok(())
    }
}

// Go: expected.go:73 ExpectedOf
#[must_use]
pub fn expected_of<T: ExpectedJsonKind>(value: T) -> Expected<T> {
    Expected { value, valid: true, actual_json_type: T::JSON_TYPE, null: false }
}

// ---------------------------------------------------------------------------
// exportsorimports.go
// ---------------------------------------------------------------------------

// Go: exportsorimports.go:8 objectKind
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
enum ObjectKind {
    #[default]
    Unknown,
    Subpaths,
    Conditions,
    Imports,
    Invalid,
}

// Go: exportsorimports.go:18 ExportsOrImports
// PORT: Go embeds `JSONValue`. It is the `json_value` field plus `Deref`.
#[derive(Clone, Debug, Default)]
pub struct ExportsOrImports {
    pub json_value: JSONValue,
    object_kind: ObjectKind,
}

impl std::ops::Deref for ExportsOrImports {
    type Target = JSONValue;
    fn deref(&self) -> &JSONValue {
        &self.json_value
    }
}

// Go: exportsorimports.go:25 UnmarshalJSONFrom
impl UnmarshalerFrom for ExportsOrImports {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        unmarshal_json_value_v2::<ExportsOrImports>(&mut self.json_value, dec)
    }
}

impl ExportsOrImports {
    // Go: exportsorimports.go:29 AsObject
    #[must_use]
    pub fn as_object(&self) -> &IndexMap<String, ExportsOrImports> {
        if self.json_value.type_ != JSONValueType::OBJECT {
            panic!("expected object");
        }
        match &self.json_value.value {
            JsonAny::ExportsObject(o) => o,
            _ => panic!("interface conversion: value is not *OrderedMap[string, ExportsOrImports]"),
        }
    }

    // Go: exportsorimports.go:36 AsArray
    #[must_use]
    pub fn as_array(&self) -> &[ExportsOrImports] {
        if self.json_value.type_ != JSONValueType::ARRAY {
            panic!("expected array");
        }
        match &self.json_value.value {
            JsonAny::ExportsArray(a) => a,
            _ => panic!("interface conversion: value is not []ExportsOrImports"),
        }
    }

    // PORT: Go `IsSubpaths`, `IsImports` and `IsConditions` have value
    // receivers, so `initObjectKind` runs on a copy and the result is never
    // cached. This helper does the same on a local copy.
    fn object_kind_of_copy(&self) -> ObjectKind {
        let mut e = self.clone();
        e.init_object_kind();
        e.object_kind
    }

    // Go: exportsorimports.go:43 IsSubpaths
    #[must_use]
    pub fn is_subpaths(&self) -> bool {
        self.object_kind_of_copy() == ObjectKind::Subpaths
    }

    // Go: exportsorimports.go:48 IsImports
    #[must_use]
    pub fn is_imports(&self) -> bool {
        self.object_kind_of_copy() == ObjectKind::Imports
    }

    // Go: exportsorimports.go:53 IsConditions
    #[must_use]
    pub fn is_conditions(&self) -> bool {
        self.object_kind_of_copy() == ObjectKind::Conditions
    }

    // Go: exportsorimports.go:58 initObjectKind
    fn init_object_kind(&mut self) {
        if self.object_kind == ObjectKind::Unknown && self.json_value.type_ == JSONValueType::OBJECT {
            let obj = self.as_object();
            if !obj.is_empty() {
                let (mut seen_dot, mut seen_hash, mut seen_other) = (false, false, false);
                for k in obj.keys() {
                    if let Some(&c) = k.as_bytes().first() {
                        seen_dot = seen_dot || c == b'.';
                        seen_hash = seen_hash || c == b'#';
                        seen_other = seen_other || (c != b'.' && c != b'#');
                        if seen_other && (seen_dot || seen_hash) {
                            self.object_kind = ObjectKind::Invalid;
                            return;
                        }
                    }
                }
                if seen_dot {
                    self.object_kind = ObjectKind::Subpaths;
                    return;
                }
                if seen_hash {
                    self.object_kind = ObjectKind::Imports;
                    return;
                }
            }
            self.object_kind = ObjectKind::Conditions;
        }
    }
}

// ---------------------------------------------------------------------------
// validated.go
// ---------------------------------------------------------------------------

// Go: validated.go:3 TypeValidatedField
pub trait TypeValidatedField {
    fn is_present(&self) -> bool;
    fn is_valid(&self) -> bool;
    fn expected_json_type(&self) -> &'static str;
    fn actual_json_type(&self) -> &'static str;
}

impl<T: UnmarshalerFrom + ExpectedJsonKind + Default + Clone> TypeValidatedField for Expected<T> {
    fn is_present(&self) -> bool {
        Expected::is_present(self)
    }
    fn is_valid(&self) -> bool {
        Expected::is_valid(self)
    }
    fn expected_json_type(&self) -> &'static str {
        Expected::expected_json_type(self)
    }
    fn actual_json_type(&self) -> &'static str {
        Expected::actual_json_type(self)
    }
}

// ---------------------------------------------------------------------------
// packagejson.go
// ---------------------------------------------------------------------------

// Go: packagejson.go:8 HeaderFields
#[derive(Clone, Debug, Default)]
pub struct HeaderFields {
    pub name: Expected<String>,
    pub version: Expected<String>,
    pub type_: Expected<String>,
}

// Go: packagejson.go:14 PathFields
#[derive(Clone, Debug, Default)]
pub struct PathFields {
    pub ts_config: Expected<String>,
    pub main: Expected<String>,
    pub types: Expected<String>,
    pub typings: Expected<String>,
    pub types_versions: JSONValue,
    pub imports: ExportsOrImports,
    pub exports: ExportsOrImports,
}

// Go: packagejson.go:24 DependencyFields
#[derive(Clone, Debug, Default)]
pub struct DependencyFields {
    pub dependencies: Expected<FxHashMap<String, String>>,
    pub dev_dependencies: Expected<FxHashMap<String, String>>,
    pub peer_dependencies: Expected<FxHashMap<String, String>>,
    pub optional_dependencies: Expected<FxHashMap<String, String>>,
}

impl DependencyFields {
    // Go: packagejson.go:34 HasDependency
    // HasDependency returns true if the package.json has a dependency with the given name
    // under any of the dependency fields (dependencies, devDependencies, peerDependencies,
    // optionalDependencies).
    #[must_use]
    pub fn has_dependency(&self, name: &str) -> bool {
        if self.dependencies.valid && self.dependencies.value.contains_key(name) {
            return true;
        }
        if self.dev_dependencies.valid && self.dev_dependencies.value.contains_key(name) {
            return true;
        }
        if self.peer_dependencies.valid && self.peer_dependencies.value.contains_key(name) {
            return true;
        }
        if self.optional_dependencies.valid && self.optional_dependencies.value.contains_key(name) {
            return true;
        }
        false
    }

    // Go: packagejson.go:58 RangeDependencies
    // PORT: Go map iteration order is random; `FxHashMap` order is arbitrary.
    pub fn range_dependencies(&self, mut f: impl FnMut(&str, &str, &str) -> bool) {
        let fields = [
            (&self.dependencies, "dependencies"),
            (&self.dev_dependencies, "devDependencies"),
            (&self.peer_dependencies, "peerDependencies"),
            (&self.optional_dependencies, "optionalDependencies"),
        ];
        for (field, field_name) in fields {
            if field.valid {
                for (name, version) in &field.value {
                    if !f(name, version, field_name) {
                        return;
                    }
                }
            }
        }
    }

    // Go: packagejson.go:89 GetRuntimeDependencyNames
    // PORT: Go ignores `ok`, so a map that failed validation part way still
    // counts. `collections.Set` is `FxHashSet`.
    #[must_use]
    pub fn get_runtime_dependency_names(&self) -> FxHashSet<String> {
        let deps = &self.dependencies.value;
        let peer_deps = &self.peer_dependencies.value;
        let opt_deps = &self.optional_dependencies.value;
        let count = deps.len() + peer_deps.len() + opt_deps.len();
        let mut names = FxHashSet::default();
        names.reserve(count);
        for name in deps.keys() {
            names.insert(name.clone());
        }
        for name in peer_deps.keys() {
            names.insert(name.clone());
        }
        for name in opt_deps.keys() {
            names.insert(name.clone());
        }
        names
    }
}

// Go: packagejson.go:110 Fields
// PORT: Go embeds the three field groups. They are nested fields here, and
// the promoted `DependencyFields` methods forward below.
#[derive(Clone, Debug, Default)]
pub struct Fields {
    pub header_fields: HeaderFields,
    pub path_fields: PathFields,
    pub dependency_fields: DependencyFields,
}

impl Fields {
    // PORT: promoted from the embedded `DependencyFields`.
    #[must_use]
    pub fn has_dependency(&self, name: &str) -> bool {
        self.dependency_fields.has_dependency(name)
    }

    // PORT: promoted from the embedded `DependencyFields`.
    pub fn range_dependencies(&self, f: impl FnMut(&str, &str, &str) -> bool) {
        self.dependency_fields.range_dependencies(f);
    }

    // PORT: promoted from the embedded `DependencyFields`.
    #[must_use]
    pub fn get_runtime_dependency_names(&self) -> FxHashSet<String> {
        self.dependency_fields.get_runtime_dependency_names()
    }
}

// PORT: the JSON v2 struct arshaler for `Fields` with its `json:"..."` tags.
// Null sets the zero value. Names match case-sensitively. Unknown members
// are skipped. Duplicate names are errors unless `AllowDuplicateNames` is
// set; then the field is decoded again into the same value.
impl UnmarshalerFrom for Fields {
    fn unmarshal_json_from(&mut self, dec: &mut JsonDecoder<'_>) -> Result<(), JsonError> {
        match dec.peek_kind() {
            b'n' => {
                dec.read_token()?;
                *self = Fields::default();
                Ok(())
            }
            b'{' => {
                dec.read_token()?;
                dec.disable_namespace();
                let mut seen: Option<FxHashSet<String>> =
                    if dec.options.allow_duplicate_names { None } else { Some(FxHashSet::default()) };
                while dec.peek_kind() != b'}' {
                    let JsonToken::String(name) = dec.read_token()? else {
                        unreachable!("the decoder only reads strings as object names")
                    };
                    if let Some(seen) = &mut seen
                        && !seen.insert(name.clone())
                    {
                        return Err(JsonError { message: format!("duplicate object member name {name:?}") });
                    }
                    match name.as_str() {
                        "name" => json_unmarshal_decode(dec, &mut self.header_fields.name)?,
                        "version" => json_unmarshal_decode(dec, &mut self.header_fields.version)?,
                        "type" => json_unmarshal_decode(dec, &mut self.header_fields.type_)?,
                        "tsconfig" => json_unmarshal_decode(dec, &mut self.path_fields.ts_config)?,
                        "main" => json_unmarshal_decode(dec, &mut self.path_fields.main)?,
                        "types" => json_unmarshal_decode(dec, &mut self.path_fields.types)?,
                        "typings" => json_unmarshal_decode(dec, &mut self.path_fields.typings)?,
                        "typesVersions" => json_unmarshal_decode(dec, &mut self.path_fields.types_versions)?,
                        "imports" => json_unmarshal_decode(dec, &mut self.path_fields.imports)?,
                        "exports" => json_unmarshal_decode(dec, &mut self.path_fields.exports)?,
                        "dependencies" => json_unmarshal_decode(dec, &mut self.dependency_fields.dependencies)?,
                        "devDependencies" => json_unmarshal_decode(dec, &mut self.dependency_fields.dev_dependencies)?,
                        "peerDependencies" => json_unmarshal_decode(dec, &mut self.dependency_fields.peer_dependencies)?,
                        "optionalDependencies" => {
                            json_unmarshal_decode(dec, &mut self.dependency_fields.optional_dependencies)?;
                        }
                        _ => dec.skip_value()?,
                    }
                }
                dec.read_token()?;
                Ok(())
            }
            _ => {
                dec.skip_value()?;
                Err(JsonError { message: "cannot unmarshal JSON value into Go packagejson.Fields".to_string() })
            }
        }
    }
}

// Go: packagejson.go:116 Parse
// PORT: Go returns `(Fields{}, err)` on error. The `Result` carries the same
// information; callers use `unwrap_or_default()` for the zero `Fields`.
pub fn parse(data: &[u8]) -> Result<Fields, JsonError> {
    let mut f = Fields::default();
    json_unmarshal(data, &mut f, &[json_allow_duplicate_names(true)])?;
    Ok(f)
}

// ---------------------------------------------------------------------------
// cache.go
// ---------------------------------------------------------------------------

// Go: cache.go:13 typeScriptVersion
static TYPE_SCRIPT_VERSION: LazyLock<Version> = LazyLock::new(|| must_parse_version(crate::core::version()));

// Go: cache.go:15 PackageJson
// PORT: Go `sync.Once` plus the `versionPaths` and `versionTraces` fields is
// one `OnceCell`. Go embeds `Fields`; `Deref` promotes it.
#[derive(Clone, Debug, Default)]
pub struct PackageJson {
    pub fields: Fields,
    pub parseable: bool,
    pub(crate) version_paths: OnceCell<(VersionPaths, Vec<DiagnosticAndArgs>)>,
}

impl std::ops::Deref for PackageJson {
    type Target = Fields;
    fn deref(&self) -> &Fields {
        &self.fields
    }
}

// Go: cache.go:23 diagnosticAndArgs
// PORT: Go `[]any` args are already strings here (`args!`).
#[derive(Clone, Debug)]
pub struct DiagnosticAndArgs {
    message: &'static Message,
    args: Vec<String>,
}

impl PackageJson {
    // Go: cache.go:28 GetVersionPaths
    // PORT: Go `trace func(m, args ...any)` is an optional boxed closure.
    pub fn get_version_paths(&self, trace: Option<Box<dyn Fn(&'static Message, Vec<String>)>>) -> VersionPaths {
        let (version_paths, version_traces) = self.version_paths.get_or_init(|| self.compute_version_paths());
        if let Some(trace) = trace {
            for msg in version_traces {
                trace(msg.message, msg.args.clone());
            }
        }
        version_paths.clone()
    }

    // PORT: the body of the Go `p.once.Do` closure in GetVersionPaths.
    fn compute_version_paths(&self) -> (VersionPaths, Vec<DiagnosticAndArgs>) {
        let mut version_traces = Vec::new();
        let types_versions = &self.fields.path_fields.types_versions;
        if types_versions.type_ == JSONValueType::NOT_PRESENT {
            version_traces.push(DiagnosticAndArgs {
                message: diag::X_package_json_does_not_have_a_0_field,
                args: args!["typesVersions"],
            });
            return (VersionPaths::default(), version_traces);
        }
        if types_versions.type_ != JSONValueType::OBJECT {
            version_traces.push(DiagnosticAndArgs {
                message: diag::Expected_type_of_0_field_in_package_json_to_be_1_got_2,
                args: args!["typesVersions", "object", types_versions.type_.string()],
            });
            return (VersionPaths::default(), version_traces);
        }

        version_traces.push(DiagnosticAndArgs {
            message: diag::X_package_json_has_a_typesVersions_field_with_version_specific_path_mappings,
            args: args!["typesVersions"],
        });

        for (key, value) in types_versions.as_object() {
            let (key_range, ok) = try_parse_version_range(key);
            if !ok {
                version_traces.push(DiagnosticAndArgs {
                    message: diag::X_package_json_has_a_typesVersions_entry_0_that_is_not_a_valid_semver_range,
                    args: args![key],
                });
                continue;
            }
            if key_range.test(&TYPE_SCRIPT_VERSION) {
                if value.type_ != JSONValueType::OBJECT {
                    version_traces.push(DiagnosticAndArgs {
                        message: diag::Expected_type_of_0_field_in_package_json_to_be_1_got_2,
                        args: args![format!("typesVersions['{key}']"), "object", value.type_.string()],
                    });
                    return (VersionPaths::default(), version_traces);
                }
                let JsonAny::Object(paths_json) = &value.value else {
                    unreachable!("an object JSONValue holds an object")
                };
                let version_paths =
                    VersionPaths { version: key.clone(), paths_json: Some(paths_json.clone()), paths: OnceCell::new() };
                return (version_paths, version_traces);
            }
        }

        version_traces.push(DiagnosticAndArgs {
            message: diag::X_package_json_does_not_have_a_typesVersions_entry_that_matches_version_0,
            args: args![crate::core::version_major_minor()],
        });
        (VersionPaths::default(), version_traces)
    }
}

// Go: cache.go:88 VersionPaths
// PORT: Go caches `paths` through a pointer field. Copies made before the
// first `GetPaths` call do not share the cache; `OnceCell` clones the same.
#[derive(Clone, Debug, Default)]
pub struct VersionPaths {
    pub version: String,
    paths_json: Option<Rc<IndexMap<String, JSONValue>>>,
    paths: OnceCell<IndexMap<String, Vec<String>>>,
}

impl VersionPaths {
    // Go: cache.go:94 Exists
    #[must_use]
    pub fn exists(&self) -> bool {
        !self.version.is_empty() && self.paths_json.is_some()
    }

    // Go: cache.go:98 GetPaths
    #[must_use]
    pub fn get_paths(&self) -> Option<&IndexMap<String, Vec<String>>> {
        if !self.exists() {
            return None;
        }
        let paths_json = self.paths_json.as_ref()?;
        Some(self.paths.get_or_init(|| {
            let mut paths = IndexMap::with_capacity(paths_json.len());
            for (key, value) in paths_json.iter() {
                if value.type_ != JSONValueType::ARRAY {
                    continue;
                }
                let arr = value.as_array();
                let mut slice = vec![String::new(); arr.len()];
                for (i, path) in arr.iter().enumerate() {
                    if path.type_ != JSONValueType::STRING {
                        continue;
                    }
                    slice[i] = path.as_string().to_string();
                }
                paths.insert(key.clone(), slice);
            }
            paths
        }))
    }
}

// Go: cache.go:123 InfoCacheEntry
// PORT: Go `*InfoCacheEntry` is `Rc<InfoCacheEntry>`; a nil entry is `None`
// at the call site, so the nil-receiver checks are gone.
#[derive(Clone, Debug, Default)]
pub struct InfoCacheEntry {
    pub package_directory: String,
    pub directory_exists: bool,
    pub contents: Option<Rc<PackageJson>>,
}

impl InfoCacheEntry {
    // Go: cache.go:129 Exists
    #[must_use]
    pub fn exists(&self) -> bool {
        self.contents.is_some()
    }

    // Go: cache.go:133 GetContents
    #[must_use]
    pub fn get_contents(&self) -> Option<&Rc<PackageJson>> {
        self.contents.as_ref()
    }

    // Go: cache.go:140 GetDirectory
    #[must_use]
    pub fn get_directory(&self) -> &str {
        &self.package_directory
    }

    // Go: cache.go:158 WithPackageDirectory
    // WithPackageDirectory returns an entry whose PackageDirectory matches the
    // caller's value. The package.json info cache is keyed by the canonical
    // path of the package.json file, but multiple callers may look up the same
    // package.json using directory paths that differ only by a trailing
    // separator (e.g. "node_modules/preact/compat" vs
    // "node_modules/preact/compat/"). Because the cache uses first-writer-wins
    // semantics, a later caller may receive an entry whose PackageDirectory
    // doesn't match its own candidate path. Downstream code compares the
    // candidate against PackageDirectory, so we must return a corrected
    // shallow copy when they diverge.
    // See https://github.com/microsoft/TypeScript/pull/50740.
    #[must_use]
    pub fn with_package_directory(self: &Rc<Self>, package_directory: &str) -> Rc<InfoCacheEntry> {
        if self.package_directory == package_directory {
            return self.clone();
        }
        Rc::new(InfoCacheEntry {
            package_directory: package_directory.to_string(),
            directory_exists: self.directory_exists,
            contents: self.contents.clone(),
        })
    }
}

// Go: cache.go:169 InfoCache
// PORT: Go `collections.SyncMap` is a `RefCell` map. The cache is shared as
// `Rc<InfoCache>`, so its methods take `&self`.
#[derive(Debug, Default)]
pub struct InfoCache {
    cache: RefCell<FxHashMap<Path, Rc<InfoCacheEntry>>>,
    current_directory: String,
    use_case_sensitive_file_names: bool,
}

// Go: cache.go:175 NewInfoCache
#[must_use]
pub fn new_info_cache(current_directory: &str, use_case_sensitive_file_names: bool) -> InfoCache {
    InfoCache {
        cache: RefCell::new(FxHashMap::default()),
        current_directory: current_directory.to_string(),
        use_case_sensitive_file_names,
    }
}

impl InfoCache {
    // Go: cache.go:182 Get
    #[must_use]
    pub fn get(&self, package_json_path: &str) -> Option<Rc<InfoCacheEntry>> {
        let key = to_path(package_json_path, &self.current_directory, self.use_case_sensitive_file_names);
        self.cache.borrow().get(&key).cloned()
    }

    // Go: cache.go:190 Set
    // PORT: Go `LoadOrStore`: the first stored entry wins and is returned.
    pub fn set(&self, package_json_path: &str, info: Rc<InfoCacheEntry>) -> Rc<InfoCacheEntry> {
        let key = to_path(package_json_path, &self.current_directory, self.use_case_sensitive_file_names);
        self.cache.borrow_mut().entry(key).or_insert(info).clone()
    }
}
