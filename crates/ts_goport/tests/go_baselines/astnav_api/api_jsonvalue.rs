//! Port of internal/api/jsonvalue_test.go.
//!
//! PORT: Go decodes into a `packagejson.JSONValue`; the port's request field
//! is `LspAny` (see `ParseJsonConfigFileContentParams`). Go `any` from
//! `jsonValueToAny` is `CompilerOptionsValue`.

use ts_goport::api::json_value_to_any;
use ts_goport::frontend::json::json_unmarshal;
use ts_goport::frontend::json_ext::LspAny;
use ts_goport::frontend::tsoptions::CompilerOptionsValue;

// Go: api/jsonvalue_test.go:13 TestJSONValueToAny
#[test]
fn test_json_value_to_any() {
    let mut value = LspAny::default();
    let err = json_unmarshal(
        br#"{"z":1,"a":{"y":2,"x":3},"m":[{"b":4,"a":5},null],"e":[]}"#,
        &mut value,
        &[],
    );
    assert!(err.is_ok(), "assertion failed: error is not nil: {err:?}");

    let CompilerOptionsValue::Map(root) = json_value_to_any(&value) else {
        panic!("root is not *collections.OrderedMap[string, any]");
    };
    assert_eq!(root.keys().collect::<Vec<_>>(), ["z", "a", "m", "e"]);
    assert_eq!(root.get("z"), Some(&CompilerOptionsValue::Number(1.0)));

    let Some(CompilerOptionsValue::Map(nested)) = root.get("a") else {
        panic!("a is not *collections.OrderedMap[string, any]");
    };
    assert_eq!(nested.keys().collect::<Vec<_>>(), ["y", "x"]);

    let Some(CompilerOptionsValue::List(array)) = root.get("m") else {
        panic!("m is not []any");
    };
    let CompilerOptionsValue::Map(array_object) = &array[0] else {
        panic!("m[0] is not *collections.OrderedMap[string, any]");
    };
    assert_eq!(array_object.keys().collect::<Vec<_>>(), ["b", "a"]);
    assert_eq!(array[1], CompilerOptionsValue::Nil);

    // PORT: Go also checks that the empty slice is not nil; a `Vec` has no
    // nil.
    let Some(CompilerOptionsValue::List(empty)) = root.get("e") else {
        panic!("e is not []any");
    };
    assert_eq!(empty.len(), 0);
}
