//! Go: `internal/debug/debug_test.go`, run on `ts_goport::gostd::debug`.
//!
//! PORT: Go `debug.Assert(cond, msg...)` is the `go_assert!` macro, and a Go
//! panic value is the `GoPanic` payload's message. Go `FailBadSyntaxKind`
//! and `AssertNever` take a value with `KindString()` or `String()`; the
//! port takes a `SyntaxKind` and the printed detail. The mock node kinds
//! ("FooNode", "BarNode") are real kinds here, so the text holds the Go
//! `Kind.String()` of that kind.

use std::panic::{AssertUnwindSafe, catch_unwind};

use ts_goport::astdata::SyntaxKind;
use ts_goport::core::GoPanic;
use ts_goport::go_assert;
use ts_goport::gostd::debug;

// Go: internal/testutil/testutil.go:14 AssertPanics
fn assert_panics(f: impl FnOnce(), expected: &str) {
    let payload = catch_unwind(AssertUnwindSafe(f)).expect_err("expected a panic");
    let got = payload
        .downcast_ref::<GoPanic>()
        .map(|p| p.message.clone())
        .unwrap_or_else(|| panic!("expected a Go panic with {expected:?}"));
    assert_eq!(got, expected);
}

// Go: debug_test.go:10 TestFailEmptyReason
#[test]
fn test_fail_empty_reason() {
    assert_panics(|| debug::fail(""), "Debug failure.");
}

// Go: debug_test.go:17 TestFailWithReason
#[test]
fn test_fail_with_reason() {
    assert_panics(
        || debug::fail("something went wrong"),
        "Debug failure. something went wrong",
    );
}

// Go: debug_test.go:28 TestFailBadSyntaxKindNoMessage
// PORT: Go mockNode{"FooNode"}; here SyntaxKind::Identifier.
#[test]
fn test_fail_bad_syntax_kind_no_message() {
    assert_panics(
        || debug::fail_bad_syntax_kind(SyntaxKind::Identifier, None),
        "Debug failure. Unexpected node.\nNode KindIdentifier was unexpected.",
    );
}

// Go: debug_test.go:35 TestFailBadSyntaxKindWithMessage
// PORT: Go mockNode{"BarNode"}; here SyntaxKind::Block.
#[test]
fn test_fail_bad_syntax_kind_with_message() {
    assert_panics(
        || debug::fail_bad_syntax_kind(SyntaxKind::Block, Some("custom message")),
        "Debug failure. custom message\nNode KindBlock was unexpected.",
    );
}

// Go: debug_test.go:42 TestAssertNeverDefaultMessageKindString
// PORT: the caller passes Go `KindString()` as the detail.
#[test]
fn test_assert_never_default_message_kind_string() {
    assert_panics(
        || debug::assert_never("TestNode", None),
        "Debug failure. Illegal value: TestNode",
    );
}

// Go: debug_test.go:49 TestAssertNeverCustomMessageKindString
#[test]
fn test_assert_never_custom_message_kind_string() {
    assert_panics(
        || debug::assert_never("TestNode", Some("bad value:")),
        "Debug failure. bad value: TestNode",
    );
}

// Go: debug_test.go:60 TestAssertNeverStringer
// PORT: the caller passes Go `String()` as the detail.
#[test]
fn test_assert_never_stringer() {
    struct MockStringer(&'static str);
    impl std::fmt::Display for MockStringer {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str(self.0)
        }
    }
    assert_panics(
        || debug::assert_never(&MockStringer("hello").to_string(), None),
        "Debug failure. Illegal value: hello",
    );
}

// Go: debug_test.go:67 TestAssertNeverFallback
// PORT: the caller passes Go `fmt.Sprintf("%v", 42)` as the detail.
#[test]
fn test_assert_never_fallback() {
    assert_panics(
        || debug::assert_never(&42.to_string(), None),
        "Debug failure. Illegal value: 42",
    );
}

// Go: debug_test.go:74 TestAssertTrue
#[test]
fn test_assert_true() {
    go_assert!(true);
}

// Go: debug_test.go:79 TestAssertTrueWithMessage
#[test]
fn test_assert_true_with_message() {
    go_assert!(true, "this should not trigger");
}

// Go: debug_test.go:84 TestAssertFalseNoMessage
#[test]
fn test_assert_false_no_message() {
    assert_panics(|| go_assert!(false), "Debug failure. False expression.");
}

// Go: debug_test.go:91 TestAssertFalseWithMessage
#[test]
fn test_assert_false_with_message() {
    assert_panics(
        || go_assert!(false, "expected x > 0"),
        "Debug failure. False expression: expected x > 0",
    );
}
