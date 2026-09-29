//! Go `internal/debug`: checks that stay on in release builds. A failed check
//! is a Go panic (`core::go_panic`), so the bins, the API and the LSP print
//! "panic: Debug failure. ..." like Go. Use these only at a Go `debug.*` site.
//! Checks that only the port has stay `debug_assert!`.
//!
//! Go site to port site:
//! - `debug.Assert(c)`: `go_assert!(c)`.
//! - `debug.Assert(c, a, b)`: `go_assert!(c, "{a}{b}")`. Go `fmt.Sprint`
//!   puts no space between string operands. Print a kind with `kind_string`.
//! - `debug.Fail(r)`: `debug::fail(r)`.
//! - `debug.AssertNever(x[, m])`: `debug::assert_never(&detail, m)`.
//! - `debug.FailBadSyntaxKind(n[, m])`: `debug::fail_bad_syntax_kind(n.kind(), m)`.

use crate::astdata::SyntaxKind;
use crate::core::go_panic;

// Go: debug/debug.go:7 Fail
#[cold]
#[inline(never)]
#[track_caller]
pub fn fail(reason: &str) -> ! {
    if reason.is_empty() {
        go_panic("Debug failure.".to_string())
    } else {
        go_panic(format!("Debug failure. {reason}"))
    }
}

// Go: debug/debug.go:52 assertSlow (the out-of-line half of Assert)
/// The failure path of `go_assert!`. `message` is Go `fmt.Sprint(message...)`.
#[cold]
#[inline(never)]
#[track_caller]
pub fn assert_failed(message: Option<std::fmt::Arguments<'_>>) -> ! {
    match message {
        Some(m) => fail(&format!("False expression: {m}")),
        None => fail("False expression."),
    }
}

// Go: debug/debug.go:27 AssertNever
/// `detail` is Go `KindString()`, `String()` or `%v` of the value.
#[cold]
#[inline(never)]
#[track_caller]
pub fn assert_never(detail: &str, message: Option<&str>) -> ! {
    fail(&format!("{} {detail}", message.unwrap_or("Illegal value:")))
}

// Go: debug/debug.go:17 FailBadSyntaxKind
#[cold]
#[inline(never)]
#[track_caller]
pub fn fail_bad_syntax_kind(kind: SyntaxKind, message: Option<&str>) -> ! {
    fail(&format!(
        "{}\nNode {} was unexpected.",
        message.unwrap_or("Unexpected node."),
        kind_string(kind)
    ))
}

// Go: ast/kind_stringer_generated.go:369 Kind.String
/// Go `Kind.String()` ("KindIdentifier"). Rust `{:?}` gives "Identifier".
pub fn kind_string(kind: SyntaxKind) -> String {
    format!("Kind{}", kind.as_str())
}

/// Go `debug.Assert(cond, message...)`. The condition runs in release
/// builds. The message is formatted only when the check fails.
#[macro_export]
macro_rules! go_assert {
    ($cond:expr $(,)?) => {
        if !$cond {
            $crate::gostd::debug::assert_failed(None)
        }
    };
    ($cond:expr, $($arg:tt)+) => {
        if !$cond {
            $crate::gostd::debug::assert_failed(Some(format_args!($($arg)+)))
        }
    };
}

// Go: debug/debug_test.go. Go's tests use mock nodes; these use real kinds.
#[cfg(test)]
mod tests {
    use super::*;

    fn panic_text(f: impl FnOnce() + std::panic::UnwindSafe) -> String {
        let payload = std::panic::catch_unwind(f).expect_err("no panic");
        match payload.downcast::<crate::core::GoPanic>() {
            Ok(p) => p.message,
            Err(_) => panic!("not a GoPanic"),
        }
    }

    #[test]
    fn fail_texts() {
        assert_eq!(panic_text(|| fail("")), "Debug failure.");
        assert_eq!(
            panic_text(|| fail("something went wrong")),
            "Debug failure. something went wrong"
        );
    }

    #[test]
    fn fail_bad_syntax_kind_texts() {
        assert_eq!(
            panic_text(|| fail_bad_syntax_kind(SyntaxKind::Identifier, None)),
            "Debug failure. Unexpected node.\nNode KindIdentifier was unexpected."
        );
        assert_eq!(
            panic_text(|| fail_bad_syntax_kind(
                SyntaxKind::JsDocTypeExpression,
                Some("custom message")
            )),
            "Debug failure. custom message\nNode KindJSDocTypeExpression was unexpected."
        );
    }

    #[test]
    fn assert_never_texts() {
        assert_eq!(
            panic_text(|| assert_never("TestNode", None)),
            "Debug failure. Illegal value: TestNode"
        );
        assert_eq!(
            panic_text(|| assert_never("TestNode", Some("bad value:"))),
            "Debug failure. bad value: TestNode"
        );
        assert_eq!(
            panic_text(|| assert_never(&42.to_string(), None)),
            "Debug failure. Illegal value: 42"
        );
    }

    #[test]
    fn assert_texts() {
        go_assert!(true);
        go_assert!(true, "this should not trigger");
        assert_eq!(
            panic_text(|| go_assert!(false)),
            "Debug failure. False expression."
        );
        let x = 0;
        assert_eq!(
            panic_text(|| go_assert!(x > 0, "expected x > {x}")),
            "Debug failure. False expression: expected x > 0"
        );
    }

    // The panic location is the `go_assert!` site, for the stderr report.
    #[test]
    fn assert_location_is_the_call_site() {
        let line = line!() + 2;
        let payload = std::panic::catch_unwind(|| {
            go_assert!(false);
        })
        .expect_err("no panic");
        let p = payload
            .downcast::<crate::core::GoPanic>()
            .ok()
            .expect("GoPanic");
        assert_eq!((p.location.file(), p.location.line()), (file!(), line));
    }
}
