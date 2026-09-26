//! Go `errors` (go1.26.8 `src/errors/errors.go`, `wrap.go`, `join.go`), the
//! error values that `fmt.Errorf` makes (`src/fmt/errors.go`) and `io.EOF`.
//!
//! PORT: Go `error` is an interface. `GoError` is one shared error value.
//! Go compares error values with `==`: pointer identity for the pointer kinds
//! (`*errorString`, `*wrapError`, `*wrapErrors`, `*joinError`) and value
//! equality for comparable value types (for example `lsproto.ErrorCode`).
//! `GoError` keeps both: `Arc` identity for the pointer kinds and
//! `PartialEq` for values made with `from_value`. A clone of a `GoError` is
//! the same Go value (the same pointer).

use crate::prelude::*;

use std::any::{Any, TypeId};
use std::fmt;
use std::sync::{Arc, LazyLock};

/// Go `error` (a non-nil value). A nil `error` is `Option<GoError>` or the
/// `Ok` side of a `Result`.
#[derive(Clone)]
pub struct GoError(Arc<ErrorRepr>);

enum ErrorRepr {
    /// Go `*errors.errorString`.
    ErrorString(ErrorString),
    /// Go `*fmt.wrapError`.
    WrapError(WrapError),
    /// Go `*fmt.wrapErrors`.
    WrapErrors(WrapErrors),
    /// Go `*errors.joinError`.
    JoinError(JoinError),
    /// A comparable Go type with an `Error()` method (and, when `unwrap` is
    /// set, an `Unwrap() error` method).
    Value(ValueError),
}

/// A Go type used as an error value. Implemented for every
/// `T: Any + Display + Debug + PartialEq + Send + Sync`.
trait ErrorValue: Send + Sync + 'static {
    fn error(&self) -> String;
    fn as_any(&self) -> &dyn Any;
    fn value_type_id(&self) -> TypeId;
    fn eq_value(&self, other: &dyn ErrorValue) -> bool;
}

impl<T: Any + fmt::Display + fmt::Debug + PartialEq + Send + Sync> ErrorValue for T {
    fn error(&self) -> String {
        self.to_string()
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn value_type_id(&self) -> TypeId {
        TypeId::of::<T>()
    }

    fn eq_value(&self, other: &dyn ErrorValue) -> bool {
        match other.as_any().downcast_ref::<T>() {
            Some(other) => self == other,
            None => false,
        }
    }
}

struct ValueError {
    value: Box<dyn ErrorValue>,
    /// Go `Unwrap() error` of the value type, when it has one.
    unwrap: Option<GoError>,
}

/// The result of Go's type switch on `Unwrap() error` and `Unwrap() []error`.
enum Unwrapped {
    /// The error has no `Unwrap` method.
    None,
    /// Go `Unwrap() error`. `None` is a nil result.
    One(Option<GoError>),
    /// Go `Unwrap() []error`.
    Many(Vec<GoError>),
}

impl GoError {
    fn from_repr(repr: ErrorRepr) -> GoError {
        GoError(Arc::new(repr))
    }

    /// Go `err.Error()`.
    pub fn error(&self) -> String {
        match &*self.0 {
            ErrorRepr::ErrorString(e) => e.error(),
            ErrorRepr::WrapError(e) => e.error(),
            ErrorRepr::WrapErrors(e) => e.error(),
            ErrorRepr::JoinError(e) => e.error(),
            ErrorRepr::Value(e) => e.value.error(),
        }
    }

    /// Go `errors.Unwrap(err)`: the result of the error's `Unwrap() error`
    /// method. `None` when the error has no such method (this includes the
    /// `Unwrap() []error` kinds) or the method returns nil.
    pub fn unwrap(&self) -> Option<GoError> {
        unwrap(self)
    }

    fn unwrapped(&self) -> Unwrapped {
        match &*self.0 {
            ErrorRepr::ErrorString(_) => Unwrapped::None,
            ErrorRepr::WrapError(e) => Unwrapped::One(Some(e.unwrap())),
            ErrorRepr::WrapErrors(e) => Unwrapped::Many(e.unwrap()),
            ErrorRepr::JoinError(e) => Unwrapped::Many(e.unwrap()),
            ErrorRepr::Value(e) => match &e.unwrap {
                Some(inner) => Unwrapped::One(Some(inner.clone())),
                None => Unwrapped::None,
            },
        }
    }

    /// Go `err == target` on two non-nil error interface values.
    fn go_eq(&self, other: &GoError) -> bool {
        match (&*self.0, &*other.0) {
            (ErrorRepr::Value(a), ErrorRepr::Value(b)) => {
                a.value.value_type_id() == b.value.value_type_id() && a.value.eq_value(&*b.value)
            }
            (ErrorRepr::Value(_), _) | (_, ErrorRepr::Value(_)) => false,
            _ => Arc::ptr_eq(&self.0, &other.0),
        }
    }

    /// Go type assertion `err.(T)` for a value type made with `from_value`.
    fn downcast<T: Any + Clone>(&self) -> Option<T> {
        match &*self.0 {
            ErrorRepr::Value(e) => e.value.as_any().downcast_ref::<T>().cloned(),
            _ => None,
        }
    }
}

/// Go `err == target` (interface equality).
impl PartialEq for GoError {
    fn eq(&self, other: &GoError) -> bool {
        self.go_eq(other)
    }
}

impl fmt::Display for GoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.error())
    }
}

// PORT: Go `%v` of an error prints `err.Error()`; so does `{:?}`.
impl fmt::Debug for GoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.error())
    }
}

impl std::error::Error for GoError {}

// Go: errors/errors.go:64 New
/// Go `errors.New(text)`. Each call makes a distinct error, even if the
/// text is identical.
pub fn new(text: impl Into<String>) -> GoError {
    GoError::from_repr(ErrorRepr::ErrorString(ErrorString { s: text.into() }))
}

// Go: errors/errors.go:69 errorString
/// errorString is a trivial implementation of error.
struct ErrorString {
    s: String,
}

impl ErrorString {
    // Go: errors/errors.go:73 Error
    fn error(&self) -> String {
        self.s.clone()
    }
}

// Go: errors/errors.go:90 ErrUnsupported
/// ErrUnsupported indicates that a requested operation cannot be performed,
/// because it is unsupported.
pub static ERR_UNSUPPORTED: LazyLock<GoError> = LazyLock::new(|| new("unsupported operation"));

// Go: io/io.go:44 EOF
/// EOF is the error returned by Read when no more input is available.
pub static EOF: LazyLock<GoError> = LazyLock::new(|| new("EOF"));

// Go: fmt/errors.go:23 Errorf
/// Go `fmt.Errorf`. `text` is the formatted message (built with `format!`).
/// `wrapped` holds the `%w` operands in argument order.
///
/// PORT: Go sorts the `%w` operands by argument index when the format
/// reorders them and drops a repeated argument index; the caller passes them
/// already in argument order, once each. A `%w` operand that is not an error
/// cannot occur. With no `%w` operand Go returns `errors.New(s)`.
pub fn errorf(text: impl Into<String>, wrapped: Vec<GoError>) -> GoError {
    // Go: fmt/errors.go:35 errorf
    let s = text.into();
    match wrapped.len() {
        0 => new(s),
        1 => {
            let err = wrapped.into_iter().next().unwrap();
            GoError::from_repr(ErrorRepr::WrapError(WrapError { msg: s, err }))
        }
        _ => GoError::from_repr(ErrorRepr::WrapErrors(WrapErrors {
            msg: s,
            errs: wrapped,
        })),
    }
}

// Go: fmt/errors.go:70 wrapError
struct WrapError {
    msg: String,
    err: GoError,
}

impl WrapError {
    // Go: fmt/errors.go:75 Error
    fn error(&self) -> String {
        self.msg.clone()
    }

    // Go: fmt/errors.go:79 Unwrap
    fn unwrap(&self) -> GoError {
        self.err.clone()
    }
}

// Go: fmt/errors.go:83 wrapErrors
struct WrapErrors {
    msg: String,
    errs: Vec<GoError>,
}

impl WrapErrors {
    // Go: fmt/errors.go:88 Error
    fn error(&self) -> String {
        self.msg.clone()
    }

    // Go: fmt/errors.go:92 Unwrap
    fn unwrap(&self) -> Vec<GoError> {
        self.errs.clone()
    }
}

/// A Go value type used as an error (for example `lsproto.ErrorCode` or a
/// `type X string` with an `Error()` method). `Error()` is `Display`; two
/// values are the same error when they have the same type and `==` holds.
pub fn from_value<T: Any + fmt::Display + fmt::Debug + PartialEq + Send + Sync>(v: T) -> GoError {
    GoError::from_repr(ErrorRepr::Value(ValueError {
        value: Box::new(v),
        unwrap: None,
    }))
}

/// Like `from_value`, for a Go value type that also has an `Unwrap() error`
/// method that returns `unwrap` (for example lsp `userFacingRequestFailedError`).
///
/// PORT: Go declares `Unwrap` on the type; the port passes its result here.
pub fn from_value_with_unwrap<T: Any + fmt::Display + fmt::Debug + PartialEq + Send + Sync>(
    v: T,
    unwrap: GoError,
) -> GoError {
    GoError::from_repr(ErrorRepr::Value(ValueError {
        value: Box::new(v),
        unwrap: Some(unwrap),
    }))
}

// Go: errors/join.go:20 Join
/// Join returns an error that wraps the given errors.
/// Any nil error values are discarded.
/// Join returns nil if every value in errs is nil.
/// The error formats as the concatenation of the strings obtained
/// by calling the Error method of each element of errs, with a newline
/// between each string.
///
/// PORT: Go `...error`; each item is a `GoError` or an `Option<GoError>`
/// (`None` is a nil error).
pub fn join<I, E>(errs: I) -> Option<GoError>
where
    I: IntoIterator<Item = E>,
    E: Into<Option<GoError>>,
{
    let errs: Vec<Option<GoError>> = errs.into_iter().map(Into::into).collect();
    let mut n = 0;
    for err in &errs {
        if err.is_some() {
            n += 1;
        }
    }
    if n == 0 {
        return None;
    }
    let mut e = JoinError {
        errs: Vec::with_capacity(n),
    };
    for err in errs {
        if let Some(err) = err {
            e.errs.push(err);
        }
    }
    Some(GoError::from_repr(ErrorRepr::JoinError(e)))
}

// Go: errors/join.go:41 joinError
struct JoinError {
    errs: Vec<GoError>,
}

impl JoinError {
    // Go: errors/join.go:45 Error
    fn error(&self) -> String {
        // Since Join returns nil if every value in errs is nil,
        // e.errs cannot be empty.
        if self.errs.len() == 1 {
            return self.errs[0].error();
        }

        let mut b = self.errs[0].error();
        for err in &self.errs[1..] {
            b.push('\n');
            b.push_str(&err.error());
        }
        b
    }

    // Go: errors/join.go:61 Unwrap
    fn unwrap(&self) -> Vec<GoError> {
        self.errs.clone()
    }
}

// Go: errors/wrap.go:17 Unwrap
/// Unwrap returns the result of calling the Unwrap method on err, if err's
/// type contains an Unwrap method returning error.
/// Otherwise, Unwrap returns nil.
///
/// Unwrap only calls a method of the form "Unwrap() error".
/// In particular Unwrap does not unwrap errors returned by [Join].
pub fn unwrap(err: &GoError) -> Option<GoError> {
    match err.unwrapped() {
        Unwrapped::One(u) => u,
        Unwrapped::None | Unwrapped::Many(_) => None,
    }
}

// Go: errors/wrap.go:45 Is
/// Is reports whether any error in err's tree matches target.
///
/// The tree consists of err itself, followed by the errors obtained by
/// repeatedly calling its Unwrap() error or Unwrap() []error method. When
/// err wraps multiple errors, Is examines err followed by a depth-first
/// traversal of its children.
///
/// An error is considered to match a target if it is equal to that target.
///
/// PORT: both arguments are non-nil here (Go `err == nil || target == nil`
/// returns `err == target`; callers with an `Option<GoError>` test it
/// first). Every `GoError` kind is comparable, so `isComparable` is true.
pub fn is(err: &GoError, target: &GoError) -> bool {
    let is_comparable = true;
    is_unexported(err, target, is_comparable)
}

// Go: errors/wrap.go:54 is
// PORT: named `is_unexported` because Go `Is` is `is` (plan contract C1).
// No ported error kind has an `Is(error) bool` method, so that step is empty.
fn is_unexported(err: &GoError, target: &GoError, target_comparable: bool) -> bool {
    let mut err = err.clone();
    loop {
        if target_comparable && err.go_eq(target) {
            return true;
        }
        match err.unwrapped() {
            Unwrapped::One(u) => match u {
                Some(u) => err = u,
                None => return false,
            },
            Unwrapped::Many(errs) => {
                for err in &errs {
                    if is_unexported(err, target, target_comparable) {
                        return true;
                    }
                }
                return false;
            }
            Unwrapped::None => return false,
        }
    }
}

// Go: errors/wrap.go:102 As
/// As finds the first error in err's tree that matches target, and if one is
/// found, sets target to that error value and returns true. Otherwise, it
/// returns false.
///
/// PORT: `target` points to a concrete value type made with `from_value`
/// (`T`). Go also accepts an interface type as the target; the port has no
/// such caller. No ported error kind has an `As(any) bool` method.
pub fn as_<T: Any + Clone>(err: &GoError, target: &mut T) -> bool {
    as_unexported(err, target)
}

// Go: errors/wrap.go:121 as
// PORT: named `as_unexported` because Go `As` is `as_`.
fn as_unexported<T: Any + Clone>(err: &GoError, target: &mut T) -> bool {
    let mut err = err.clone();
    loop {
        if let Some(v) = err.downcast::<T>() {
            *target = v;
            return true;
        }
        match err.unwrapped() {
            Unwrapped::One(u) => match u {
                Some(u) => err = u,
                None => return false,
            },
            Unwrapped::Many(errs) => {
                for err in &errs {
                    if as_unexported(err, target) {
                        return true;
                    }
                }
                return false;
            }
            Unwrapped::None => return false,
        }
    }
}

// Go: errors/wrap.go:167 AsType
/// AsType finds the first error in err's tree that matches the type E, and
/// if one is found, returns that error value and true. Otherwise, it
/// returns the zero value of E and false.
///
/// PORT: `(E, bool)` is `Option<T>`; `T` is a value type made with
/// `from_value`.
pub fn as_type<T: Any + Clone>(err: &GoError) -> Option<T> {
    as_type_unexported::<T>(err)
}

// Go: errors/wrap.go:176 asType
// PORT: named `as_type_unexported` because Go `AsType` is `as_type`. The
// lazily allocated `ppe` only serves `As(any) bool` methods, which no ported
// error kind has.
fn as_type_unexported<T: Any + Clone>(err: &GoError) -> Option<T> {
    let mut err = err.clone();
    loop {
        if let Some(e) = err.downcast::<T>() {
            return Some(e);
        }
        match err.unwrapped() {
            Unwrapped::One(u) => match u {
                Some(u) => err = u,
                None => return None,
            },
            Unwrapped::Many(errs) => {
                for err in &errs {
                    if let Some(x) = as_type_unexported::<T>(err) {
                        return Some(x);
                    }
                }
                return None;
            }
            Unwrapped::None => return None,
        }
    }
}
