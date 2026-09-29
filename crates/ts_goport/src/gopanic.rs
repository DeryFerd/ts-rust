//! Go panics and unported-code hits: `GoPanic`, `go_panic`, `unported!`
//! and the unported registry. They live in `goport_util` as the module
//! `core`, so util files keep their `crate::core::` paths and
//! `$crate::core::record_unported` resolves. `ts_goport`'s `core.rs`
//! re-exports them.

/// Unported hits of every thread, by Go name.
static UNPORTED_NAMES: std::sync::Mutex<std::collections::BTreeMap<&'static str, u64>> =
    std::sync::Mutex::new(std::collections::BTreeMap::new());

/// Records one hit of unported Go code. The runner reports every name.
/// A run with any hit is not a match.
pub fn record_unported(go_name: &'static str) {
    let mut names = UNPORTED_NAMES
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    *names.entry(go_name).or_default() += 1;
}

/// All unported names hit so far on any thread, with hit counts.
#[must_use]
pub fn unported_report() -> Vec<(&'static str, u64)> {
    let names = UNPORTED_NAMES
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    names.iter().map(|(k, v)| (*k, *v)).collect()
}

/// Puts back the unported hits that `unported_report` returned. Work that
/// is thrown away and redone uses it, so the hits are not counted twice.
pub fn restore_unported(report: &[(&'static str, u64)]) {
    let mut names = UNPORTED_NAMES
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    *names = report.iter().copied().collect();
}

/// Marks unported Go code. It records the hit, then panics so the gap is
/// loud. Use only where a port is missing, never as a fallback.
#[macro_export]
macro_rules! unported {
    ($go_name:expr) => {{
        $crate::core::record_unported($go_name);
        panic!("unported Go code: {}", $go_name)
    }};
}

/// The panic payload of `go_panic`.
pub struct GoPanic {
    /// The Go panic value as the Go runtime prints it (port form).
    pub message: String,
    /// The port site, for the stderr report.
    pub location: &'static std::panic::Location<'static>,
}

/// Go `panic(message)` at a site where the pinned Go panics on the same
/// input. It is not a port gap, so the run ends as the Go runtime ends it:
/// guards that keep a run going after a port gap pass it on
/// (`resume_go_panic`), and the bins write the output so far, print it with
/// `print_go_panic` and exit `EXIT_GO_PANIC`. Other panics stay port gaps
/// (`execute::tsc::EXIT_UNPORTED`).
#[track_caller]
pub fn go_panic(message: String) -> ! {
    std::panic::panic_any(GoPanic {
        message,
        location: std::panic::Location::caller(),
    })
}

/// `go_panic` with the Go runtime text for a nil pointer dereference, at a
/// site where the pinned Go dereferences nil on the same input. It is cold
/// and out of line, so the nil check at a hot site is one compare.
#[cold]
#[inline(never)]
#[track_caller]
pub fn go_nil_dereference() -> ! {
    go_panic("runtime error: invalid memory address or nil pointer dereference".to_string())
}

/// The Go runtime exit code after a panic that nothing recovers.
pub const EXIT_GO_PANIC: i32 = 2;

/// Continues a caught `go_panic`. Returns any other payload.
pub fn resume_go_panic(payload: Box<dyn std::any::Any + Send>) -> Box<dyn std::any::Any + Send> {
    if payload.is::<GoPanic>() {
        std::panic::resume_unwind(payload);
    }
    payload
}

/// Prints a caught `go_panic` to stderr and returns true. The first line is
/// the Go runtime one (`panic: <message>`). The port site takes the place of
/// the goroutine trace. False for any other payload.
pub fn print_go_panic(payload: &(dyn std::any::Any + Send)) -> bool {
    let Some(panic) = payload.downcast_ref::<GoPanic>() else {
        return false;
    };
    let text = format!(
        "panic: {}\n\n\t{}:{}\n",
        panic.message,
        panic.location.file(),
        panic.location.line()
    );
    use std::io::Write;
    let _ = std::io::stderr().write_all(&crate::scanner_util::go_string_bytes(&text));
    true
}
