//! Go `internal/project/logging/logger.go`.
//!
//! PORT: log arguments are preformatted. Go `Log(msg ...any)` joins them
//! with `fmt.Sprint`; Go `Logf(format, args...)` formats with `fmt.Sprintf`.
//! Rust callers pass the finished text (`log(&format!(..))`), so `log` and
//! `logf` take the message as `&str`. The nil forms are `Option` (see
//! `project/dirty/interfaces.rs`, decision 5).

use crate::project::logging::prelude::*;
use std::cell::Cell;
use std::io::Write;
use std::time::SystemTime;

// Go: project/logging/logger.go:10 Logger
pub trait Logger {
    // Error logs an error message.
    fn error(&self, msg: &str);
    // Errorf logs a formatted error message.
    fn errorf(&self, msg: &str);
    // Warn logs a warning message.
    fn warn(&self, msg: &str);
    // Warnf logs a formatted warning message.
    fn warnf(&self, msg: &str);
    // Info logs an info message.
    fn info(&self, msg: &str);
    // Infof logs a formatted info message.
    fn infof(&self, msg: &str);
    // Log prints a line to the output writer with a header.
    fn log(&self, msg: &str);
    // Logf prints a formatted line to the output writer with a header.
    fn logf(&self, msg: &str);

    // Verbose returns the logger instance if verbose logging is enabled, and otherwise returns nil.
    // A nil logger created with `logging.NewLogger` is safe to call methods on.
    // PORT: returns a borrow of the same logger (no Go code calls Verbose).
    fn verbose(&self) -> Option<&dyn Logger>;
    // IsVerbose returns true if verbose logging is enabled, and false otherwise.
    fn is_verbose(&self) -> bool;
    // SetVerbose sets the verbose logging flag.
    fn set_verbose(&self, verbose: bool);
}

// Go: project/logging/logger.go:39 logger
// PORT: Go unexported type behind the `Logger` interface, so the Rust name
// is `LoggerImpl`. `mu` is dropped (one thread). A Go nil `*logger`
// (`NewNopLogger`) is `None` of `Option<Rc<dyn Logger>>`; its methods are
// the `Logger` impl on that `Option` below.
pub struct LoggerImpl {
    pub verbose: Cell<bool>,
    pub writer: RefCell<Box<dyn Write>>,
    pub prefix: Box<dyn Fn() -> String>,
}

impl Logger for LoggerImpl {
    // Go: project/logging/logger.go:94 Error
    fn error(&self, msg: &str) {
        self.log(msg);
    }

    // Go: project/logging/logger.go:98 Errorf
    fn errorf(&self, msg: &str) {
        self.logf(msg);
    }

    // Go: project/logging/logger.go:102 Warn
    fn warn(&self, msg: &str) {
        self.log(msg);
    }

    // Go: project/logging/logger.go:106 Warnf
    fn warnf(&self, msg: &str) {
        self.logf(msg);
    }

    // Go: project/logging/logger.go:110 Info
    fn info(&self, msg: &str) {
        self.log(msg);
    }

    // Go: project/logging/logger.go:114 Infof
    fn infof(&self, msg: &str) {
        self.logf(msg);
    }

    // Go: project/logging/logger.go:46 Log
    fn log(&self, msg: &str) {
        // Go: `if l == nil { return }` is the `None` impl below.
        // Go: fmt.Fprintln(l.writer, l.prefix(), fmt.Sprint(msg...)); the
        // write error is ignored.
        let prefix = (self.prefix)();
        let _ = writeln!(self.writer.borrow_mut(), "{} {}", prefix, msg);
    }

    // Go: project/logging/logger.go:55 Logf
    fn logf(&self, msg: &str) {
        // Go: fmt.Fprintf(l.writer, "%s %s\n", l.prefix(), fmt.Sprintf(format, args...))
        let prefix = (self.prefix)();
        let _ = write!(self.writer.borrow_mut(), "{} {}\n", prefix, msg);
    }

    // Go: project/logging/logger.go:64 Verbose
    fn verbose(&self) -> Option<&dyn Logger> {
        if !self.verbose.get() {
            return None;
        }
        Some(self)
    }

    // Go: project/logging/logger.go:76 IsVerbose
    fn is_verbose(&self) -> bool {
        self.verbose.get()
    }

    // Go: project/logging/logger.go:85 SetVerbose
    fn set_verbose(&self, verbose: bool) {
        self.verbose.set(verbose);
    }
}

// Go: project/logging/logger.go:118 NewLogger
pub fn new_logger(output: Box<dyn Write>) -> Option<Rc<dyn Logger>> {
    Some(Rc::new(LoggerImpl {
        verbose: Cell::new(false),
        writer: RefCell::new(output),
        prefix: Box::new(|| format_time(SystemTime::now())),
    }))
}

// Go: project/logging/logger.go:129 NewNopLogger
// NewNopLogger returns a no-op Logger that discards all log messages.
// It is safe to call any method on the returned Logger.
// PORT: Go returns a nil `*logger`; the port returns `None`.
pub fn new_nop_logger() -> Option<Rc<dyn Logger>> {
    None
}

// Go: project/logging/logger.go:133 formatTime
pub fn format_time(t: SystemTime) -> String {
    format!("[{}]", format_clock_millis(t))
}

/// Go `t.Format("15:04:05.000")` of a Go `time.Now()`, which is in
/// `time.Local` (the local time zone, from `TZ` or `/etc/localtime`).
pub fn format_clock_millis(t: SystemTime) -> String {
    format_clock_millis_in(t, crate::execute::tsc::diagnostics::local_location())
}

/// Go `t.In(zone).Format("15:04:05.000")`: two-digit hour, minute and
/// second, then milliseconds, truncated (not rounded).
// Go (go1.27.1, the pin N oracle toolchain): time/format.go:667
// (Time).appendFormat, the stdHour (:747), stdZeroMinute (:765),
// stdZeroSecond (:769) and stdFracSecond0 (:831) cases.
// PORT: jiff converts the time to the zone's civil time (Go
// `Time.locabs`). A time outside the jiff range (years -9999 to 9999) is
// not ported.
fn format_clock_millis_in(t: SystemTime, zone: &jiff::tz::TimeZone) -> String {
    let Ok(timestamp) = jiff::Timestamp::try_from(t) else {
        unported!("Time.Format of a time outside years -9999 to 9999");
    };
    let datetime = zone.to_datetime(timestamp);
    format!(
        "{:02}:{:02}:{:02}.{:03}",
        datetime.hour(),
        datetime.minute(),
        datetime.second(),
        datetime.subsec_nanosecond() / 1_000_000
    )
}

// PORT: Go nil-receiver methods of `logger` (the `NewNopLogger` value).
// `None` behaves like a nil `*logger`: every call does nothing, `Verbose`
// is nil and `IsVerbose` is false.
impl Logger for Option<Rc<dyn Logger>> {
    fn error(&self, msg: &str) {
        self.log(msg);
    }

    fn errorf(&self, msg: &str) {
        self.logf(msg);
    }

    fn warn(&self, msg: &str) {
        self.log(msg);
    }

    fn warnf(&self, msg: &str) {
        self.logf(msg);
    }

    fn info(&self, msg: &str) {
        self.log(msg);
    }

    fn infof(&self, msg: &str) {
        self.logf(msg);
    }

    fn log(&self, msg: &str) {
        if let Some(l) = self {
            l.log(msg);
        }
    }

    fn logf(&self, msg: &str) {
        if let Some(l) = self {
            l.logf(msg);
        }
    }

    fn verbose(&self) -> Option<&dyn Logger> {
        match self {
            Some(l) => l.verbose(),
            None => None,
        }
    }

    fn is_verbose(&self) -> bool {
        match self {
            Some(l) => l.is_verbose(),
            None => false,
        }
    }

    fn set_verbose(&self, verbose: bool) {
        if let Some(l) = self {
            l.set_verbose(verbose);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project::logging::logcollector::{LogCollector, new_test_logger};

    /// Set in the child process of `log_time_is_local_time`.
    const CHILD_ENV: &str = "GOPORT_LOGGER_TZ_CHILD";
    const CHILD_TEST: &str = "project::logging::logger::tests::log_time_is_local_time";

    // Go: project/logging/logger.go:133 formatTime prints Go `time.Local`.
    // Go's `NewTestLogger` (logcollector.go:23) prints its fixed time
    // (2012-10-01 10:01:12 UTC) in `time.Local`, so with
    // `TZ=Etc/GMT+7` (UTC-7) the line starts with `[03:01:12.000]`.
    // `time.Local` is read once per process, so the test runs itself again
    // with that `TZ`.
    #[test]
    fn log_time_is_local_time() {
        if std::env::var_os(CHILD_ENV).is_some() {
            let logger = new_test_logger();
            logger.log("x");
            assert_eq!(logger.string(), "[03:01:12.000] x\n");
            return;
        }
        // `/proc/self/exe` still names this binary when a build replaces it.
        let proc_exe = std::path::Path::new("/proc/self/exe");
        let exe = if proc_exe.exists() {
            proc_exe.to_path_buf()
        } else {
            std::env::current_exe().expect("test binary")
        };
        let output = std::process::Command::new(exe)
            .args(["--exact", CHILD_TEST, "--nocapture", "--test-threads", "1"])
            .env(CHILD_ENV, "1")
            .env("TZ", "Etc/GMT+7")
            .stdin(std::process::Stdio::null())
            .output()
            .expect("run the child test");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success() && stdout.contains("1 passed"),
            "child ({}):\n{stdout}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
