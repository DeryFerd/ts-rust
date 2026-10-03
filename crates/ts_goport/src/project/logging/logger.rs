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
use std::time::{SystemTime, UNIX_EPOCH};

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

// PORT: Go `t.Format("15:04:05.000")`: two-digit hour, minute and second,
// then milliseconds, truncated (not rounded). Go prints the local time zone.
// The crate has no time zone database (no dependency may be added), so the
// port prints UTC; log text is not compared by the oracle.
pub fn format_clock_millis(t: SystemTime) -> String {
    let (secs, nanos): (i64, u32) = match t.duration_since(UNIX_EPOCH) {
        Ok(d) => (d.as_secs() as i64, d.subsec_nanos()),
        Err(e) => {
            let d = e.duration();
            let mut secs = -(d.as_secs() as i64);
            let mut nanos = d.subsec_nanos();
            if nanos > 0 {
                secs -= 1;
                nanos = 1_000_000_000 - nanos;
            }
            (secs, nanos)
        }
    };
    let day_secs = secs.rem_euclid(86_400);
    let hour = day_secs / 3_600;
    let minute = (day_secs % 3_600) / 60;
    let second = day_secs % 60;
    let millis = nanos / 1_000_000;
    format!("{:02}:{:02}:{:02}.{:03}", hour, minute, second, millis)
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
