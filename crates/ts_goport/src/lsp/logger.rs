//! Go `internal/lsp/logger.go`.
//!
//! PORT: Go `Log(msg ...any)` joins its arguments with `fmt.Sprint` and
//! `Logf(format, args...)` formats with `fmt.Sprintf`. As in
//! `project/logging`, callers pass the finished text, so every method takes
//! `&str`. Log text is not compared with Go.

use crate::lsp::prelude::*;

use crate::project::logging;

use std::io::Write as _;
use std::sync::atomic::Ordering;
use std::sync::{Arc, Mutex, MutexGuard, Weak};

// PORT: Go mutexes do not poison.
fn lock<T>(m: &Mutex<T>) -> MutexGuard<'_, T> {
    m.lock().unwrap_or_else(|e| e.into_inner())
}

// Go: lsp/logger.go:11 `var _ logging.Logger = (*logger)(nil)`: the
// `logging::Logger` impl below.

// Go: lsp/logger.go:13 logger
// PORT: Go `server *Server`. The logger runs on the reader thread and the
// dispatch thread, so it points at the `Send` half of the server
// (`ServerShared`). The server owns the logger, so the pointer is `Weak`.
// Go `mu` guards `verbosity`; here the mutex holds it.
pub struct Logger {
    pub server: Weak<ServerShared>,
    pub verbosity: Mutex<lsproto::LogVerbosity>,
}

// Go: lsp/logger.go:19 newLogger
pub fn new_logger(server: Weak<ServerShared>) -> Logger {
    Logger {
        server,
        verbosity: Mutex::new(lsproto::LogVerbosity::INFO),
    }
}

// Go: lsp/logger.go:28 maxVerbosityForMessageType
// maxVerbosityForMessageType returns the least-verbose log level at which
// messages of the given LSP MessageType should still be sent.
pub fn max_verbosity_for_message_type(msg_type: lsproto::MessageType) -> lsproto::LogVerbosity {
    if msg_type == lsproto::MessageType::ERROR {
        lsproto::LogVerbosity::ERROR
    } else if msg_type == lsproto::MessageType::WARNING {
        lsproto::LogVerbosity::WARNING
    } else if msg_type == lsproto::MessageType::INFO {
        lsproto::LogVerbosity::INFO
    } else if msg_type == lsproto::MessageType::DEBUG {
        lsproto::LogVerbosity::DEBUG
    } else {
        lsproto::LogVerbosity::INFO
    }
}

// Go: lsp/logger.go:44 isValidLogVerbosity
// isValidLogVerbosity reports whether v is one of the defined LogVerbosity values.
pub fn is_valid_log_verbosity(v: lsproto::LogVerbosity) -> bool {
    v >= lsproto::LogVerbosity::OFF && v <= lsproto::LogVerbosity::ERROR
}

// PORT: Go checks `l == nil` in every method. The server always has a
// logger, so the checks are dropped.
impl Logger {
    // Go: lsp/logger.go:48 sendLogMessage
    pub fn send_log_message(&self, msg_type: lsproto::MessageType, message: &str) {
        // PORT: the server is gone only after the process stopped using it.
        let Some(server) = self.server.upgrade() else {
            return;
        };

        if !server.init_started.load(Ordering::SeqCst) {
            let _ = writeln!(lock(&server.stderr), "{message}");
            return;
        }

        // Don't send messages that the client will filter out anyway.
        let verbosity = *lock(&self.verbosity);
        if verbosity == lsproto::LogVerbosity::OFF
            || verbosity > max_verbosity_for_message_type(msg_type)
        {
            return;
        }

        let notification =
            lsproto::WINDOW_LOG_MESSAGE_INFO.new_notification_message(lsproto::LogMessageParams {
                type_: msg_type,
                message: message.to_string(),
            });

        let background_ctx = server.background_ctx();
        if server
            .outgoing_queue
            .put(&background_ctx, notification.message())
            .is_err()
            && background_ctx.err().is_some()
        {
            let _ = writeln!(lock(&server.stderr), "{message}");
        }
    }

    // Go: lsp/logger.go:126 IsTracing
    pub fn is_tracing(&self) -> bool {
        *lock(&self.verbosity) == lsproto::LogVerbosity::TRACE
    }

    // Go: lsp/logger.go:135 SetVerbosity
    pub fn set_verbosity(&self, verbosity: lsproto::LogVerbosity) {
        *lock(&self.verbosity) = verbosity;
    }
}

impl logging::Logger for Logger {
    // Go: lsp/logger.go:144 Error
    fn error(&self, msg: &str) {
        self.send_log_message(lsproto::MessageType::ERROR, msg);
    }

    // Go: lsp/logger.go:151 Errorf
    fn errorf(&self, msg: &str) {
        self.send_log_message(lsproto::MessageType::ERROR, msg);
    }

    // Go: lsp/logger.go:158 Warn
    fn warn(&self, msg: &str) {
        self.send_log_message(lsproto::MessageType::WARNING, msg);
    }

    // Go: lsp/logger.go:165 Warnf
    fn warnf(&self, msg: &str) {
        self.send_log_message(lsproto::MessageType::WARNING, msg);
    }

    // Go: lsp/logger.go:172 Info
    fn info(&self, msg: &str) {
        self.send_log_message(lsproto::MessageType::INFO, msg);
    }

    // Go: lsp/logger.go:179 Infof
    fn infof(&self, msg: &str) {
        self.send_log_message(lsproto::MessageType::INFO, msg);
    }

    // Go: lsp/logger.go:78 Log
    fn log(&self, msg: &str) {
        self.send_log_message(lsproto::MessageType::INFO, msg);
    }

    // Go: lsp/logger.go:85 Logf
    fn logf(&self, msg: &str) {
        self.send_log_message(lsproto::MessageType::INFO, msg);
    }

    // Go: lsp/logger.go:92 Verbose
    fn verbose(&self) -> Option<&dyn logging::Logger> {
        let verbosity = *lock(&self.verbosity);
        if verbosity == lsproto::LogVerbosity::OFF || verbosity > lsproto::LogVerbosity::DEBUG {
            return None;
        }
        Some(self)
    }

    // Go: lsp/logger.go:104 IsVerbose
    fn is_verbose(&self) -> bool {
        let verbosity = *lock(&self.verbosity);
        verbosity >= lsproto::LogVerbosity::TRACE && verbosity <= lsproto::LogVerbosity::DEBUG
    }

    // Go: lsp/logger.go:113 SetVerbose
    fn set_verbose(&self, verbose: bool) {
        let mut verbosity = lock(&self.verbosity);
        if verbose {
            *verbosity = lsproto::LogVerbosity::DEBUG;
        } else {
            *verbosity = lsproto::LogVerbosity::INFO;
        }
    }
}

// PORT: Go hands the same `*logger` to the session and the lspwatcher as a
// `logging.Logger`. The logger is shared with the reader thread through an
// `Arc`, and those consumers hold `Rc<dyn logging::Logger>`, so they get
// `Rc::new(arc_logger)`; this impl forwards to the logger.
impl logging::Logger for Arc<Logger> {
    fn error(&self, msg: &str) {
        (**self).error(msg);
    }

    fn errorf(&self, msg: &str) {
        (**self).errorf(msg);
    }

    fn warn(&self, msg: &str) {
        (**self).warn(msg);
    }

    fn warnf(&self, msg: &str) {
        (**self).warnf(msg);
    }

    fn info(&self, msg: &str) {
        (**self).info(msg);
    }

    fn infof(&self, msg: &str) {
        (**self).infof(msg);
    }

    fn log(&self, msg: &str) {
        (**self).log(msg);
    }

    fn logf(&self, msg: &str) {
        (**self).logf(msg);
    }

    fn verbose(&self) -> Option<&dyn logging::Logger> {
        (**self).verbose()
    }

    fn is_verbose(&self) -> bool {
        (**self).is_verbose()
    }

    fn set_verbose(&self, verbose: bool) {
        (**self).set_verbose(verbose);
    }
}
