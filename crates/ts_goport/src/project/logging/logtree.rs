//! Go `internal/project/logging/logtree.go`.
//!
//! PORT: Go `*LogTree` is `Option<Rc<LogTree>>` (see
//! `project/dirty/interfaces.rs`, decision 5). The inherent methods below are
//! the non-nil paths. Go's `c == nil` checks are in the `Logger` and
//! `LogTreeMethods` impls on `Option<Rc<LogTree>>` at the end of the file.
//! `mu` is dropped (one thread).

use crate::project::logging::prelude::*;
use std::cell::Cell;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::SystemTime;

// Go: project/logging/logtree.go:11 seq
pub static SEQ: AtomicU64 = AtomicU64::new(0);

// Go: project/logging/logtree.go:13 logEntry
pub struct LogEntry {
    pub seq: u64,
    pub time: SystemTime,
    pub message: String,
    pub child: Option<Rc<LogTree>>,
}

// Go: project/logging/logtree.go:20 newLogEntry
pub fn new_log_entry(child: Option<Rc<LogTree>>, message: String) -> Rc<LogEntry> {
    Rc::new(LogEntry {
        // Go: seq.Add(1) returns the new value.
        seq: SEQ.fetch_add(1, Ordering::SeqCst) + 1,
        time: SystemTime::now(),
        message,
        child,
    })
}

// PORT: Go `LogTree.count` and `LogTree.stringLength` ("Only set on root").
// They live in a shared cell, so a child reaches its root's counters through
// `root` without a strong reference cycle (root -> logs -> child -> root).
// Go reads `c.root` only for these counters and for the `c.root != c` test.
// Go `atomic.Int32` becomes `Cell<i32>` with wrapping adds.
#[derive(Default)]
pub struct LogTreeCounts {
    pub count: Cell<i32>,
    pub string_length: Cell<i32>,
}

// Go: project/logging/logtree.go:31 LogTree
pub struct LogTree {
    pub name: String,
    pub logs: RefCell<Vec<Rc<LogEntry>>>,
    // PORT: Go `root *LogTree`: the root tree's `counts`.
    pub root: Rc<LogTreeCounts>,
    pub level: i32,
    pub verbose: Cell<bool>,

    // Only set on root
    // PORT: Go `count` and `stringLength` of this tree.
    pub counts: Rc<LogTreeCounts>,
}

// Go: project/logging/logtree.go:44 NewLogTree
// PORT: returns the Go `*LogTree` form, `Option<Rc<LogTree>>` (never `None`).
pub fn new_log_tree(name: &str) -> Option<Rc<LogTree>> {
    let counts = Rc::new(LogTreeCounts::default());
    // Go: lc.root = lc
    Some(Rc::new(LogTree {
        name: name.to_string(),
        logs: RefCell::new(Vec::new()),
        root: counts.clone(),
        level: 0,
        verbose: Cell::new(false),
        counts,
    }))
}

impl LogTree {
    // Go: project/logging/logtree.go:52 add
    pub fn add(&self, log: Rc<LogEntry>) {
        // indent + header + message + newline
        let length = self
            .level
            .wrapping_add(15)
            .wrapping_add(log.message.len() as i32)
            .wrapping_add(1);
        self.root
            .string_length
            .set(self.root.string_length.get().wrapping_add(length));
        self.root.count.set(self.root.count.get().wrapping_add(1));
        self.logs.borrow_mut().push(log);
    }

    // Go: project/logging/logtree.go:61 Log
    pub fn log(&self, message: &str) {
        let log = new_log_entry(None, message.to_string());
        self.add(log);
    }

    // Go: project/logging/logtree.go:69 Logf
    pub fn logf(&self, message: &str) {
        let log = new_log_entry(None, message.to_string());
        self.add(log);
    }

    // Go: project/logging/logtree.go:77 IsVerbose
    pub fn is_verbose(&self) -> bool {
        self.verbose.get()
    }

    // Go: project/logging/logtree.go:81 SetVerbose
    pub fn set_verbose(&self, verbose: bool) {
        self.verbose.set(verbose);
    }

    // Go: project/logging/logtree.go:88 Verbose
    pub fn verbose(&self) -> Option<&dyn Logger> {
        if !self.verbose.get() {
            return None;
        }
        Some(self)
    }

    // Go: project/logging/logtree.go:95 Error
    pub fn error(&self, msg: &str) {
        self.log(msg);
    }

    // Go: project/logging/logtree.go:99 Errorf
    pub fn errorf(&self, msg: &str) {
        self.logf(msg);
    }

    // Go: project/logging/logtree.go:103 Warn
    pub fn warn(&self, msg: &str) {
        self.log(msg);
    }

    // Go: project/logging/logtree.go:107 Warnf
    pub fn warnf(&self, msg: &str) {
        self.logf(msg);
    }

    // Go: project/logging/logtree.go:111 Info
    pub fn info(&self, msg: &str) {
        self.log(msg);
    }

    // Go: project/logging/logtree.go:115 Infof
    pub fn infof(&self, msg: &str) {
        self.logf(msg);
    }

    // Go: project/logging/logtree.go:119 Embed
    // PORT: `logs` is a Go `*LogTree`; Go dereferences it without a nil check.
    pub fn embed(&self, logs: &Option<Rc<LogTree>>) {
        let logs = logs.as_ref().expect("nil pointer dereference: LogTree");
        let count = logs.counts.count.get();
        self.root.string_length.set(
            self.root.string_length.get().wrapping_add(
                logs.counts
                    .string_length
                    .get()
                    .wrapping_add(count.wrapping_mul(self.level)),
            ),
        );
        self.root
            .count
            .set(self.root.count.get().wrapping_add(count));
        let log = new_log_entry(Some(logs.clone()), logs.name.clone());
        self.add(log);
    }

    // Go: project/logging/logtree.go:130 Fork
    pub fn fork(&self, message: &str) -> Option<Rc<LogTree>> {
        let child = Rc::new(LogTree {
            name: String::new(),
            logs: RefCell::new(Vec::new()),
            root: self.root.clone(),
            level: self.level + 1,
            verbose: Cell::new(self.verbose.get()),
            counts: Rc::new(LogTreeCounts::default()),
        });
        let log = new_log_entry(Some(child.clone()), message.to_string());
        self.add(log);
        Some(child)
    }

    // Go: project/logging/logtree.go:140 String
    pub fn string(&self) -> String {
        if !Rc::ptr_eq(&self.root, &self.counts) {
            panic!("can only call String on root LogTree");
        }
        let header = format!("======== {} ========\n", self.name);
        // Go: builder.Grow(int(c.stringLength.Load()) + len(header))
        let grow = self.counts.string_length.get() as i64 + header.len() as i64;
        if grow < 0 {
            panic!("strings.Builder.Grow: negative count");
        }
        let mut builder = String::with_capacity(grow as usize);
        builder.push_str(&header);
        self.write_logs_recursive(&mut builder, "");
        builder
    }

    // Go: project/logging/logtree.go:152 writeLogsRecursive
    pub fn write_logs_recursive(&self, builder: &mut String, indent: &str) {
        for log in self.logs.borrow().iter() {
            builder.push_str(indent);
            builder.push_str(&format_time(log.time));
            builder.push(' ');
            builder.push_str(&log.message);
            builder.push('\n');
            if let Some(child) = &log.child {
                child.write_logs_recursive(builder, &format!("{}\t", indent));
            }
        }
    }
}

// Go: project/logging/logtree.go:29 `var _ LogCollector = (*LogTree)(nil)`
impl Logger for LogTree {
    fn error(&self, msg: &str) {
        LogTree::error(self, msg)
    }

    fn errorf(&self, msg: &str) {
        LogTree::errorf(self, msg)
    }

    fn warn(&self, msg: &str) {
        LogTree::warn(self, msg)
    }

    fn warnf(&self, msg: &str) {
        LogTree::warnf(self, msg)
    }

    fn info(&self, msg: &str) {
        LogTree::info(self, msg)
    }

    fn infof(&self, msg: &str) {
        LogTree::infof(self, msg)
    }

    fn log(&self, msg: &str) {
        LogTree::log(self, msg)
    }

    fn logf(&self, msg: &str) {
        LogTree::logf(self, msg)
    }

    fn verbose(&self) -> Option<&dyn Logger> {
        LogTree::verbose(self)
    }

    fn is_verbose(&self) -> bool {
        LogTree::is_verbose(self)
    }

    fn set_verbose(&self, verbose: bool) {
        LogTree::set_verbose(self, verbose)
    }
}

impl LogCollector for LogTree {
    fn string(&self) -> String {
        LogTree::string(self)
    }
}

// PORT: Go `*LogTree` methods with a nil receiver. `Log`, `Logf`,
// `SetVerbose`, `Verbose` (and the Error..Infof wrappers) check for nil;
// `IsVerbose` does not, so a nil tree panics as in Go.
impl Logger for Option<Rc<LogTree>> {
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
        let Some(c) = self else {
            return;
        };
        c.log(msg);
    }

    fn logf(&self, msg: &str) {
        let Some(c) = self else {
            return;
        };
        c.logf(msg);
    }

    fn verbose(&self) -> Option<&dyn Logger> {
        let Some(c) = self else {
            return None;
        };
        c.verbose()
    }

    fn is_verbose(&self) -> bool {
        self.as_ref()
            .expect("nil pointer dereference: LogTree")
            .is_verbose()
    }

    fn set_verbose(&self, verbose: bool) {
        let Some(c) = self else {
            return;
        };
        c.set_verbose(verbose);
    }
}

// PORT: the `LogTree` methods that are not in `Logger`, callable on a Go
// `*LogTree` that may be nil.
pub trait LogTreeMethods {
    fn embed(&self, logs: &Option<Rc<LogTree>>);
    fn fork(&self, message: &str) -> Option<Rc<LogTree>>;
    fn string(&self) -> String;
}

impl LogTreeMethods for Option<Rc<LogTree>> {
    // Go: project/logging/logtree.go:119 Embed (nil check)
    fn embed(&self, logs: &Option<Rc<LogTree>>) {
        let Some(c) = self else {
            return;
        };
        c.embed(logs);
    }

    // Go: project/logging/logtree.go:130 Fork (nil check)
    fn fork(&self, message: &str) -> Option<Rc<LogTree>> {
        let Some(c) = self else {
            return None;
        };
        c.fork(message)
    }

    // Go: project/logging/logtree.go:140 String (no nil check in Go)
    fn string(&self) -> String {
        self.as_ref()
            .expect("nil pointer dereference: LogTree")
            .string()
    }
}
