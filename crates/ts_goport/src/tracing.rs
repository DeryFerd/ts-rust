//! Go: tracing/tracing.go (the `--generateTrace` session: trace.json,
//! types_N.json and legend.json), checker/tracer.go (the checker's tracer
//! and its type adapter) and the execute/tsc.go helpers
//! `startTracingIfNeeded` and `stopTracing`.
//!
//! PORT: Go passes the `*tracing.Tracing` through `ProgramOptions`,
//! `EmitInput` and the checker pool. The port has one program per process
//! (see `program.rs`), so the session is a process global: `get()` returns
//! it, or None when tracing is off (Go `tr == nil`). Each checker keeps its
//! `Tracer` in `Checker::tracer` as in Go.
//!
//! PORT: Go `Push` returns the `func()` that ends the event. Here it returns
//! a `Pop`; the event ends when the `Pop` drops, so Go
//! `defer tr.Push(...)()` is `let _trace = tr.push(...)`, which ends at the
//! end of the enclosing Rust scope.
//!
//! PORT: Go `map[string]any` args are `Args`: a list of (key, value) pairs.
//! Go writes the keys sorted (`json.Deterministic`); the writer here sorts
//! them the same way. No Go call site passes an empty non-nil map, so an
//! empty `Args` is the Go nil map and is left out of the JSON.
//!
//! PORT: Go writes through the program `vfs.FS`. The session is shared by
//! the checker threads, so it writes with `std::fs`, with the same
//! create-directory-and-retry step as Go `osvfs` `WriteFile`/`AppendFile`.
//! OS error texts are the Rust `io::Error` texts, not the Go ones. A test
//! process that installs an OS override writes through `osvfs_fs()`
//! instead (see `write_file`).

use crate::execute::incremental::emit_files::fs_error_text;
use crate::prelude::*;

use std::borrow::Cow;
use std::fmt::Write as _;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, MutexGuard, OnceLock, PoisonError};

// ---------------------------------------------------------------------------
// Session
// ---------------------------------------------------------------------------

/// The tracing session of the process. Set once by `start_tracing`.
static TRACING: OnceLock<Tracing> = OnceLock::new();

/// The tracing session, or None when `--generateTrace` is off.
#[inline]
pub fn get() -> Option<&'static Tracing> {
    TRACING.get()
}

// Go: tracing/tracing.go:70 TraceRecord
#[derive(Clone, Debug, Default)]
pub struct TraceRecord {
    pub config_file_path: String,
    pub trace_path: String,
    pub types_path: String,
    pub checker_id: i64,
}

// Go: tracing/tracing.go:77 traceEvent
struct TraceEvent<'a> {
    pid: i64,
    tid: i64,
    ph: &'static str,
    cat: &'static str,
    ts: f64,
    name: &'static str,
    /// scope, only set for instant events ("g" = global)
    s: &'static str,
    dur: Option<f64>,
    args: &'a [(&'static str, Arg)],
}

// sampleInterval matches TypeScript's 10ms sampling interval.
// Events with separateBeginAndEnd=false are only recorded if their
// duration crosses a 10ms sampling boundary.
// Go: tracing/tracing.go:92 sampleInterval
const SAMPLE_INTERVAL: std::time::Duration = std::time::Duration::from_millis(10);

// Go: tracing/tracing.go:94 traceFileName
const TRACE_FILE_NAME: &str = "trace.json";

// Go: tracing/tracing.go:96
const MAIN_THREAD_ID: i64 = 1;
const FIRST_SYNTHETIC_THREAD_ID: i64 = 2;
const FIRST_FILE_THREAD_ID: i64 = 1_000_000;
const FILE_THREAD_ID_HASH_RANGE: u64 = 1_000_000_000;

// Go: tracing/tracing.go:103 traceThreadArgKeys
const TRACE_THREAD_ARG_KEYS: [&str; 5] = [
    "path",
    "fileName",
    "containingFileName",
    "jsFilePath",
    "declarationFilePath",
];

// flushThreshold is the size at which buffered trace content is flushed to disk
// via AppendFile. Keeps peak memory bounded for long-running compilations while
// avoiding a syscall per event.
// Go: tracing/tracing.go:108 flushThreshold
const FLUSH_THRESHOLD: usize = 256 * 1024;

// Go: tracing/tracing.go:111 Tracing
// Tracing manages the overall tracing session including all checkers.
// PORT: the Go fields that `mu` guards are in `TracingState`. Go `fs` is
// `std::fs`, or `osvfs_fs()` in a test process (see the module comment).
// Go `tracers` is not kept: each checker holds its own `TypeTracer` (see
// `stop_tracing`).
pub struct Tracing {
    trace_dir: String,
    trace_path: String,
    config_file_path: String,
    trace_started: AtomicBool,
    metadata_ts: f64,
    /// when true, use monotonic counter instead of real time
    deterministic: bool,
    start_time: std::time::Instant,
    state: Mutex<TracingState>,
}

struct TracingState {
    legend: Vec<TraceRecord>,
    trace_content: String,
    thread_ids: FxHashMap<TraceThreadKey, i64>,
    thread_keys: FxHashMap<i64, TraceThreadKey>,
    /// only used in deterministic mode
    timestamp_counter: u64,
    // flushErr holds the first error encountered while appending the trace buffer
    // to disk. Once set, subsequent flushes become no-ops and the error is
    // surfaced from StopTracing so that transient I/O failures (disk full,
    // permission denied, etc.) don't crash the compiler.
    flush_err: Option<String>,
}

// Go: tracing/tracing.go:133 Phase
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Phase {
    Parse,
    Program,
    Bind,
    Check,
    CheckTypes,
    Emit,
    Session,
}

impl Phase {
    // Go: tracing/tracing.go:136 (the Phase string values)
    #[must_use]
    pub fn as_str(self) -> &'static str {
        match self {
            Phase::Parse => "parse",
            Phase::Program => "program",
            Phase::Bind => "bind",
            Phase::Check => "check",
            Phase::CheckTypes => "checkTypes",
            Phase::Emit => "emit",
            Phase::Session => "session",
        }
    }
}

/// A Go `any` value of a trace event argument.
#[derive(Clone, Debug)]
pub enum Arg {
    Int(i64),
    Str(Cow<'static, str>),
    Bool(bool),
    Strs(Vec<String>),
}

/// Go `map[string]any` trace event arguments (see the module comment).
pub type Args = Vec<(&'static str, Arg)>;

impl From<i32> for Arg {
    fn from(value: i32) -> Self {
        Arg::Int(i64::from(value))
    }
}

impl From<u32> for Arg {
    fn from(value: u32) -> Self {
        Arg::Int(i64::from(value))
    }
}

impl From<i64> for Arg {
    fn from(value: i64) -> Self {
        Arg::Int(value)
    }
}

impl From<usize> for Arg {
    fn from(value: usize) -> Self {
        Arg::Int(value as i64)
    }
}

impl From<bool> for Arg {
    fn from(value: bool) -> Self {
        Arg::Bool(value)
    }
}

impl From<&'static str> for Arg {
    fn from(value: &'static str) -> Self {
        Arg::Str(Cow::Borrowed(value))
    }
}

impl From<String> for Arg {
    fn from(value: String) -> Self {
        Arg::Str(Cow::Owned(value))
    }
}

impl From<Vec<String>> for Arg {
    fn from(value: Vec<String>) -> Self {
        Arg::Strs(value)
    }
}

/// Go `ast.Kind` values are ints.
impl From<SyntaxKind> for Arg {
    fn from(value: SyntaxKind) -> Self {
        Arg::Int(value as i64)
    }
}

/// Go `TypeId` values are ints (the type id number).
impl From<TypeId> for Arg {
    fn from(value: TypeId) -> Self {
        Arg::Int(i64::from(value.0))
    }
}

fn find_arg<'a>(args: &'a [(&'static str, Arg)], key: &str) -> Option<&'a Arg> {
    args.iter().find(|(k, _)| *k == key).map(|(_, v)| v)
}

/// The args that Go `checkDeferredNode`, `checkVariableDeclaration` and
/// `checkExpressionEx` pass: `{"kind": node.Kind, "pos": node.Pos(),
/// "end": node.End(), "path": ast.GetSourceFileOfNode(node).FileName()}`.
#[must_use]
pub fn node_args(node: Node) -> Args {
    vec![
        ("kind", node.kind().into()),
        ("pos", node.pos().into()),
        ("end", node.end().into()),
        (
            "path",
            source_file_file_name(get_source_file_of_node(node)).into(),
        ),
    ]
}

// Go: tracing/tracing.go:149 StartTracing
// StartTracing creates a new tracing session.
// When deterministic is true, timestamps use a monotonic counter instead of
// real wall-clock time, producing stable output for test baselines.
// PORT: the session is the process global (`get`). A second start fails.
pub fn start_tracing(
    trace_dir: &str,
    config_file_path: &str,
    deterministic: bool,
) -> Result<&'static Tracing, String> {
    if TRACING.get().is_some() {
        return Err("tracing already started".to_string());
    }
    let trace_path = crate::frontend::tspath::combine_paths(trace_dir, &[TRACE_FILE_NAME]);
    let mut state = TracingState {
        legend: Vec::new(),
        trace_content: String::new(),
        thread_ids: FxHashMap::default(),
        thread_keys: FxHashMap::default(),
        timestamp_counter: 0,
        flush_err: None,
    };
    let start_time = std::time::Instant::now();

    // Write the trace file header with metadata events
    state.trace_content.push_str("[\n");

    // Write metadata events (matching TypeScript's format)
    let meta_ts = timestamp(deterministic, start_time, &mut state);
    let name_arg = |name: &'static str| -> Args { vec![("name", name.into())] };
    let process_name = name_arg("tsgo");
    write_event(
        &mut state.trace_content,
        &TraceEvent {
            pid: 1,
            tid: MAIN_THREAD_ID,
            ph: "M",
            cat: "__metadata",
            ts: meta_ts,
            name: "process_name",
            s: "",
            dur: None,
            args: &process_name,
        },
    );
    state.trace_content.push_str(",\n");
    let thread_name = name_arg("Main");
    write_event(
        &mut state.trace_content,
        &TraceEvent {
            pid: 1,
            tid: MAIN_THREAD_ID,
            ph: "M",
            cat: "__metadata",
            ts: meta_ts,
            name: "thread_name",
            s: "",
            dur: None,
            args: &thread_name,
        },
    );
    state.trace_content.push_str(",\n");
    write_event(
        &mut state.trace_content,
        &TraceEvent {
            pid: 1,
            tid: MAIN_THREAD_ID,
            ph: "M",
            cat: "disabled-by-default-devtools.timeline",
            ts: meta_ts,
            name: "TracingStartedInBrowser",
            s: "",
            dur: None,
            args: &[],
        },
    );

    // Truncate any existing trace file with the header so subsequent AppendFile
    // calls extend a clean file.
    if let Err(err) = write_file(&trace_path, &state.trace_content) {
        return Err(format!("failed to write trace file header: {err}"));
    }
    state.trace_content.clear();

    let tr = Tracing {
        trace_dir: trace_dir.to_string(),
        trace_path,
        config_file_path: config_file_path.to_string(),
        trace_started: AtomicBool::new(true),
        metadata_ts: meta_ts,
        deterministic,
        start_time,
        state: Mutex::new(state),
    };
    if TRACING.set(tr).is_err() {
        return Err("tracing already started".to_string());
    }
    Ok(TRACING.get().expect("tracing session set above"))
}

// Go: tracing/tracing.go:187 (*Tracing).timestamp
// timestamp returns the current timestamp in microseconds.
// In deterministic mode it returns a monotonically increasing counter;
// otherwise it returns the real elapsed wall-clock time since tracing started,
// matching TypeScript's 1000 * timestamp() (microseconds).
// PORT: a free function so `start_tracing` can call it before the session
// exists.
fn timestamp(deterministic: bool, start_time: std::time::Instant, state: &mut TracingState) -> f64 {
    if deterministic {
        state.timestamp_counter += 1;
        return state.timestamp_counter as f64;
    }
    micros(start_time.elapsed())
}

/// Go `float64(d.Nanoseconds()) / 1000.0`.
fn micros(d: std::time::Duration) -> f64 {
    d.as_nanos() as f64 / 1000.0
}

// Go: tracing/tracing.go:195 writeEventTo
fn write_event(buf: &mut String, event: &TraceEvent<'_>) {
    let _ = write!(buf, "{{\"pid\":{},\"tid\":{},\"ph\":", event.pid, event.tid);
    write_json_string(buf, event.ph);
    buf.push_str(",\"cat\":");
    write_json_string(buf, event.cat);
    buf.push_str(",\"ts\":");
    write_json_float(buf, event.ts);
    if !event.name.is_empty() {
        buf.push_str(",\"name\":");
        write_json_string(buf, event.name);
    }
    if !event.s.is_empty() {
        buf.push_str(",\"s\":");
        write_json_string(buf, event.s);
    }
    if let Some(dur) = event.dur {
        buf.push_str(",\"dur\":");
        write_json_float(buf, dur);
    }
    if !event.args.is_empty() {
        buf.push_str(",\"args\":");
        write_args(buf, event.args);
    }
    buf.push('}');
}

/// Go `json.Deterministic(true)` map output: the keys in byte order.
fn write_args(buf: &mut String, args: &[(&'static str, Arg)]) {
    let mut sorted: Vec<&(&'static str, Arg)> = args.iter().collect();
    sorted.sort_by(|a, b| a.0.cmp(b.0));
    buf.push('{');
    for (i, (key, value)) in sorted.into_iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write_json_string(buf, key);
        buf.push(':');
        match value {
            Arg::Int(n) => {
                let _ = write!(buf, "{n}");
            }
            Arg::Str(s) => write_json_string(buf, s),
            Arg::Bool(b) => buf.push_str(if *b { "true" } else { "false" }),
            Arg::Strs(list) => {
                buf.push('[');
                for (j, s) in list.iter().enumerate() {
                    if j > 0 {
                        buf.push(',');
                    }
                    write_json_string(buf, s);
                }
                buf.push(']');
            }
        }
    }
    buf.push('}');
}

impl Tracing {
    fn lock(&self) -> MutexGuard<'_, TracingState> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }

    fn timestamp(&self, state: &mut TracingState) -> f64 {
        timestamp(self.deterministic, self.start_time, state)
    }

    // Go: tracing/tracing.go:205 (*Tracing).writeEvent
    fn write_event_locked(state: &mut TracingState, event: &TraceEvent<'_>) {
        write_event(&mut state.trace_content, event);
    }

    // Go: tracing/tracing.go:213 (*Tracing).maybeFlushLocked
    // maybeFlushLocked appends the buffered trace content to disk if it has grown
    // past the flush threshold. Caller must hold tr.mu. If a previous flush failed,
    // or this flush fails, the error is recorded in tr.flushErr and subsequent
    // writes become no-ops; the error is surfaced from StopTracing.
    fn maybe_flush_locked(&self, state: &mut TracingState) {
        if state.flush_err.is_some() {
            state.trace_content.clear();
            return;
        }
        if state.trace_content.len() < FLUSH_THRESHOLD {
            return;
        }
        if let Err(err) = append_file(&self.trace_path, &state.trace_content) {
            state.flush_err = Some(format!("failed to flush trace file: {err}"));
        }
        state.trace_content.clear();
    }

    // Go: tracing/tracing.go:229 (*Tracing).Instant
    // Instant records an instant event in the trace.
    pub fn instant(&self, phase: Phase, name: &'static str, args: Args) {
        if !self.trace_started.load(Ordering::Acquire) {
            return;
        }

        let mut state = self.lock();

        // Re-check under the lock: StopTracing may have run between the load above
        // and acquiring the lock. Once stopped, further writes would land in a buffer
        // that has already been flushed and the closing "]" written.
        if !self.trace_started.load(Ordering::Acquire) {
            return;
        }

        let ts = self.timestamp(&mut state);
        let tid = self.thread_id_locked(&mut state, &args);
        state.trace_content.push_str(",\n");
        Self::write_event_locked(
            &mut state,
            &TraceEvent {
                pid: 1,
                tid,
                ph: "I",
                cat: phase.as_str(),
                ts,
                name,
                s: "g",
                dur: None,
                args: &args,
            },
        );
        self.maybe_flush_locked(&mut state);
    }

    // Go: tracing/tracing.go:266 (*Tracing).Push
    // Push starts a trace event block on the shared trace buffer.
    // Safe to call from multiple threads.
    //
    // When separateBeginAndEnd is true, a "B" (begin) event is written immediately and
    // the returned value writes a matching "E" (end) event. This is used for events
    // that must always appear in the trace (e.g. checkSourceFile, createProgram, emit).
    //
    // When separateBeginAndEnd is false (the default in TypeScript), the event is only
    // recorded if its duration crosses a 10ms sampling boundary, matching TypeScript's
    // behavior of sampling short-lived events to avoid trace bloat.
    //
    // Returns a `Pop` that ends the event when it drops. Each one is
    // self-contained and does not depend on a shared stack.
    pub fn push(
        &'static self,
        phase: Phase,
        name: &'static str,
        args: Args,
        separate_begin_and_end: bool,
    ) -> Pop {
        if !self.trace_started.load(Ordering::Acquire) {
            return Pop(None);
        }

        if separate_begin_and_end {
            let mut state = self.lock();
            if !self.trace_started.load(Ordering::Acquire) {
                return Pop(None);
            }
            let ts = self.timestamp(&mut state);
            let tid = self.thread_id_locked(&mut state, &args);
            state.trace_content.push_str(",\n");
            Self::write_event_locked(
                &mut state,
                &TraceEvent {
                    pid: 1,
                    tid,
                    ph: "B",
                    cat: phase.as_str(),
                    ts,
                    name,
                    s: "",
                    dur: None,
                    args: &args,
                },
            );
            self.maybe_flush_locked(&mut state);
            drop(state);

            return Pop(Some(Box::new(PopState {
                tracing: self,
                phase,
                name,
                args,
                kind: PopKind::End { tid },
            })));
        }

        // Sampled event: only record if duration crosses a sampling boundary.
        // In deterministic mode, sampled events are skipped entirely to avoid flaky baselines,
        // so avoid the cost of cloning args / capturing the start time.
        if self.deterministic {
            return Pop(None);
        }
        let start_time = std::time::Instant::now();
        Pop(Some(Box::new(PopState {
            tracing: self,
            phase,
            name,
            args,
            kind: PopKind::Sampled { start_time },
        })))
    }

    // Go: tracing/tracing.go:324 (*Tracing).threadIDLocked
    fn thread_id_locked(&self, state: &mut TracingState, args: &[(&'static str, Arg)]) -> i64 {
        let Some(key) = trace_thread_key_from_args(args) else {
            return MAIN_THREAD_ID;
        };

        if let Some(&tid) = state.thread_ids.get(&key) {
            return tid;
        }

        let mut tid = key.default_thread_id();
        loop {
            match state.thread_keys.get(&tid) {
                Some(existing_key) if *existing_key != key => tid += 1,
                _ => break,
            }
        }
        state.thread_ids.insert(key.clone(), tid);
        state.thread_keys.insert(tid, key.clone());
        self.write_thread_name_event_locked(state, tid, key.display_name());
        tid
    }

    // Go: tracing/tracing.go:346 (*Tracing).writeThreadNameEventLocked
    fn write_thread_name_event_locked(&self, state: &mut TracingState, tid: i64, name: String) {
        state.trace_content.push_str(",\n");
        let args: Args = vec![("name", name.into())];
        Self::write_event_locked(
            state,
            &TraceEvent {
                pid: 1,
                tid,
                ph: "M",
                cat: "__metadata",
                ts: self.metadata_ts,
                name: "thread_name",
                s: "",
                dur: None,
                args: &args,
            },
        );
    }

    // Go: tracing/tracing.go:411 (*Tracing).NewTypeTracer
    // NewTypeTracer creates a new tracer for a specific checker.
    // The checkerIndex is used to create unique filenames for each checker's output.
    // PORT: `goport` replaces a checker that panicked with a new checker of
    // the same index. Its tracer replaces the old one: the legend keeps one
    // entry per index, and the old checker's types are not dumped (their
    // ids belong to the dropped checker).
    pub fn new_type_tracer(&self, checker_index: usize) -> &'static TypeTracer {
        let mut state = self.lock();

        let types_path = crate::frontend::tspath::combine_paths(
            &self.trace_dir,
            &[&format!("types_{checker_index}.json")],
        );
        let tracer: &'static TypeTracer = Box::leak(Box::new(TypeTracer {
            checker_index,
            types_path: types_path.clone(),
            types: Mutex::new(Vec::new()),
        }));
        let checker_id = checker_index as i64;
        if !state.legend.iter().any(|r| r.checker_id == checker_id) {
            state.legend.push(TraceRecord {
                config_file_path: self.config_file_path.clone(),
                trace_path: self.trace_path.clone(),
                types_path,
                checker_id,
            });
        }
        tracer
    }

    // Go: tracing/tracing.go:434 (*Tracing).StopTracing
    // StopTracing finalizes the tracing session and writes all output files.
    // PORT: Go dumps the types of every `tr.tracers` entry. Each checker
    // lives on its own worker thread here, so each dumps its own types there
    // (`program::for_each_checker_parallel`). Only checkers that exist are
    // dumped: the pool is not made for this.
    pub fn stop_tracing(&'static self) -> Result<(), String> {
        // Dump types from all tracers BEFORE acquiring the lock, because
        // DumpTypes → buildTypeDescriptor → Display() → TypeToString can
        // re-enter the checker which calls Push/Pop (which need tr.mu).
        if crate::program::checker_pool_created() {
            for result in crate::program::for_each_checker_parallel(dump_checker_types) {
                result?;
            }
        }

        let mut state = self.lock();

        // Close the trace file(s)
        if self.trace_started.load(Ordering::Acquire) {
            // Surface any buffered flush failure before attempting the final write.
            if let Some(err) = state.flush_err.clone() {
                state.trace_content.clear();
                self.trace_started.store(false, Ordering::Release);
                return Err(err);
            }
            // Flush any remaining buffered content and close the JSON array.
            let content = format!("{}\n]\n", state.trace_content);
            if let Err(err) = append_file(&self.trace_path, &content) {
                return Err(format!("failed to write trace file: {err}"));
            }
            state.trace_content.clear();
            self.trace_started.store(false, Ordering::Release);
        }

        // Sort legend entries by typesPath for deterministic output
        state
            .legend
            .sort_by(|a, b| a.types_path.as_str().cmp(b.types_path.as_str()));

        // Write the legend file
        let legend_path = crate::frontend::tspath::combine_paths(&self.trace_dir, &["legend.json"]);
        let legend_data = marshal_legend(&state.legend);
        if let Err(err) = write_file(&legend_path, &legend_data) {
            return Err(format!("failed to write legend file: {err}"));
        }

        Ok(())
    }
}

/// A trace event that has begun. It ends when it drops (Go calls the
/// function that `Push` returns).
///
/// PORT: the state is boxed so an `Option<Pop>` is one word on the stack of
/// the recursive checker functions that hold one.
#[must_use = "the trace event ends when this value drops; bind it to a named variable"]
pub struct Pop(Option<Box<PopState>>);

struct PopState {
    tracing: &'static Tracing,
    phase: Phase,
    name: &'static str,
    args: Args,
    kind: PopKind,
}

enum PopKind {
    /// A "B" event was written; the "E" event uses the same thread.
    End { tid: i64 },
    /// A sampled event that started at `start_time`.
    Sampled { start_time: std::time::Instant },
}

impl Pop {
    /// The args that the end event writes. Go `getVariancesWorker` adds
    /// "variances" to its args map before it ends the event; the "E" event
    /// shows it. None when the event is not recorded.
    pub fn args_mut(&mut self) -> Option<&mut Args> {
        self.0.as_mut().map(|state| &mut state.args)
    }
}

impl Drop for Pop {
    // Go: tracing/tracing.go:289 (the closure that ends a separate event) and
    // tracing/tracing.go:307 (the closure that ends a sampled event).
    fn drop(&mut self) {
        let Some(pop) = self.0.take() else {
            return;
        };
        let tr = pop.tracing;
        match pop.kind {
            PopKind::End { tid } => {
                let mut state = tr.lock();
                if !tr.trace_started.load(Ordering::Acquire) {
                    return;
                }
                let end_ts = tr.timestamp(&mut state);
                state.trace_content.push_str(",\n");
                Tracing::write_event_locked(
                    &mut state,
                    &TraceEvent {
                        pid: 1,
                        tid,
                        ph: "E",
                        cat: pop.phase.as_str(),
                        ts: end_ts,
                        name: pop.name,
                        s: "",
                        dur: None,
                        args: &pop.args,
                    },
                );
                tr.maybe_flush_locked(&mut state);
            }
            PopKind::Sampled { start_time } => {
                let dur = micros(start_time.elapsed());
                let start_micros = micros(start_time.saturating_duration_since(tr.start_time));
                let interval_micros = micros(SAMPLE_INTERVAL);
                if interval_micros - start_micros % interval_micros > dur {
                    return;
                }
                let mut state = tr.lock();
                if !tr.trace_started.load(Ordering::Acquire) {
                    return;
                }
                let tid = tr.thread_id_locked(&mut state, &pop.args);
                state.trace_content.push_str(",\n");
                Tracing::write_event_locked(
                    &mut state,
                    &TraceEvent {
                        pid: 1,
                        tid,
                        ph: "X",
                        cat: pop.phase.as_str(),
                        ts: start_micros,
                        name: pop.name,
                        s: "",
                        dur: Some(dur),
                        args: &pop.args,
                    },
                );
                tr.maybe_flush_locked(&mut state);
            }
        }
    }
}

// Go: tracing/tracing.go:351 traceThreadKind
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum TraceThreadKind {
    Checker,
    File,
}

impl TraceThreadKind {
    fn as_str(self) -> &'static str {
        match self {
            TraceThreadKind::Checker => "checker",
            TraceThreadKind::File => "file",
        }
    }
}

// Go: tracing/tracing.go:358 traceThreadKey
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct TraceThreadKey {
    kind: TraceThreadKind,
    text: String,
    index: i64,
    has_index: bool,
}

// Go: tracing/tracing.go:365 traceThreadKeyFromArgs
fn trace_thread_key_from_args(args: &[(&'static str, Arg)]) -> Option<TraceThreadKey> {
    if args.is_empty() {
        return None;
    }

    if let Some(Arg::Int(checker_id)) = find_arg(args, "checkerId") {
        return Some(TraceThreadKey {
            kind: TraceThreadKind::Checker,
            text: String::new(),
            index: *checker_id,
            has_index: true,
        });
    }

    for key in TRACE_THREAD_ARG_KEYS {
        if let Some(Arg::Str(path)) = find_arg(args, key) {
            if !path.is_empty() {
                return Some(TraceThreadKey {
                    kind: TraceThreadKind::File,
                    text: path.to_string(),
                    index: 0,
                    has_index: false,
                });
            }
        }
    }

    None
}

impl TraceThreadKey {
    // Go: tracing/tracing.go:385 traceThreadKey.defaultThreadID
    fn default_thread_id(&self) -> i64 {
        if self.kind == TraceThreadKind::Checker && self.has_index && self.index >= 0 {
            return FIRST_SYNTHETIC_THREAD_ID + self.index;
        }
        stable_trace_thread_id(self)
    }

    // Go: tracing/tracing.go:392 traceThreadKey.displayName
    fn display_name(&self) -> String {
        if self.has_index {
            return format!("{}:{}", self.kind.as_str(), self.index);
        }
        format!("{}:{}", self.kind.as_str(), self.text)
    }
}

// Go: tracing/tracing.go:399 stableTraceThreadID
// PORT: Go writes the parts into a streaming xxh3 hasher (seed 0); the hash
// of the joined bytes is the same.
fn stable_trace_thread_id(key: &TraceThreadKey) -> i64 {
    let text = if key.has_index {
        format!("{}:{}", key.kind.as_str(), key.index)
    } else {
        format!("{}:{}", key.kind.as_str(), key.text)
    };
    let hash = xxhash_rust::xxh3::xxh3_64(text.as_bytes());
    FIRST_FILE_THREAD_ID + (hash % FILE_THREAD_ID_HASH_RANGE) as i64
}

// Go: tracing/tracing.go:434 json.MarshalIndent(tr.legend, "", "  ")
// PORT: the Go v2 JSON indent output, written by hand.
fn marshal_legend(legend: &[TraceRecord]) -> String {
    if legend.is_empty() {
        return "[]".to_string();
    }
    let mut out = String::from("[\n");
    for (i, record) in legend.iter().enumerate() {
        if i > 0 {
            out.push_str(",\n");
        }
        out.push_str("  {\n");
        let mut fields: Vec<String> = Vec::new();
        for (key, value) in [
            ("configFilePath", &record.config_file_path),
            ("tracePath", &record.trace_path),
            ("typesPath", &record.types_path),
        ] {
            // `omitzero`
            if !value.is_empty() {
                let mut field = format!("    \"{key}\": ");
                write_json_string(&mut field, value);
                fields.push(field);
            }
        }
        fields.push(format!("    \"checkerId\": {}", record.checker_id));
        out.push_str(&fields.join(",\n"));
        out.push_str("\n  }");
    }
    out.push_str("\n]");
    out
}

// ---------------------------------------------------------------------------
// Type tracer
// ---------------------------------------------------------------------------

// Go: tracing/tracing.go:487 typeTracer
// typeTracer is the per-checker tracer implementation
// PORT: Go keeps `*TracedType` values; the port keeps the type ids, which
// index the checker's arena.
pub struct TypeTracer {
    checker_index: usize,
    types_path: String,
    types: Mutex<Vec<TypeId>>,
}

impl TypeTracer {
    // Go: tracing/tracing.go:495 (*typeTracer).RecordType
    pub fn record_type(&self, t: TypeId) {
        self.types
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(t);
    }

    // Go: tracing/tracing.go:501 (*typeTracer).DumpTypes
    // PORT: Go reaches the checker through each type. Here the checker that
    // owns the types is passed in.
    pub fn dump_types(&self, checker: &mut Checker) -> Result<(), String> {
        // Copy the types slice under lock, then release so Display() calls during
        // buildTypeDescriptor don't deadlock when they create new types
        let types = self
            .types
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone();

        if types.is_empty() {
            return Ok(());
        }

        let mut sb = String::new();
        // Write opening bracket (no newline so type ID matches line number)
        sb.push('[');

        let mut recursion_identity_map: FxHashMap<RecursionId, i64> = FxHashMap::default();

        for (i, &t) in types.iter().enumerate() {
            let descriptor = build_type_descriptor(checker, t, &mut recursion_identity_map);
            descriptor.write_json(&mut sb);

            if i < types.len() - 1 {
                sb.push_str(",\n");
            }
        }

        sb.push_str("]\n");

        write_file(&self.types_path, &sb).map_err(|err| err.to_string())
    }
}

/// The body of the `for_each_checker_parallel` job that `stop_tracing` runs
/// on each checker thread.
fn dump_checker_types(index: usize, checker: &mut Checker) -> Result<(), String> {
    let Some(tracer) = checker.tracer else {
        return Ok(());
    };
    tracer
        .recorder
        .dump_types(checker)
        .map_err(|err| format!("failed to dump types for checker {index}: {err}"))
}

// Go: tracing/tracing.go:538 TypeDescriptor
// TypeDescriptor represents a type in the output JSON
// PORT: Go `omitzero` fields: an empty `Vec`, an empty `String` and `None`
// are left out.
#[derive(Default)]
struct TypeDescriptor {
    id: u32,
    intrinsic_name: String,
    symbol_name: String,
    recursion_id: Option<i64>,
    is_tuple: bool,
    union_types: Vec<u32>,
    intersection_types: Vec<u32>,
    alias_type_arguments: Vec<u32>,
    keyof_type: Option<i64>,
    indexed_access_object_type: Option<i64>,
    indexed_access_index_type: Option<i64>,
    conditional_check_type: Option<i64>,
    conditional_extends_type: Option<i64>,
    // ConditionalTrueType and ConditionalFalseType can be -1: unresolved
    // conditional branches are serialized as -1, matching TypeScript's behavior.
    conditional_true_type: Option<i64>,
    conditional_false_type: Option<i64>,
    substitution_base_type: Option<i64>,
    constraint_type: Option<i64>,
    instantiated_type: Option<i64>,
    type_arguments: Vec<u32>,
    reference_location: Option<Location>,
    reverse_mapped_source_type: Option<i64>,
    reverse_mapped_mapped_type: Option<i64>,
    reverse_mapped_constraint_type: Option<i64>,
    evolving_array_element_type: Option<i64>,
    evolving_array_final_type: Option<i64>,
    destructuring_pattern: Option<Location>,
    first_declaration: Option<Location>,
    flags: Vec<String>,
    display: String,
}

// Go: tracing/tracing.go:573 Location
// Location represents a source code location
struct Location {
    path: String,
    start: Option<LineAndChar>,
    end: Option<LineAndChar>,
}

// Go: tracing/tracing.go:580 LineAndChar
// LineAndChar represents a line and character position (1-indexed)
struct LineAndChar {
    line: i32,
    character: i32,
}

impl TypeDescriptor {
    /// Go `json.MarshalWrite(&sb, descriptor)`: the fields in Go order.
    fn write_json(&self, out: &mut String) {
        let _ = write!(out, "{{\"id\":{}", self.id);
        if !self.intrinsic_name.is_empty() {
            out.push_str(",\"intrinsicName\":");
            write_json_string(out, &self.intrinsic_name);
        }
        if !self.symbol_name.is_empty() {
            out.push_str(",\"symbolName\":");
            write_json_string(out, &self.symbol_name);
        }
        write_opt_int(out, "recursionId", self.recursion_id);
        if self.is_tuple {
            out.push_str(",\"isTuple\":true");
        }
        write_id_list(out, "unionTypes", &self.union_types);
        write_id_list(out, "intersectionTypes", &self.intersection_types);
        write_id_list(out, "aliasTypeArguments", &self.alias_type_arguments);
        write_opt_int(out, "keyofType", self.keyof_type);
        write_opt_int(
            out,
            "indexedAccessObjectType",
            self.indexed_access_object_type,
        );
        write_opt_int(
            out,
            "indexedAccessIndexType",
            self.indexed_access_index_type,
        );
        write_opt_int(out, "conditionalCheckType", self.conditional_check_type);
        write_opt_int(out, "conditionalExtendsType", self.conditional_extends_type);
        write_opt_int(out, "conditionalTrueType", self.conditional_true_type);
        write_opt_int(out, "conditionalFalseType", self.conditional_false_type);
        write_opt_int(out, "substitutionBaseType", self.substitution_base_type);
        write_opt_int(out, "constraintType", self.constraint_type);
        write_opt_int(out, "instantiatedType", self.instantiated_type);
        write_id_list(out, "typeArguments", &self.type_arguments);
        write_opt_location(out, "referenceLocation", self.reference_location.as_ref());
        write_opt_int(
            out,
            "reverseMappedSourceType",
            self.reverse_mapped_source_type,
        );
        write_opt_int(
            out,
            "reverseMappedMappedType",
            self.reverse_mapped_mapped_type,
        );
        write_opt_int(
            out,
            "reverseMappedConstraintType",
            self.reverse_mapped_constraint_type,
        );
        write_opt_int(
            out,
            "evolvingArrayElementType",
            self.evolving_array_element_type,
        );
        write_opt_int(
            out,
            "evolvingArrayFinalType",
            self.evolving_array_final_type,
        );
        write_opt_location(
            out,
            "destructuringPattern",
            self.destructuring_pattern.as_ref(),
        );
        write_opt_location(out, "firstDeclaration", self.first_declaration.as_ref());
        // `flags` has no `omitzero`: Go writes it always (a nil slice as `[]`).
        out.push_str(",\"flags\":[");
        for (i, flag) in self.flags.iter().enumerate() {
            if i > 0 {
                out.push(',');
            }
            write_json_string(out, flag);
        }
        out.push(']');
        if !self.display.is_empty() {
            out.push_str(",\"display\":");
            write_json_string(out, &self.display);
        }
        out.push('}');
    }
}

fn write_opt_int(out: &mut String, key: &str, value: Option<i64>) {
    if let Some(value) = value {
        let _ = write!(out, ",\"{key}\":{value}");
    }
}

fn write_id_list(out: &mut String, key: &str, ids: &[u32]) {
    if ids.is_empty() {
        return;
    }
    let _ = write!(out, ",\"{key}\":[");
    for (i, id) in ids.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        let _ = write!(out, "{id}");
    }
    out.push(']');
}

fn write_opt_location(out: &mut String, key: &str, location: Option<&Location>) {
    let Some(location) = location else {
        return;
    };
    let _ = write!(out, ",\"{key}\":{{\"path\":");
    write_json_string(out, &location.path);
    for (name, position) in [("start", &location.start), ("end", &location.end)] {
        if let Some(position) = position {
            let _ = write!(
                out,
                ",\"{name}\":{{\"line\":{},\"character\":{}}}",
                position.line, position.character
            );
        }
    }
    out.push('}');
}

// Go: tracing/tracing.go:585 (*typeTracer).buildTypeDescriptor
// PORT: Go reads the type through the `TracedType` adapter
// (checker/tracer.go). The adapter methods are inlined here, each marked
// with its Go name.
fn build_type_descriptor(
    checker: &mut Checker,
    t: TypeId,
    recursion_identity_map: &mut FxHashMap<RecursionId, i64>,
) -> TypeDescriptor {
    let (flags, object_flags, symbol) = {
        let ty = checker.ty(t);
        (ty.flags, ty.object_flags, ty.symbol)
    };
    // Go: checker/tracer.go:96 AliasSymbol
    let alias_symbol = checker
        .ty(t)
        .alias
        .as_ref()
        .map_or(SymbolId::NIL, |alias| alias.symbol());

    // Go: checker/tracer.go:80 Id and :84 FormatFlags
    let mut desc = TypeDescriptor {
        id: t.0,
        flags: format_type_flags(flags),
        ..TypeDescriptor::default()
    };

    // Assign a unique integer token per recursion identity, matching TypeScript's behavior.
    // This lets trace analysis tools detect which types share the same recursion identity.
    // Go: checker/tracer.go:335 RecursionIdentity
    // PORT: Go `getRecursionIdentity(t).value` is never nil, so every type
    // gets a token.
    let identity = checker.get_recursion_identity(t);
    let next_token = recursion_identity_map.len() as i64;
    let token = *recursion_identity_map.entry(identity).or_insert(next_token);
    desc.recursion_id = Some(token);

    // Intrinsic name
    // Go: checker/tracer.go:111 IntrinsicName
    if flags.intersects(TypeFlags::INTRINSIC) {
        if let TypeData::Intrinsic(data) = &checker.ty(t).data {
            desc.intrinsic_name = data.intrinsic_name.clone();
        }
    }

    // Symbol name - escape the internal symbol name prefix for valid JSON
    if alias_symbol.is_some() {
        desc.symbol_name = escape_all_internal_symbol_names(&checker.sym(alias_symbol).name);
    } else if symbol.is_some() {
        desc.symbol_name = escape_all_internal_symbol_names(&checker.sym(symbol).name);
    }

    // Tuple flag
    // Go: checker/tracer.go:325 IsTuple
    if object_flags.intersects(ObjectFlags::TUPLE) {
        desc.is_tuple = true;
    }

    // Union types
    // Go: checker/tracer.go:122 UnionTypes
    if flags.intersects(TypeFlags::UNION) {
        desc.union_types = map_type_ids(&checker.ty(t).as_union_type().union_or_intersection.types);
    }

    // Intersection types
    // Go: checker/tracer.go:129 IntersectionTypes
    if flags.intersects(TypeFlags::INTERSECTION) {
        desc.intersection_types = map_type_ids(
            &checker
                .ty(t)
                .as_intersection_type()
                .union_or_intersection
                .types,
        );
    }

    // Alias type arguments
    // Go: checker/tracer.go:104 AliasTypeArguments
    if let Some(alias) = &checker.ty(t).alias {
        desc.alias_type_arguments = map_type_ids(alias.type_arguments());
    }

    // Index type (keyof)
    // Go: checker/tracer.go:136 IndexType
    if flags.intersects(TypeFlags::INDEX) {
        desc.keyof_type = opt_id(checker.ty(t).as_index_type().target);
    }

    // Indexed access type
    // Go: checker/tracer.go:147 IndexedAccessObjectType and :158 IndexedAccessIndexType
    if flags.intersects(TypeFlags::INDEXED_ACCESS) {
        let data = checker.ty(t).as_indexed_access_type();
        desc.indexed_access_object_type = opt_id(data.object_type);
        desc.indexed_access_index_type = opt_id(data.index_type);
    }

    // Conditional type
    // Go: checker/tracer.go:88 IsConditional and :169-:211 Conditional*Type
    if flags.intersects(TypeFlags::CONDITIONAL) {
        let data = checker.ty(t).as_conditional_type();
        desc.conditional_check_type = opt_id(data.check_type);
        desc.conditional_extends_type = opt_id(data.extends_type);
        desc.conditional_true_type = Some(if data.resolved_true_type.is_some() {
            i64::from(data.resolved_true_type.0)
        } else {
            -1
        });
        desc.conditional_false_type = Some(if data.resolved_false_type.is_some() {
            i64::from(data.resolved_false_type.0)
        } else {
            -1
        });
    }

    // Substitution type
    // Go: checker/tracer.go:213 SubstitutionBaseType and :224 SubstitutionConstraintType
    if flags.intersects(TypeFlags::SUBSTITUTION) {
        let data = checker.ty(t).as_substitution_type();
        desc.substitution_base_type = opt_id(data.base_type);
        desc.constraint_type = opt_id(data.constraint);
    }

    // Reference type
    // Go: checker/tracer.go:235 ReferenceTarget, :246 ReferenceTypeArguments
    // and :253 ReferenceNode
    let mut reference_node = Node::NIL;
    if flags.intersects(TypeFlags::OBJECT) && object_flags.intersects(ObjectFlags::REFERENCE) {
        let data = checker.ty(t).as_type_reference();
        desc.instantiated_type = opt_id(data.object.target);
        desc.type_arguments = map_type_ids(&data.resolved_type_arguments);
        reference_node = data.node;
    }
    if reference_node.is_some() {
        desc.reference_location = get_location(reference_node);
    }

    // Reverse mapped type
    // Go: checker/tracer.go:260-:291 ReverseMapped*Type
    if flags.intersects(TypeFlags::OBJECT) && object_flags.intersects(ObjectFlags::REVERSE_MAPPED) {
        let data = checker.ty(t).as_reverse_mapped_type();
        desc.reverse_mapped_source_type = opt_id(data.source);
        desc.reverse_mapped_mapped_type = opt_id(data.mapped_type);
        desc.reverse_mapped_constraint_type = opt_id(data.constraint_type);
    }

    // Evolving array type
    // Go: checker/tracer.go:293 EvolvingArrayElementType and :304 EvolvingArrayFinalType
    if flags.intersects(TypeFlags::OBJECT) && object_flags.intersects(ObjectFlags::EVOLVING_ARRAY) {
        let data = checker.ty(t).as_evolving_array_type();
        desc.evolving_array_element_type = opt_id(data.element_type);
        desc.evolving_array_final_type = opt_id(data.final_array_type);
    }

    // Pattern (destructuring)
    // Go: checker/tracer.go:328 Pattern
    if let Some(&pattern) = checker.pattern_for_type.get(&t) {
        if pattern.is_some() {
            desc.destructuring_pattern = get_location(pattern);
        }
    }

    // First declaration - prefer aliasSymbol, matching TypeScript's `aliasSymbol ?? symbol`
    let first_decl_symbol = if alias_symbol.is_some() {
        alias_symbol
    } else {
        symbol
    };
    if first_decl_symbol.is_some() {
        if let Some(&declaration) = checker.sym(first_decl_symbol).declarations.first() {
            desc.first_declaration = get_location(declaration);
        }
    }

    // Display text
    desc.display = display(checker, t, flags, object_flags);

    desc
}

// Go: checker/tracer.go:339 Display
// Compute display text for types where it's valuable for trace analysis.
// TypeScript only does this for Anonymous|Literal types, but we extend to
// unions, intersections, and template literals since they often lack
// firstDeclaration and the display text helps identify them.
// Incomplete types during tracing can cause panics, which we intentionally
// suppress (returning ""), matching TypeScript's try/catch around typeToString.
// PORT: Go `recover()` is `catch_unwind`. An unported path reached here
// still counts in the unported report.
fn display(
    checker: &mut Checker,
    t: TypeId,
    flags: TypeFlags,
    object_flags: ObjectFlags,
) -> String {
    if object_flags.intersects(ObjectFlags::ANONYMOUS)
        || flags.intersects(
            TypeFlags::LITERAL
                | TypeFlags::TEMPLATE_LITERAL
                | TypeFlags::UNION
                | TypeFlags::INTERSECTION,
        )
    {
        return std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            checker.type_to_string_exported(t)
        }))
        .unwrap_or_default();
    }
    String::new()
}

// Go: tracing/tracing.go:720 mapTypeIds
fn map_type_ids(types: &[TypeId]) -> Vec<u32> {
    // Go: a nil type maps to 0, which is `TypeId::NIL.0`.
    types.iter().map(|t| t.0).collect()
}

/// Go `if x != nil { desc.X = new(x.Id()) }`.
fn opt_id(t: TypeId) -> Option<i64> {
    t.is_some().then_some(i64::from(t.0))
}

// Go: tracing/tracing.go:733 getLocation
fn get_location(node: Node) -> Option<Location> {
    if node.is_nil() {
        return None;
    }
    let file = get_source_file_of_node(node);
    if file.is_nil() {
        return None;
    }

    let start_pos = get_token_pos_of_node(node, file, false);
    let (start_line, start_char) = get_ecma_line_and_utf16_character_of_position(file, start_pos);
    let (end_line, end_char) = get_ecma_line_and_utf16_character_of_position(file, node.end());

    Some(Location {
        path: crate::frontend::tspath::to_path(source_file_file_name(file), "", false).0,
        start: Some(LineAndChar {
            line: start_line + 1,
            character: start_char + 1,
        }),
        end: Some(LineAndChar {
            line: end_line + 1,
            character: end_char + 1,
        }),
    })
}

// ---------------------------------------------------------------------------
// Checker tracer
// ---------------------------------------------------------------------------

// Go: checker/tracer.go:13 Tracer
// Tracer records types and trace events during type checking. A None
// `Checker::tracer` is the Go nil `*Tracer`, so call sites use
// `if let Some(tr) = self.tracer` to gate work that only matters under
// --generateTrace.
#[derive(Clone, Copy)]
pub struct Tracer {
    tracing: &'static Tracing,
    recorder: &'static TypeTracer,
    checker_index: usize,
}

// Go: checker/tracer.go:21 NewTracer
// NewTracer creates a Tracer for the given checker index that records both
// type-creation events and trace events through the provided tracing session.
#[must_use]
pub fn new_tracer(tr: &'static Tracing, checker_index: usize) -> Tracer {
    Tracer {
        tracing: tr,
        recorder: tr.new_type_tracer(checker_index),
        checker_index,
    }
}

/// The tracer of a new checker: Go compiler/checkerpool.go:104 makes one
/// when the pool has a tracing session, and nil otherwise.
#[must_use]
pub fn new_checker_tracer(checker_index: usize) -> Option<Tracer> {
    get().map(|tr| new_tracer(tr, checker_index))
}

impl Tracer {
    // Go: checker/tracer.go:25 (*Tracer).RecordType
    pub fn record_type(self, t: TypeId) {
        self.recorder.record_type(t);
    }

    // Go: checker/tracer.go:29 (*Tracer).Push
    // PORT: Go adds "checkerId" to a copy of the args for a sampled event,
    // and to the caller's map for the "B" and "E" events of a separate one.
    // Both end with the same args plus "checkerId"; the `Pop` owns them.
    pub fn push(
        self,
        phase: Phase,
        name: &'static str,
        mut args: Args,
        separate_begin_and_end: bool,
    ) -> Pop {
        args.push(("checkerId", Arg::Int(self.checker_index as i64)));
        self.tracing.push(phase, name, args, separate_begin_and_end)
    }

    // Go: checker/tracer.go:45 (*Tracer).Instant
    pub fn instant(self, phase: Phase, name: &'static str, mut args: Args) {
        args.push(("checkerId", Arg::Int(self.checker_index as i64)));
        self.tracing.instant(phase, name, args);
    }
}

// ---------------------------------------------------------------------------
// execute/tsc.go helpers
// ---------------------------------------------------------------------------

// Go: execute/tsc.go:27 startTracingIfNeeded
// PORT: Go prints the warning to `sys.Writer()` and returns the session.
// The session is the process global here, and the warning text (with its
// newline) is returned for the caller to print. `testing` is Go
// `testing != nil`.
pub fn start_tracing_if_needed(
    config: &crate::frontend::tsoptions::ParsedCommandLine,
    testing: bool,
) -> Option<String> {
    let trace_dir = &config.compiler_options().generate_trace;
    if trace_dir.is_empty() {
        return None;
    }
    let mut config_file_path = "";
    if let Some(config_file) = &config.config_file {
        if config_file.source_file.is_some() {
            config_file_path = source_file_file_name(config_file.source_file);
        }
    }
    match start_tracing(trace_dir, config_file_path, testing) {
        Ok(_) => None,
        Err(err) => Some(format!("Warning: Failed to start tracing: {err}\n")),
    }
}

// Go: execute/tsc.go:43 stopTracing
// PORT: the warning text is returned, as for `start_tracing_if_needed`.
// Call it on the thread that loaded the program (it reaches the checkers).
pub fn stop_tracing() -> Option<String> {
    let tr = get()?;
    match tr.stop_tracing() {
        Ok(()) => None,
        Err(err) => Some(format!("Warning: Failed to stop tracing: {err}\n")),
    }
}

// ---------------------------------------------------------------------------
// JSON and file helpers
// ---------------------------------------------------------------------------

// Go: go-json-experiment jsonwire.AppendQuote with the default flags: only
// `"`, `\` and control characters are escaped (no HTML or JS escaping).
// PORT: Go `internal/json` marshals with `AllowInvalidUTF8`, so each byte
// that is not valid UTF-8 becomes U+FFFD. `s` is the port form of a Go
// string (see `scanner_util::GO_STRING_MARKER`), and
// `json::append_json_quote` does that replacement.
fn write_json_string(out: &mut String, s: &str) {
    crate::frontend::json::append_json_quote(out, s);
}

// Go: go-json-experiment jsonwire.AppendFloat(dst, src, 64)
// PORT: Rust `{}` prints the shortest round-trip digits without an
// exponent, which is Go `strconv.AppendFloat(f, 'f', -1, 64)`.
fn write_json_float(out: &mut String, value: f64) {
    let abs = value.abs();
    if abs != 0.0 && (abs < 1e-6 || abs >= 1e21) {
        // Go 'e' format with the "e-09" to "e-9" clean up.
        let text = format!("{value:e}");
        let (mantissa, exponent) = text.split_once('e').unwrap_or((text.as_str(), "0"));
        let exponent: i32 = exponent.parse().unwrap_or(0);
        if exponent < 0 {
            let _ = write!(out, "{mantissa}e-{}", -exponent);
        } else {
            let _ = write!(out, "{mantissa}e+{exponent:02}");
        }
        return;
    }
    let _ = write!(out, "{value}");
}

// Go: vfs/osvfs/os.go:194 writeFileEnsuringDir
// PORT: Go `WriteFile` truncates and `AppendFile` appends; a failed first
// write creates the directory and tries once more.
// PORT: `path` and `content` are port forms of Go strings (see
// `scanner_util::GO_STRING_MARKER`). The OS gets the Go bytes of the path
// (`os_path`), and the file gets the Go bytes of the content.
fn write_file_ensuring_dir(path: &str, content: &str, append: bool) -> std::io::Result<()> {
    use crate::frontend::vfs::os_path;
    let write = || -> std::io::Result<()> {
        use std::io::Write as _;
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(!append)
            .append(append)
            .open(os_path(path))?;
        file.write_all(&go_string_bytes(content))
    };
    if write().is_ok() {
        return Ok(());
    }
    let directory =
        crate::frontend::tspath::get_directory_path(&crate::frontend::tspath::normalize_path(path));
    std::fs::create_dir_all(os_path(&directory))?;
    write()
}

// Go: vfs/osvfs/os.go:205 WriteFile
// PORT: Go `tr.fs.WriteFile`, where `tr.fs` is `sys.FS()`. A test process
// installs an OS override (`osvfs::install_os_override`), and then the
// session writes through that thread's `osvfs_fs()`, which is the test
// file system. The error text is Go `err.Error()`. A real run never
// installs the override and writes with `std::fs` as before.
fn write_file(path: &str, content: &str) -> std::io::Result<()> {
    if crate::frontend::vfs::os_override_installed() {
        return crate::frontend::vfs::osvfs_fs()
            .write_file(path, content)
            .map_err(|err| std::io::Error::other(fs_error_text(&err)));
    }
    write_file_ensuring_dir(path, content, false)
}

// Go: vfs/osvfs/os.go:209 AppendFile
// PORT: Go `tr.fs.AppendFile`; see `write_file` for the OS override.
fn append_file(path: &str, content: &str) -> std::io::Result<()> {
    if crate::frontend::vfs::os_override_installed() {
        return crate::frontend::vfs::osvfs_fs()
            .append_file(path, content)
            .map_err(|err| std::io::Error::other(fs_error_text(&err)));
    }
    write_file_ensuring_dir(path, content, true)
}
