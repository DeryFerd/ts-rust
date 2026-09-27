//! Go: `internal/tracing/tracing_test.go`.
//!
//! PORT: the Rust tracing session is one process global (`tracing::get`; a
//! second start fails) and writes to the OS file system, not to a Go
//! `vfstest` FS. Each session runs in a child process of this test binary
//! (`trace_child`, which does nothing unless `S2_TRACE_CHILD` is set) in a
//! fresh temp directory, and the parent reads the trace file it wrote.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use indexmap::IndexMap;
use ts_goport::frontend::json::json_unmarshal;
use ts_goport::frontend::json_ext::LspAny;
use ts_goport::tracing::{Arg, Phase, start_tracing};

const CHILD_TEST: &str = "units_platform::tracing::trace_child";
const CHILD_ENV: &str = "S2_TRACE_CHILD";
const DIR_ENV: &str = "S2_TRACE_DIR";

/// One trace session, run by `trace_child`.
fn run_session(kind: &str, dir: &str) {
    let tr = start_tracing(dir, "", true /*deterministic*/).expect("StartTracing");
    let path = |p: &'static str| -> Vec<(&'static str, Arg)> { vec![("path", p.into())] };
    match kind {
        // Go: tracing_test.go:13 TestConcurrentDurationEventsUseSeparateThreadIDs
        "concurrent" => {
            let end_a = tr.push(Phase::Parse, "createSourceFile", path("/a.ts"), true);
            let end_b = tr.push(Phase::Parse, "createSourceFile", path("/b.ts"), true);
            drop(end_a);
            drop(end_b);

            let end_check = tr.push(
                Phase::Check,
                "checkSourceFile",
                vec![("checkerId", 0.into()), ("path", "/a.ts".into())],
                true,
            );
            let end_variance = tr.push(
                Phase::CheckTypes,
                "getVariancesWorker",
                vec![("checkerId", 0.into()), ("id", 1.into())],
                true,
            );
            drop(end_variance);
            drop(end_check);
        }
        // Go: tracing_test.go:67 traceThreadIDsForPaths
        "a-b" | "b-a" => {
            let paths = if kind == "a-b" {
                ["/a.ts", "/b.ts"]
            } else {
                ["/b.ts", "/a.ts"]
            };
            for p in paths {
                let end = tr.push(Phase::Parse, "createSourceFile", path(p), true);
                drop(end);
            }
        }
        _ => panic!("unknown trace session {kind}"),
    }
    tr.stop_tracing().expect("StopTracing");
}

/// Child entry: runs one trace session when `S2_TRACE_CHILD` names it.
#[test]
fn trace_child() {
    let Some(kind) = std::env::var_os(CHILD_ENV) else {
        return;
    };
    let dir = std::env::var(DIR_ENV).expect("S2_TRACE_DIR");
    run_session(kind.to_str().unwrap(), &dir);
}

fn temp_dir(name: &str) -> PathBuf {
    let n = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("s2-tracing-{name}-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Runs trace session `kind` in a child process and returns the events of
/// its `trace.json`.
fn trace_events(kind: &str) -> Vec<TraceEvent> {
    let dir = temp_dir(kind);
    let exe = std::env::current_exe().expect("current test binary");
    let output = std::process::Command::new(exe)
        .args(["--exact", CHILD_TEST, "--nocapture", "--test-threads", "1"])
        .env(CHILD_ENV, kind)
        .env(DIR_ENV, &dir)
        .stdin(std::process::Stdio::null())
        .output()
        .expect("run trace child");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("1 passed"),
        "trace child {kind} failed ({}):\n{stdout}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    let text = std::fs::read(Path::new(&dir).join("trace.json")).expect("trace.json");
    let _ = std::fs::remove_dir_all(&dir);
    let mut value = LspAny::Null;
    json_unmarshal(&text, &mut value, &[]).expect("trace.json is JSON");
    let LspAny::Array(items) = value else {
        panic!("trace.json is not an array");
    };
    items.into_iter().map(TraceEvent::from_json).collect()
}

// Go: tracing.go traceEvent (the fields the test reads)
#[derive(Clone, Debug)]
struct TraceEvent {
    ph: String,
    cat: String,
    name: String,
    tid: i64,
    args: IndexMap<String, LspAny>,
}

impl TraceEvent {
    fn from_json(value: LspAny) -> TraceEvent {
        let LspAny::Object(mut fields) = value else {
            panic!("trace event is not an object");
        };
        let text = |key: &str| match fields.get(key) {
            Some(LspAny::String(s)) => s.clone(),
            _ => String::new(),
        };
        let ph = text("ph");
        let cat = text("cat");
        let name = text("name");
        let tid = match fields.get("tid") {
            Some(LspAny::Number(n)) => *n as i64,
            _ => 0,
        };
        let args = match fields.shift_remove("args") {
            Some(LspAny::Object(args)) => args,
            _ => IndexMap::new(),
        };
        TraceEvent {
            ph,
            cat,
            name,
            tid,
            args,
        }
    }
}

// Go: tracing_test.go:103 findEvent
fn find_event(
    events: &[TraceEvent],
    phase: &str,
    name: &str,
    arg_name: &str,
    arg_value: &LspAny,
) -> TraceEvent {
    for event in events {
        if event.ph == phase && event.name == name && event.args.get(arg_name) == Some(arg_value) {
            return event.clone();
        }
    }
    panic!("failed to find {phase} event {name:?} with {arg_name}={arg_value:?}");
}

fn s(text: &str) -> LspAny {
    LspAny::String(text.to_string())
}

// Go: tracing_test.go:114 assertThreadName
fn assert_thread_name(events: &[TraceEvent], tid: i64, name: &str) {
    for event in events {
        if event.ph == "M"
            && event.name == "thread_name"
            && event.tid == tid
            && event.args.get("name") == Some(&s(name))
        {
            return;
        }
    }
    panic!("failed to find thread_name metadata for thread {tid} named {name:?}");
}

// Go: tracing_test.go:124 assertDurationEventsAreWellNestedByThread
fn assert_duration_events_are_well_nested_by_thread(events: &[TraceEvent]) {
    let mut stacks: HashMap<i64, Vec<TraceEvent>> = HashMap::new();
    for event in events {
        match event.ph.as_str() {
            "B" => stacks.entry(event.tid).or_default().push(event.clone()),
            "E" => {
                let stack = stacks.entry(event.tid).or_default();
                let begin = stack.pop().unwrap_or_else(|| {
                    panic!(
                        "unmatched end event {:?} on thread {}",
                        event.name, event.tid
                    )
                });
                assert_eq!(begin.cat, event.cat);
                assert_eq!(begin.name, event.name);
            }
            _ => {}
        }
    }
    for (tid, stack) in stacks {
        assert!(
            stack.is_empty(),
            "thread {tid} has {} unterminated events",
            stack.len()
        );
    }
}

// Go: tracing_test.go:13 TestConcurrentDurationEventsUseSeparateThreadIDs
#[test]
fn test_concurrent_duration_events_use_separate_thread_ids() {
    let events = trace_events("concurrent");

    let a_begin = find_event(&events, "B", "createSourceFile", "path", &s("/a.ts"));
    let a_end = find_event(&events, "E", "createSourceFile", "path", &s("/a.ts"));
    let b_begin = find_event(&events, "B", "createSourceFile", "path", &s("/b.ts"));
    let b_end = find_event(&events, "E", "createSourceFile", "path", &s("/b.ts"));
    assert_eq!(a_begin.tid, a_end.tid);
    assert_eq!(b_begin.tid, b_end.tid);
    assert_ne!(a_begin.tid, b_begin.tid);
    assert_thread_name(&events, a_begin.tid, "file:/a.ts");
    assert_thread_name(&events, b_begin.tid, "file:/b.ts");

    let check_begin = find_event(&events, "B", "checkSourceFile", "path", &s("/a.ts"));
    let variance_begin = find_event(
        &events,
        "B",
        "getVariancesWorker",
        "id",
        &LspAny::Number(1.0),
    );
    assert_eq!(check_begin.tid, variance_begin.tid);
    assert_thread_name(&events, check_begin.tid, "checker:0");

    assert_duration_events_are_well_nested_by_thread(&events);
}

// Go: tracing_test.go:67 traceThreadIDsForPaths
fn trace_thread_ids_for_paths(kind: &str, paths: &[&str]) -> HashMap<String, i64> {
    let events = trace_events(kind);
    paths
        .iter()
        .map(|p| {
            (
                p.to_string(),
                find_event(&events, "B", "createSourceFile", "path", &s(p)).tid,
            )
        })
        .collect()
}

// Go: tracing_test.go:58 TestThreadIDsAreStableAcrossFirstSeenOrder
#[test]
fn test_thread_ids_are_stable_across_first_seen_order() {
    let first = trace_thread_ids_for_paths("a-b", &["/a.ts", "/b.ts"]);
    let second = trace_thread_ids_for_paths("b-a", &["/b.ts", "/a.ts"]);
    assert_eq!(first, second);
}
