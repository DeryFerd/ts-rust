//! The process protocol of the compiler runner. No Go equivalent: Go runs
//! every test configuration as a parallel subtest of one process.
//!
//! PORT: a program and the OS override (`install_os_override`) are process
//! state, so each test configuration (`ConfigCase`) runs in a child process
//! (this test binary again, test `compiler_runner::__compiler_runner_child`).
//! The parent writes a request file (`key=value` lines) and names it in
//! `COMPILER_RUNNER_REQUEST`. The child appends one line per Go subtest to
//! the response file as the subtest ends, so a crash keeps the earlier
//! results:
//!
//! ```text
//! <kind>\t<pass|fail|skip>\t<escaped message>
//! ```
//!
//! and `done` last. `kind` is `compile` (the Go test around
//! `newCompilerTest`), `config` (a skipped configuration), `error`,
//! `output`, `sourcemap`, `sourcemaprecord`, `types`, `symbols`,
//! `moduleresolution`, `unionordering`, `parentpointers`, or `test` (a
//! panic between the subtests). A child that ends without `done` is a
//! `crash`.
//!
//! Environment of the parent:
//! - `COMPILER_RUNNER_FILTER=<substring>`: runs the cases whose key
//!   (`<local|submodule>/<suite>/<configured name>`) contains it.
//! - `COMPILER_RUNNER_SHARD=<i>/<n>`: runs the test files whose index
//!   (both runners, in enumeration order) is `i` modulo `n`.
//! - `COMPILER_RUNNER_JOBS` (default 4): child processes at once.
//! - `COMPILER_RUNNER_TIMEOUT` (seconds, default 600): a child that runs
//!   longer is killed and is a `crash`.
//! - `COMPILER_RUNNER_RESULTS=<file>`: writes every result as
//!   `<status>\t<kind>\t<key>\t<escaped message>` and the compared baselines
//!   as `baseline\t<relative path>`.
//! - `COMPILER_RUNNER_TMP` (default `tests2/S1/tmp`): request, response and
//!   stderr files, deleted after use unless `COMPILER_RUNNER_KEEP=1`.
//! - `TS_TEST_PROGRAM_SINGLE_THREADED=false` (the Go variable, read by
//!   `harness::create_program`): programs use more than one checker, as in
//!   the Go CI job "concurrent test programs". The references are the same.
//!
//! Known failures are in `known_failures.txt` next to this file: one
//! `<kind> <key> <bug id>` per line. A listed failure passes the run; a
//! listed case that passes is reported as recovered. Any other failure
//! fails the run.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::io::Write as _;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use super::runner::{
    CompilerTestType, ConfigCase, Outcome, enumerate_config_cases, new_compiler_baseline_runner,
    payload_text, run_single_config_test,
};

/// The libtest name of the child test (see mod.rs).
const CHILD_TEST: &str = "compiler_runner::__compiler_runner_child";
const REQUEST_ENV: &str = "COMPILER_RUNNER_REQUEST";
const FILTER_ENV: &str = "COMPILER_RUNNER_FILTER";
const SHARD_ENV: &str = "COMPILER_RUNNER_SHARD";
const JOBS_ENV: &str = "COMPILER_RUNNER_JOBS";
const TIMEOUT_ENV: &str = "COMPILER_RUNNER_TIMEOUT";
const RESULTS_ENV: &str = "COMPILER_RUNNER_RESULTS";
const TMP_ENV: &str = "COMPILER_RUNNER_TMP";
const KEEP_ENV: &str = "COMPILER_RUNNER_KEEP";
const DEFAULT_TMP: &str =
    "/home/theo/Code/sandbox/ts-rust/target/continuation-r97-goport/tests2/S1/tmp";
const DEFAULT_JOBS: usize = 4;
const DEFAULT_TIMEOUT_SECS: u64 = 600;
/// The stack of the compile thread in a child, as the bins use.
const STACK_SIZE: usize = 1 << 30;
/// Lines of a crashed child's stderr that its failure shows.
const STDERR_TAIL_LINES: usize = 30;
/// The longest message a response line keeps.
const MAX_MESSAGE: usize = 4000;
/// Failures that the final panic lists.
const MAX_LISTED_FAILURES: usize = 60;

const KNOWN_FAILURES: &str = include_str!("known_failures.txt");

fn escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for ch in text.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(ch),
        }
    }
    out
}

fn unescape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars();
    while let Some(ch) = chars.next() {
        if ch != '\\' {
            out.push(ch);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some('t') => out.push('\t'),
            Some(other) => out.push(other),
            None => {}
        }
    }
    out
}

fn truncate(text: &str) -> &str {
    if text.len() <= MAX_MESSAGE {
        return text;
    }
    let mut end = MAX_MESSAGE;
    while !text.is_char_boundary(end) {
        end -= 1;
    }
    &text[..end]
}

// ---------------------------------------------------------------------------
// Child
// ---------------------------------------------------------------------------

/// The child test body: runs the case of `COMPILER_RUNNER_REQUEST`, or
/// returns at once when the variable is not set.
pub fn child_entry() {
    let Some(request_path) = std::env::var_os(REQUEST_ENV) else {
        return;
    };
    let request = std::fs::read_to_string(&request_path)
        .unwrap_or_else(|err| panic!("cannot read request {request_path:?}: {err}"));
    let mut fields: BTreeMap<&str, &str> = BTreeMap::new();
    for line in request.lines() {
        if let Some((key, value)) = line.split_once('=') {
            fields.insert(key, value);
        }
    }
    let field = |key: &str| -> String {
        fields
            .get(key)
            .map(|value| unescape(value))
            .unwrap_or_else(|| panic!("request has no {key}"))
    };
    let case = ConfigCase {
        is_submodule: field("submodule") == "true",
        suite: if field("suite") == "compiler" {
            CompilerTestType::Regression.string()
        } else {
            CompilerTestType::Conformance.string()
        },
        filename: field("file"),
        configuration: fields.get("configuration").map(|value| unescape(value)),
        test_name: field("test_name"),
        file_index: 0,
    };
    let response_path = PathBuf::from(field("response"));

    // Quiet panics: each one is reported through the response.
    std::panic::set_hook(Box::new(|info| {
        if info.payload().is::<super::harness::SkipPayload>() {
            return;
        }
        let location = info
            .location()
            .map(|l| format!(" at {}:{}", l.file(), l.line()))
            .unwrap_or_default();
        eprintln!("panic{location}: {}", payload_text(info.payload()));
    }));

    let handle = std::thread::Builder::new()
        .name("compiler-runner-case".to_string())
        .stack_size(STACK_SIZE)
        .spawn(move || {
            let mut response = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(&response_path)
                .unwrap_or_else(|err| panic!("cannot open response {response_path:?}: {err}"));
            let mut write_line = |line: String| {
                response
                    .write_all(line.as_bytes())
                    .and_then(|()| response.flush())
                    .expect("write response");
            };
            let mut report = |kind: &str, outcome: Outcome| {
                let (status, message) = match outcome {
                    Outcome::Pass => ("pass", String::new()),
                    Outcome::Fail(message) => ("fail", message),
                    Outcome::Skip(message) => ("skip", message),
                };
                write_line(format!(
                    "{kind}\t{status}\t{}\n",
                    escape(truncate(&message))
                ));
            };
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                run_single_config_test(&case, &mut report);
            }));
            if let Err(payload) = result {
                report(
                    "test",
                    Outcome::Fail(format!(
                        "Panic on compiling test {}:\n{}",
                        case.filename,
                        payload_text(payload.as_ref())
                    )),
                );
            }
            write_line("done\n".to_string());
        })
        .expect("spawn the compile thread");
    let _ = handle.join();
    // Checker threads can still hold the program; the process ends here.
    std::process::exit(0);
}

// ---------------------------------------------------------------------------
// Parent
// ---------------------------------------------------------------------------

/// The results of one case.
struct CaseResult {
    /// (kind, status, message) in report order.
    subtests: Vec<(String, String, String)>,
    /// The compared baselines (relative to the reference root).
    baselines: Vec<String>,
    /// The crash message when the child ended without `done`.
    crash: Option<String>,
    elapsed: Duration,
}

fn tmp_dir() -> PathBuf {
    match std::env::var_os(TMP_ENV) {
        Some(dir) if !dir.is_empty() => PathBuf::from(dir),
        _ => PathBuf::from(DEFAULT_TMP),
    }
}

fn keep_files() -> bool {
    std::env::var_os(KEEP_ENV).is_some_and(|value| value == "1")
}

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name)
        .ok()
        .and_then(|value| value.parse().ok())
        .filter(|&value| value > 0)
        .unwrap_or(default)
}

fn tail(text: &str) -> String {
    let lines: Vec<&str> = text.lines().collect();
    lines[lines.len().saturating_sub(STDERR_TAIL_LINES)..].join("\n")
}

/// Runs `case` in a child process and reads its response.
fn run_case_in_child(case: &ConfigCase, timeout: Duration) -> CaseResult {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let dir = tmp_dir();
    let _ = std::fs::create_dir_all(&dir);
    let stem = format!(
        "{}-{}",
        std::process::id(),
        COUNTER.fetch_add(1, Ordering::Relaxed)
    );
    let request_path = dir.join(format!("{stem}.request"));
    let response_path = dir.join(format!("{stem}.response"));
    let stderr_path = dir.join(format!("{stem}.stderr"));
    let track_path = dir.join(format!("{stem}.track"));
    let _ = std::fs::remove_file(&response_path);
    let _ = std::fs::remove_file(&track_path);

    let mut request = String::new();
    request.push_str(&format!("submodule={}\n", case.is_submodule));
    request.push_str(&format!("suite={}\n", case.suite));
    request.push_str(&format!("file={}\n", escape(&case.filename)));
    if let Some(configuration) = &case.configuration {
        request.push_str(&format!("configuration={}\n", escape(configuration)));
    }
    request.push_str(&format!("test_name={}\n", escape(&case.test_name)));
    request.push_str(&format!(
        "response={}\n",
        escape(&response_path.to_string_lossy())
    ));
    std::fs::write(&request_path, request).expect("write request");

    let start = Instant::now();
    let exe = std::env::current_exe().expect("current test binary");
    let stderr_file = std::fs::File::create(&stderr_path).expect("create stderr file");
    let spawned = std::process::Command::new(exe)
        .args(["--exact", CHILD_TEST, "--nocapture", "--test-threads", "1"])
        .env(REQUEST_ENV, &request_path)
        .env(crate::support::baseline::TRACK_ENV, &track_path)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(stderr_file)
        .spawn();
    let mut crash = None;
    match spawned {
        Err(err) => crash = Some(format!("cannot run {CHILD_TEST}: {err}")),
        Ok(mut child) => loop {
            match child.try_wait() {
                Ok(Some(_)) => break,
                Ok(None) => {
                    if start.elapsed() > timeout {
                        let _ = child.kill();
                        let _ = child.wait();
                        crash = Some(format!("timeout after {}s", timeout.as_secs()));
                        break;
                    }
                    std::thread::sleep(Duration::from_millis(20));
                }
                Err(err) => {
                    crash = Some(format!("wait failed: {err}"));
                    break;
                }
            }
        },
    }
    let elapsed = start.elapsed();

    let response = std::fs::read_to_string(&response_path).unwrap_or_default();
    let mut subtests = Vec::new();
    let mut done = false;
    for line in response.lines() {
        if line == "done" {
            done = true;
            continue;
        }
        let mut parts = line.splitn(3, '\t');
        let (Some(kind), Some(status)) = (parts.next(), parts.next()) else {
            continue;
        };
        let message = unescape(parts.next().unwrap_or(""));
        subtests.push((kind.to_string(), status.to_string(), message));
    }
    if !done && crash.is_none() {
        let stderr = std::fs::read_to_string(&stderr_path).unwrap_or_default();
        crash = Some(format!(
            "child ended without a result; stderr tail:\n{}",
            tail(&stderr)
        ));
    }
    let baselines: Vec<String> = std::fs::read_to_string(&track_path)
        .unwrap_or_default()
        .lines()
        .map(str::to_string)
        .collect();
    // The child tracks into its own file; pass the names on to the file of
    // this process (`TS_GOPORT_BASELINE_TRACK`), if any.
    if let Some(parent_track) =
        std::env::var_os(crate::support::baseline::TRACK_ENV).filter(|value| !value.is_empty())
        && !baselines.is_empty()
    {
        let mut text = baselines.join("\n");
        text.push('\n');
        let written = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&parent_track)
            .and_then(|mut file| file.write_all(text.as_bytes()));
        if let Err(err) = written {
            panic!("cannot append to {parent_track:?}: {err}");
        }
    }

    if !keep_files() {
        for path in [&request_path, &response_path, &stderr_path, &track_path] {
            let _ = std::fs::remove_file(path);
        }
    }
    CaseResult {
        subtests,
        baselines,
        crash,
        elapsed,
    }
}

/// `known_failures.txt`: (kind, key) to bug id.
fn known_failures() -> BTreeMap<(String, String), String> {
    let mut known = BTreeMap::new();
    for line in KNOWN_FAILURES.lines() {
        let line = line.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        let parts: Vec<&str> = line.split_whitespace().collect();
        assert!(
            parts.len() == 3,
            "known_failures.txt: want `<kind> <key> <bug id>`, got {line:?}"
        );
        known.insert(
            (parts[0].to_string(), parts[1].to_string()),
            parts[2].to_string(),
        );
    }
    known
}

/// The shard of `COMPILER_RUNNER_SHARD`: (index, count).
fn shard() -> Option<(usize, usize)> {
    let value = std::env::var(SHARD_ENV).ok()?;
    let (i, n) = value.split_once('/')?;
    let (i, n): (usize, usize) = (i.parse().ok()?, n.parse().ok()?);
    (n > 0 && i < n).then_some((i, n))
}

// Go: compiler_runner_test.go:20 runCompilerTests
pub fn run_compiler_tests(is_submodule: bool) {
    if is_submodule
        && !crate::tsoptions::tsoptionstest::type_script_submodule_path()
            .join("package.json")
            .exists()
    {
        eprintln!("skipped: TypeScript submodule does not exist");
        return;
    }

    let runners = [
        new_compiler_baseline_runner(CompilerTestType::Regression, is_submodule),
        new_compiler_baseline_runner(CompilerTestType::Conformance, is_submodule),
    ];

    let mut failures: Vec<String> = Vec::new();
    let mut seen_tests: BTreeSet<String> = BTreeSet::new();
    for runner in &runners {
        for test in runner.enumerate_test_files() {
            let test = ts_goport::frontend::tspath::get_base_file_name(test);
            if !seen_tests.insert(test.clone()) {
                failures.push(format!("Duplicate test file: {test}"));
            }
        }
    }

    let mut cases: Vec<ConfigCase> = Vec::new();
    let mut file_index = 0usize;
    for runner in &runners {
        let (runner_cases, errors) = enumerate_config_cases(runner, file_index);
        file_index += runner.enumerate_test_files().len();
        cases.extend(runner_cases);
        failures.extend(errors);
    }
    let filter = std::env::var(FILTER_ENV).ok().filter(|f| !f.is_empty());
    let shard = shard();
    cases.retain(|case| {
        filter
            .as_ref()
            .is_none_or(|filter| case.key().contains(filter.as_str()))
            && shard.is_none_or(|(i, n)| case.file_index % n == i)
    });

    let jobs = env_usize(JOBS_ENV, DEFAULT_JOBS);
    let timeout = Duration::from_secs(env_usize(TIMEOUT_ENV, DEFAULT_TIMEOUT_SECS as usize) as u64);
    eprintln!(
        "compiler runner ({}): {} cases, {jobs} jobs",
        if is_submodule { "submodule" } else { "local" },
        cases.len()
    );

    let queue: Arc<Mutex<VecDeque<(usize, ConfigCase)>>> =
        Arc::new(Mutex::new(cases.iter().cloned().enumerate().collect()));
    let results: Arc<Mutex<Vec<Option<CaseResult>>>> =
        Arc::new(Mutex::new((0..cases.len()).map(|_| None).collect()));
    let finished = Arc::new(AtomicU64::new(0));
    let total = cases.len();
    std::thread::scope(|scope| {
        for _ in 0..jobs {
            let queue = queue.clone();
            let results = results.clone();
            let finished = finished.clone();
            scope.spawn(move || {
                loop {
                    let next = queue
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner)
                        .pop_front();
                    let Some((index, case)) = next else {
                        break;
                    };
                    let result = run_case_in_child(&case, timeout);
                    results
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner)[index] = Some(result);
                    let count = finished.fetch_add(1, Ordering::Relaxed) + 1;
                    if count % 500 == 0 {
                        eprintln!("compiler runner: {count}/{total} cases");
                    }
                }
            });
        }
    });
    let results: Vec<CaseResult> = Arc::try_unwrap(results)
        .ok()
        .expect("workers ended")
        .into_inner()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .into_iter()
        .map(|result| result.expect("every case ran"))
        .collect();

    let known = known_failures();
    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    let mut recovered: Vec<String> = Vec::new();
    let mut known_hits = 0usize;
    let mut report_lines: Vec<String> = Vec::new();
    let mut slowest: Vec<(Duration, String)> = Vec::new();
    for (case, result) in cases.iter().zip(&results) {
        let key = case.key();
        slowest.push((result.elapsed, key.clone()));
        let mut statuses: Vec<(String, String, String)> = result.subtests.clone();
        if let Some(crash) = &result.crash {
            statuses.push(("crash".to_string(), "fail".to_string(), crash.clone()));
        }
        for (kind, status, message) in &statuses {
            *counts.entry(format!("{kind} {status}")).or_default() += 1;
            report_lines.push(format!("{status}\t{kind}\t{key}\t{}", escape(message)));
            let listed = known.get(&(kind.clone(), key.clone()));
            match (status.as_str(), listed) {
                ("fail", Some(_)) => known_hits += 1,
                ("fail", None) => failures.push(format!("{kind} {key}: {message}")),
                ("pass", Some(bug)) => recovered.push(format!("{kind} {key} ({bug})")),
                _ => {}
            }
        }
        for baseline in &result.baselines {
            report_lines.push(format!("baseline\t{baseline}"));
        }
    }

    if let Ok(path) = std::env::var(RESULTS_ENV)
        && !path.is_empty()
    {
        let mut text = report_lines.join("\n");
        text.push('\n');
        std::fs::write(&path, text).unwrap_or_else(|err| panic!("cannot write {path}: {err}"));
    }

    slowest.sort_by(|a, b| b.0.cmp(&a.0));
    for (elapsed, key) in slowest.iter().take(5) {
        eprintln!("slow: {:.1}s {key}", elapsed.as_secs_f64());
    }
    for (status, count) in &counts {
        eprintln!("count: {status} {count}");
    }
    eprintln!("known failures hit: {known_hits}");
    for line in &recovered {
        eprintln!("recovered: {line}");
    }
    if !failures.is_empty() {
        let shown: Vec<&str> = failures
            .iter()
            .take(MAX_LISTED_FAILURES)
            .map(String::as_str)
            .collect();
        panic!(
            "{} new failures (first {}):\n{}",
            failures.len(),
            shown.len(),
            shown.join("\n---\n")
        );
    }
}
