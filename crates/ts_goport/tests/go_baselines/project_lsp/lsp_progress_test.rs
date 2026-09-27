//! Port of Go `internal/lsp/progress_test.go` (`TestProgress`).
//!
//! PORT: Go runs each subtest in a `synctest` bubble with fake time. The
//! port uses real time: `synctest.Wait()` is `settle()` (a short sleep that
//! lets the progress thread handle its queue), and each fake sleep is the
//! same real sleep plus `SLACK`. These tests run in the test process: they
//! build no program.

use std::sync::{Arc, Mutex};
use std::time::Duration;

use ts_goport::diag;
use ts_goport::gostd::Context;
use ts_goport::gostd::context::{self, Done};
use ts_goport::lsp::lsproto;
use ts_goport::lsp::progress::{
    ProgressEvent, ProgressReporter, new_project_loading_progress_from_reporter,
};

/// Extra real time on top of a Go fake-time sleep.
const SLACK: Duration = Duration::from_millis(150);

/// Go `synctest.Wait()`: let the progress thread handle what is queued.
fn settle() {
    std::thread::sleep(Duration::from_millis(60));
}

fn sleep_past(d: Duration) {
    std::thread::sleep(d + SLACK);
}

// Go: progress_test.go:15 progressCall
#[derive(Clone, Debug, Default)]
struct ProgressCall {
    method: String, // "create", "begin", "report", "end"
    token: String,
    title: String, // begin only
    msg: String,   // begin/report only
}

// Go: progress_test.go:22 fakeProgressReporter
struct FakeProgressReporter {
    calls: Mutex<Vec<ProgressCall>>,
    ctx: Context,
}

impl ProgressReporter for FakeProgressReporter {
    // Go: progress_test.go:28 done
    fn done(&self) -> Option<Done> {
        self.ctx.done()
    }

    // Go: progress_test.go:32 localize
    fn localize(&self, msg: &'static ts_diagnostics::Message, args: Vec<String>) -> String {
        ts_goport::diagnostics_loc::message_localize(msg, &Default::default(), &args)
    }

    // Go: progress_test.go:36 createWorkDoneProgress
    fn create_work_done_progress(&self, token: &str) {
        self.lock().push(ProgressCall {
            method: "create".to_string(),
            token: token.to_string(),
            ..Default::default()
        });
    }

    // Go: progress_test.go:42 sendProgress
    fn send_progress(&self, token: &str, value: lsproto::WorkDoneProgressBeginOrReportOrEnd) {
        let call = if let Some(begin) = &value.begin {
            ProgressCall {
                method: "begin".to_string(),
                token: token.to_string(),
                title: begin.title.clone(),
                msg: begin.message.clone().unwrap_or_default(),
            }
        } else if let Some(report) = &value.report {
            ProgressCall {
                method: "report".to_string(),
                token: token.to_string(),
                msg: report.message.clone().unwrap_or_default(),
                ..Default::default()
            }
        } else if value.end.is_some() {
            ProgressCall {
                method: "end".to_string(),
                token: token.to_string(),
                ..Default::default()
            }
        } else {
            return;
        };
        self.lock().push(call);
    }
}

impl FakeProgressReporter {
    fn lock(&self) -> std::sync::MutexGuard<'_, Vec<ProgressCall>> {
        self.calls
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }

    // Go: progress_test.go:63 getCalls
    fn get_calls(&self) -> Vec<ProgressCall> {
        self.lock().clone()
    }
}

fn args(s: &str) -> Vec<String> {
    vec![s.to_string()]
}

/// A reporter on a new cancellable context, and the context's cancel.
fn reporter() -> (Arc<FakeProgressReporter>, context::CancelFunc) {
    let (ctx, cancel) = context::with_cancel(&context::background());
    (
        Arc::new(FakeProgressReporter {
            calls: Mutex::default(),
            ctx,
        }),
        cancel,
    )
}

// Go: progress_test.go:72 TestProgress/StartFinishBeforeDelay
#[test]
fn start_finish_before_delay() {
    let (reporter, cancel) = reporter();
    let p =
        new_project_loading_progress_from_reporter(reporter.clone(), Duration::from_millis(500));

    p.start(diag::Project_0, args("myProject"));
    settle();

    // Finish before the delay fires — no UI should appear.
    p.finish(diag::Project_0, args("myProject"));
    settle();

    // Advance time past the delay to ensure no progress is sent.
    sleep_past(Duration::from_millis(600));
    settle();

    let calls = reporter.get_calls();
    assert!(
        calls.is_empty(),
        "expected no progress calls for fast operation, got {calls:?}"
    );

    cancel();
}

// Go: progress_test.go:100 TestProgress/ShowsAfterDelay
#[test]
fn shows_after_delay() {
    let (reporter, cancel) = reporter();
    let p =
        new_project_loading_progress_from_reporter(reporter.clone(), Duration::from_millis(500));

    p.start(diag::Project_0, args("myProject"));
    settle();

    // Let the delay fire.
    sleep_past(Duration::from_millis(500));
    settle();

    let calls = reporter.get_calls();
    assert_eq!(
        calls.len(),
        2,
        "expected 2 calls (create + begin), got {}: {calls:?}",
        calls.len()
    );
    assert_eq!(
        calls[0].method, "create",
        "expected create, got {:?}",
        calls[0]
    );
    assert_eq!(
        calls[1].method, "begin",
        "expected begin, got {:?}",
        calls[1]
    );
    assert_eq!(calls[1].title, diag::Loading.text(), "expected title");

    // Finish the operation.
    p.finish(diag::Project_0, args("myProject"));
    settle();

    let calls = reporter.get_calls();
    let last = calls.last().unwrap();
    assert_eq!(last.method, "end", "expected end, got {last:?}");

    cancel();
}

// Go: progress_test.go:143 TestProgress/ReportsMultipleOperations
#[test]
fn reports_multiple_operations() {
    let (reporter, cancel) = reporter();
    let p =
        new_project_loading_progress_from_reporter(reporter.clone(), Duration::from_millis(100));

    // Start two different operations.
    p.start(diag::Project_0, args("projA"));
    p.start(diag::Project_0, args("projB"));
    settle();

    // Let the delay fire.
    sleep_past(Duration::from_millis(100));
    settle();

    let calls = reporter.get_calls();
    // Should have: create, begin (with first message).
    assert!(
        calls.len() >= 2,
        "expected at least 2 calls, got {}: {calls:?}",
        calls.len()
    );
    assert_eq!(
        calls[0].method, "create",
        "expected create, got {:?}",
        calls[0]
    );
    assert_eq!(
        calls[1].method, "begin",
        "expected begin, got {:?}",
        calls[1]
    );

    // Finish one — should send a report with the remaining operation.
    p.finish(diag::Project_0, args("projA"));
    settle();

    let calls = reporter.get_calls();
    assert!(
        calls.iter().any(|c| c.method == "report"),
        "expected a report after partial finish, got {calls:?}"
    );

    // Finish the second — should send end.
    p.finish(diag::Project_0, args("projB"));
    settle();

    let calls = reporter.get_calls();
    let last = calls.last().unwrap();
    assert_eq!(last.method, "end", "expected end, got {last:?}");

    cancel();
}

// Go: progress_test.go:202 TestProgress/RefCounting
#[test]
fn ref_counting() {
    let (reporter, cancel) = reporter();
    let p =
        new_project_loading_progress_from_reporter(reporter.clone(), Duration::from_millis(100));

    // Start the same operation twice (ref count = 2).
    p.start(diag::Project_0, args("proj"));
    p.start(diag::Project_0, args("proj"));
    settle();

    sleep_past(Duration::from_millis(100));
    settle();

    // Finish once (ref count = 1) — should NOT end.
    p.finish(diag::Project_0, args("proj"));
    settle();

    let calls = reporter.get_calls();
    assert!(
        !calls.iter().any(|c| c.method == "end"),
        "unexpected end with ref count > 0: {calls:?}"
    );

    // Finish again (ref count = 0) — should end.
    p.finish(diag::Project_0, args("proj"));
    settle();

    let calls = reporter.get_calls();
    let last = calls.last().unwrap();
    assert_eq!(
        last.method, "end",
        "expected end when ref count reaches 0, got {last:?}"
    );

    cancel();
}

// Go: progress_test.go:243 TestProgress/NewTokenAfterEnd
#[test]
fn new_token_after_end() {
    let (reporter, cancel) = reporter();
    let p =
        new_project_loading_progress_from_reporter(reporter.clone(), Duration::from_millis(100));

    // First cycle.
    p.start(diag::Project_0, args("proj"));
    settle();
    sleep_past(Duration::from_millis(100));
    settle();

    let calls = reporter.get_calls();
    let first_token = calls[0].token.clone();

    p.finish(diag::Project_0, args("proj"));
    settle();

    // Second cycle — should get a new token.
    p.start(diag::Project_0, args("proj2"));
    settle();
    sleep_past(Duration::from_millis(100));
    settle();

    let calls = reporter.get_calls();
    let second_token = calls
        .iter()
        .find(|c| c.method == "create" && c.token != first_token)
        .map(|c| c.token.clone())
        .unwrap_or_default();
    assert!(
        !second_token.is_empty(),
        "expected a new token for second cycle, got calls: {calls:?}"
    );
    assert_ne!(
        first_token, second_token,
        "expected different tokens, both were {first_token:?}"
    );

    p.finish(diag::Project_0, args("proj2"));
    settle();

    cancel();
}

// Go: progress_test.go:291 TestProgress/StartBeforeDelayThenMoreAfterDelay
#[test]
fn start_before_delay_then_more_after_delay() {
    let (reporter, cancel) = reporter();
    let p =
        new_project_loading_progress_from_reporter(reporter.clone(), Duration::from_millis(200));

    // Start before delay.
    p.start(diag::Project_0, args("projA"));
    settle();

    // Let delay fire.
    sleep_past(Duration::from_millis(200));
    settle();

    let calls = reporter.get_calls();
    assert!(
        calls.len() >= 2,
        "expected create + begin after delay, got {calls:?}"
    );

    // Start another operation after delay — should send a report immediately.
    p.start(diag::Project_0, args("projB"));
    settle();

    let calls = reporter.get_calls();
    let last = calls.last().unwrap();
    assert_eq!(
        last.method, "report",
        "expected report for new start after delay, got {last:?}"
    );

    // Clean up.
    p.finish(diag::Project_0, args("projA"));
    p.finish(diag::Project_0, args("projB"));
    settle();

    cancel();
}

// Go: progress_test.go:331 TestProgress/FinishWithNoActiveToken
#[test]
fn finish_with_no_active_token() {
    let (reporter, cancel) = reporter();
    let p =
        new_project_loading_progress_from_reporter(reporter.clone(), Duration::from_millis(100));

    // Finish without any prior start — should be a no-op.
    p.finish(diag::Project_0, args("proj"));
    settle();

    let calls = reporter.get_calls();
    assert!(
        calls.is_empty(),
        "expected no calls for orphan finish, got {calls:?}"
    );

    cancel();
}

// Go: progress_test.go:352 TestProgress/ShutdownDuringStartAndFinish
#[test]
fn shutdown_during_start_and_finish() {
    let (reporter, cancel) = reporter();
    let p = new_project_loading_progress_from_reporter(reporter, Duration::from_millis(100));

    // Cancel context so the run goroutine exits.
    cancel();
    settle();

    // Fill the channel buffer so start/finish block on send.
    // PORT: Go sends `cap(p.ch)` (64) events. When the run thread has
    // already dropped the receiver, a send fails at once; that is fine.
    for _ in 0..64 {
        let _ = p.ch.try_send(Some(ProgressEvent {
            message: diag::Project_0,
            args: args("fill"),
            finish: false,
        }));
    }

    // These should return immediately via the done() path
    // since the channel is full and the context is cancelled.
    p.start(diag::Project_0, args("proj"));
    p.finish(diag::Project_0, args("proj"));
}

// Go: progress_test.go:375 TestProgress/ShutdownWithActiveTimer
#[test]
fn shutdown_with_active_timer() {
    let (reporter, cancel) = reporter();
    let p = new_project_loading_progress_from_reporter(reporter, Duration::from_millis(500));

    // Start an operation so the delay timer is created.
    p.start(diag::Project_0, args("proj"));
    settle();

    // Shutdown while the delay timer is still pending.
    cancel();
    settle();
}

// Go: progress_test.go:392 TestProgress/ZeroDelay
#[test]
fn zero_delay() {
    let (reporter, cancel) = reporter();
    let p = new_project_loading_progress_from_reporter(reporter.clone(), Duration::ZERO);

    // With zero delay, progress should begin immediately.
    p.start(diag::Project_0, args("proj"));
    settle();

    let calls = reporter.get_calls();
    assert_eq!(
        calls.len(),
        2,
        "expected 2 calls (create + begin), got {}: {calls:?}",
        calls.len()
    );
    assert_eq!(
        calls[0].method, "create",
        "expected create, got {:?}",
        calls[0]
    );
    assert_eq!(
        calls[1].method, "begin",
        "expected begin, got {:?}",
        calls[1]
    );
    assert_eq!(calls[1].msg, "Project 'proj'");

    // Start+finish should still produce begin and end.
    p.finish(diag::Project_0, args("proj"));
    settle();

    let calls = reporter.get_calls();
    let last = calls.last().unwrap();
    assert_eq!(last.method, "end", "expected end, got {last:?}");

    cancel();
}

// Go: progress_test.go:432 TestProgress/FinishBeforeDelayNoBegun
#[test]
fn finish_before_delay_no_begun() {
    let (reporter, cancel) = reporter();
    let p =
        new_project_loading_progress_from_reporter(reporter.clone(), Duration::from_millis(500));

    // Start, then finish before delay — begun is false, so no end is sent.
    p.start(diag::Project_0, args("proj"));
    settle();
    p.finish(diag::Project_0, args("proj"));
    settle();

    let calls = reporter.get_calls();
    assert!(
        !calls.iter().any(|c| c.method == "end"),
        "unexpected end when begun=false: {calls:?}"
    );

    cancel();
}
