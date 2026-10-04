//! PORT: no Go source. The port's model of the race between the answer of
//! a request and the snapshot tasks that the request starts.
//!
//! Go: `updateSnapshot` (project/session.go:1396) starts each snapshot task
//! on its own goroutine: logs, `updateWatches` (a registerCapability per
//! new glob, each waiting for the client's reply), the content-mapper
//! registration, then `publishProgramDiagnostics`. The handler goes on at
//! the same time and sends its answer when it returns (lsp/server.go:1337,
//! :1363). So the client sees one of these orders:
//!
//! - answer, register, diag: the handler ends before the task starts (no
//!   checker build, a few hundred microseconds of work);
//! - register, answer, diag: the task waits for the reply, and then its
//!   diagnostics step waits for `checkerPool.mu` while the handler builds
//!   a checker; the handler answers right after the build;
//! - register, diag, answer: the reply comes during the build, and the
//!   handler works on after the build.
//!
//! The port has one dispatch thread, so a task can not run while the
//! handler works. A snapshot task is a future here. While a request is in
//! flight (`begin_request` to its answer), its tasks run only at these
//! points, which give the Go orders above:
//!
//! - `build_start`: a checker build. Go's build takes about a millisecond,
//!   so the task starts during it: it runs up to its first wait for the
//!   client (the register goes out). `build_end` lets it go on when the
//!   reply is in, up to its diagnostics step.
//! - `loop_point`: a long loop with no checker (workspace/symbol). A task
//!   starts after `TASK_START_GO`, and its diagnostics step runs
//!   `DIAG_STEP_GO` after the reply.
//! - `answer_point`: just before the answer. A task that has not started
//!   starts after the answer. A task at its diagnostics step runs it before
//!   the answer when the step has been ready for `DIAG_STEP_GO` (the reply
//!   came, and the last checker build ended, that long ago).
//!
//! A task never waits for the client while a request is in flight: its
//! client call returns `Pending`, and the request goes on. Outside a request
//! (after the answer, at the end of a message, in a notification) the
//! tasks run in `gostd::local::run_pending` as before, and a client call
//! blocks the dispatch thread until the reply, so all of a message's tasks
//! end before the next message (lsp/server.rs "Effects of the one dispatch
//! thread").
//!
//! The async part of a request (`open_gates`) runs its tasks before it, up to
//! their first wait for the client, as the port did before; a task with no
//! client call runs to its end there.

use crate::project::background::prelude::*;
use std::cell::Cell;
use std::future::Future;
use std::pin::Pin;
use std::task::{Poll, Waker};
use std::time::{Duration, Instant};

/// Go's time from a snapshot update to the first client call of its task
/// (the goroutine start, the adoption logs and the watch diff): 0.15 to
/// 0.45 ms on the 4-file probe project. A loop with no checker build starts
/// the task after this time.
pub const TASK_START_GO: Duration = Duration::from_micros(450);

/// Go's time for the diagnostics step of a snapshot task once it can run
/// (it has the reply, and the handler's checker build has ended):
/// `GetGlobalDiagnostics` and the publishDiagnostics, 0.01 to 0.14 ms. A
/// handler that works on longer than this after that point answers after
/// the diagnostics.
pub const DIAG_STEP_GO: Duration = Duration::from_micros(100);

/// The future of a snapshot task.
pub type TaskFuture = Pin<Box<dyn Future<Output = ()>>>;

/// What the scheduler and one task share.
struct TaskInfo {
    /// The snapshot update that queued the task.
    queued_at: Instant,
    /// The task may start (its first step) while a request is in flight.
    start_ok: Cell<bool>,
    /// The task may run its diagnostics step while a request is in flight.
    diag_ok: Cell<bool>,
    /// The task waits at its diagnostics step.
    at_diag: Cell<bool>,
    /// The step after the gate calls the client (the content-mapper
    /// registration), so it does not run while a request is in flight.
    diag_calls_client: Cell<bool>,
    /// When the task last went on: its start, or the arrival of the last
    /// client reply.
    ready_at: Cell<Instant>,
}

struct Task {
    info: Rc<TaskInfo>,
    /// None while the task is polled.
    fut: RefCell<Option<TaskFuture>>,
}

/// The request in flight on this thread.
struct Request {
    answered: bool,
    /// The end of the last checker build of the request.
    last_build_end: Option<Instant>,
}

thread_local! {
    /// The snapshot tasks that have not ended, in the order of their
    /// snapshot updates.
    static TASKS: RefCell<Vec<Rc<Task>>> = const { RefCell::new(Vec::new()) };
    static REQUEST: RefCell<Option<Request>> = const { RefCell::new(None) };
    /// The task being polled.
    static CURRENT: RefCell<Option<Rc<TaskInfo>>> = const { RefCell::new(None) };
    /// The gates are open (`open_gates`).
    static FREE: Cell<u32> = const { Cell::new(0) };
    /// A caller waits for the tasks (`background::Queue::wait`): the gates
    /// are open and client calls block.
    static WAITING: Cell<u32> = const { Cell::new(0) };
}

/// Whether a request is in flight and has not answered.
pub fn in_request() -> bool {
    REQUEST.with(|r| r.borrow().as_ref().is_some_and(|r| !r.answered))
}

/// Whether a client call of a snapshot task may block the thread until the
/// reply. False while a request is in flight: the call returns `Pending`.
pub fn may_block() -> bool {
    !in_request() || WAITING.with(Cell::get) > 0
}

fn gates_open() -> bool {
    !in_request() || FREE.with(Cell::get) > 0 || WAITING.with(Cell::get) > 0
}

fn polling() -> bool {
    CURRENT.with(|c| c.borrow().is_some())
}

/// The gates of one snapshot task, which its future awaits.
pub struct Gates {
    info: Rc<TaskInfo>,
}

impl Gates {
    /// Waits until the task may start.
    pub async fn start(&self) {
        std::future::poll_fn(|_| {
            if gates_open() || self.info.start_ok.get() {
                self.info.ready_at.set(Instant::now());
                Poll::Ready(())
            } else {
                Poll::Pending
            }
        })
        .await
    }

    /// Waits until the task may run its diagnostics step. `calls_client`
    /// tells whether the step before the diagnostics will call the client.
    pub async fn diag(&self, calls_client: impl Fn() -> bool) {
        std::future::poll_fn(|_| {
            if gates_open() || self.info.diag_ok.get() {
                self.info.at_diag.set(false);
                Poll::Ready(())
            } else {
                self.info.at_diag.set(true);
                self.info.diag_calls_client.set(calls_client());
                Poll::Pending
            }
        })
        .await
    }
}

/// Starts a snapshot task: `make` gets its gates and returns its future.
/// The task runs in the next `gostd::local::run_pending`, or at a point of
/// the request in flight.
pub fn spawn(make: impl FnOnce(Gates) -> TaskFuture) {
    let now = Instant::now();
    let info = Rc::new(TaskInfo {
        queued_at: now,
        start_ok: Cell::new(false),
        diag_ok: Cell::new(false),
        at_diag: Cell::new(false),
        diag_calls_client: Cell::new(false),
        ready_at: Cell::new(now),
    });
    let fut = make(Gates { info: info.clone() });
    let task = Rc::new(Task {
        info,
        fut: RefCell::new(Some(fut)),
    });
    TASKS.with(|t| t.borrow_mut().push(task.clone()));
    queue_poll(task);
}

/// Polls `task` in the next `gostd::local::run_pending`.
fn queue_poll(task: Rc<Task>) {
    gostd::local::go(Box::new(move || poll(&task)));
}

/// Polls `task` once, unless it is being polled or has ended. A task wakes
/// only at the points of this module: it is polled with a no-op waker.
fn poll(task: &Rc<Task>) {
    let Some(mut fut) = task.fut.borrow_mut().take() else {
        return;
    };
    let prev = CURRENT.with(|c| c.replace(Some(task.info.clone())));
    let mut cx = std::task::Context::from_waker(Waker::noop());
    // Go: the wg.Go goroutine recovers a panic and raises it again.
    let ready = crate::core::go_wait_group_task(|| fut.as_mut().poll(&mut cx).is_ready());
    CURRENT.with(|c| *c.borrow_mut() = prev);
    if ready {
        TASKS.with(|t| t.borrow_mut().retain(|other| !Rc::ptr_eq(other, task)));
    } else {
        *task.fut.borrow_mut() = Some(fut);
    }
}

fn tasks() -> Vec<Rc<Task>> {
    TASKS.with(|t| t.borrow().clone())
}

fn has_tasks() -> bool {
    TASKS.with(|t| !t.borrow().is_empty())
}

/// Polls the tasks that have started, in order.
fn poll_started() {
    for task in tasks() {
        if task.info.start_ok.get() {
            poll(&task);
        }
    }
}

/// Runs the diagnostics step of each task that waits at it, when the step
/// has been ready for `DIAG_STEP_GO` at `now`.
fn run_ready_diags(now: Instant) {
    let last_build_end = REQUEST.with(|r| r.borrow().as_ref().and_then(|r| r.last_build_end));
    for task in tasks() {
        let info = &task.info;
        if !info.at_diag.get() || info.diag_calls_client.get() {
            continue;
        }
        let ready = match last_build_end {
            Some(end) => end.max(info.ready_at.get()),
            None => info.ready_at.get(),
        };
        if now.saturating_duration_since(ready) >= DIAG_STEP_GO {
            info.diag_ok.set(true);
            poll(&task);
        }
    }
}

/// Whether the points below act: a request is in flight, a task waits, and
/// no task is being polled (a task's own checker build is not a point).
fn active() -> bool {
    in_request() && !polling() && has_tasks()
}

/// Records that the running task's client call got its reply at `at`.
pub fn note_reply(at: Instant) {
    CURRENT.with(|c| {
        if let Some(info) = c.borrow().as_ref() {
            info.ready_at.set(info.ready_at.get().max(at));
        }
    });
}

/// The request in flight on this thread from `begin_request` to the drop
/// of the guard.
pub struct RequestGuard {
    prev: Option<Request>,
}

/// Starts a request (a message with an ID) on the dispatch thread.
pub fn begin_request() -> RequestGuard {
    let prev = REQUEST.with(|r| {
        r.borrow_mut().replace(Request {
            answered: false,
            last_build_end: None,
        })
    });
    RequestGuard { prev }
}

impl Drop for RequestGuard {
    fn drop(&mut self) {
        let prev = self.prev.take();
        REQUEST.with(|r| *r.borrow_mut() = prev);
        // The tasks go on in the next run_pending, now outside the request.
        for task in tasks() {
            queue_poll(task);
        }
    }
}

/// Runs `f` (the `run_pending` before the async part of a request) with
/// the gates open: the tasks that the sync part queued run up to their
/// first wait for the client, or to their end.
pub fn open_gates(f: impl FnOnce()) {
    FREE.with(|n| n.set(n.get() + 1));
    for task in tasks() {
        task.info.start_ok.set(true);
    }
    f();
    FREE.with(|n| n.set(n.get() - 1));
}

/// Runs `f` (a wait for the background tasks) with the gates open and
/// blocking client calls.
pub fn waiting(f: impl FnOnce()) {
    WAITING.with(|n| n.set(n.get() + 1));
    for task in tasks() {
        queue_poll(task);
    }
    f();
    WAITING.with(|n| n.set(n.get() - 1));
}

/// A checker build starts during the request in flight. Go's tasks run
/// during the build up to their diagnostics step, which waits for
/// `checkerPool.mu`.
pub fn build_start() {
    if !active() {
        return;
    }
    for task in tasks() {
        task.info.start_ok.set(true);
    }
    poll_started();
}

/// A checker build of the request in flight ended.
pub fn build_end() {
    if !in_request() || polling() {
        return;
    }
    let now = Instant::now();
    REQUEST.with(|r| {
        if let Some(r) = r.borrow_mut().as_mut() {
            r.last_build_end = Some(now);
        }
    });
    if has_tasks() {
        poll_started();
    }
}

/// One step of a long loop with no checker build (workspace/symbol).
pub fn loop_point() {
    if !active() {
        return;
    }
    let now = Instant::now();
    for task in tasks() {
        if !task.info.start_ok.get()
            && now.saturating_duration_since(task.info.queued_at) >= TASK_START_GO
        {
            task.info.start_ok.set(true);
        }
    }
    poll_started();
    run_ready_diags(now);
}

/// The request in flight sends its answer (a result or an error). After
/// this the tasks run outside the request.
pub fn answer_point() {
    if !in_request() || polling() {
        return;
    }
    if has_tasks() {
        poll_started();
        run_ready_diags(Instant::now());
    }
    REQUEST.with(|r| {
        if let Some(r) = r.borrow_mut().as_mut() {
            r.answered = true;
        }
    });
}
