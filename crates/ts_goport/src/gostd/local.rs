//! The dispatch-thread work queue. No Go source: this is the port's model
//! for Go goroutines and `time.AfterFunc` callbacks that touch
//! language-service state (PORTING.md "Threads" and "Go runtime").
//!
//! One thread (the LSP dispatch thread) owns all `Rc`/`RefCell` state. A Go
//! `go f()` over that state becomes `local::go(Box::new(f))`, and a Go
//! `time.AfterFunc(d, f)` over that state becomes `local::after_func`. Both
//! run on the dispatch thread when it calls `run_pending`, in the order they
//! became ready: a job when it is queued, a timer when it is due.
//!
//! Contract with the dispatch loop: the server calls `set_waker(f)` once. A
//! timer thread calls the waker when a `LocalTimer` becomes due. The
//! dispatch loop calls `run_pending()` after each message and after each
//! wake-up; Go `WaitForBackgroundTasks` calls it until `has_pending()` is
//! false.
//!
//! The queue is per thread: `go`, `after_func` and `run_pending` act on the
//! calling thread's queue.

use crate::prelude::*;

use std::cell::Cell;
use std::collections::VecDeque;
use std::sync::{Arc, Condvar, Mutex, MutexGuard};
use std::time::{Duration, Instant};

// PORT: Go mutexes do not poison.
fn lock<T>(m: &Mutex<T>) -> MutexGuard<'_, T> {
    m.lock().unwrap_or_else(|e| e.into_inner())
}

/// The waker the dispatch loop installs with `set_waker`.
pub type Waker = Arc<dyn Fn() + Send + Sync>;

/// The part of a thread's queue that timer threads can reach.
struct LocalShared {
    /// Ready work in the order it became ready.
    queue: Mutex<VecDeque<Entry>>,
    waker: Mutex<Option<Waker>>,
}

#[derive(Clone, Copy)]
enum Entry {
    /// A job from `go`, by id.
    Job(u64),
    /// A due `LocalTimer`, by id.
    Timer(u64),
}

/// The thread-local part: closures that are not `Send`.
struct LocalState {
    shared: Arc<LocalShared>,
    next_id: Cell<u64>,
    jobs: RefCell<FxHashMap<u64, Box<dyn FnOnce()>>>,
    /// Timers that are armed or have a due entry in the queue.
    timers: RefCell<FxHashMap<u64, Rc<LocalTimerInner>>>,
}

thread_local! {
    static LOCAL: LocalState = LocalState {
        shared: Arc::new(LocalShared { queue: Mutex::new(VecDeque::new()), waker: Mutex::new(None) }),
        next_id: Cell::new(1),
        jobs: RefCell::new(FxHashMap::default()),
        timers: RefCell::new(FxHashMap::default()),
    };
}

fn next_id() -> u64 {
    LOCAL.with(|l| {
        let id = l.next_id.get();
        l.next_id.set(id + 1);
        id
    })
}

/// Go `go f()` for a function that touches dispatch-thread state: queue `f`
/// to run on this thread in FIFO order.
pub fn go(f: Box<dyn FnOnce()>) {
    let id = next_id();
    LOCAL.with(|l| {
        l.jobs.borrow_mut().insert(id, f);
        lock(&l.shared.queue).push_back(Entry::Job(id));
    });
}

/// Installs the function that timer threads call when a `LocalTimer` of this
/// thread becomes due. The dispatch loop wakes and calls `run_pending`.
pub fn set_waker(f: Waker) {
    LOCAL.with(|l| {
        *lock(&l.shared.waker) = Some(f);
    });
}

/// Whether ready work (queued jobs or due timers) is waiting for
/// `run_pending`. Armed timers that are not due yet do not count.
pub fn has_pending() -> bool {
    LOCAL.with(|l| !lock(&l.shared.queue).is_empty())
}

/// Runs the ready work of this thread in the order it became ready, until
/// the queue is empty. Work that a job queues (or a timer that becomes due
/// meanwhile) also runs before this returns.
pub fn run_pending() {
    let shared = LOCAL.with(|l| l.shared.clone());
    loop {
        let entry = lock(&shared.queue).pop_front();
        let Some(entry) = entry else {
            return;
        };
        match entry {
            Entry::Job(id) => {
                let job = LOCAL.with(|l| l.jobs.borrow_mut().remove(&id));
                if let Some(job) = job {
                    job();
                }
            }
            Entry::Timer(id) => {
                let timer = LOCAL.with(|l| l.timers.borrow().get(&id).cloned());
                let Some(timer) = timer else {
                    continue;
                };
                {
                    let mut state = lock(&timer.core.state);
                    state.queued -= 1;
                }
                // Go: the goroutine that the timer started runs f.
                {
                    let mut f = timer.f.borrow_mut();
                    (*f)();
                }
                timer.forget_if_idle();
            }
        }
    }
}

/// Go `*time.Timer` from `time.AfterFunc` whose function runs on the
/// dispatch thread.
pub struct LocalTimer {
    inner: Rc<LocalTimerInner>,
}

struct LocalTimerInner {
    id: u64,
    f: RefCell<Box<dyn FnMut()>>,
    core: Arc<LocalTimerCore>,
}

/// The `Send` part of a `LocalTimer`, shared with its waiting thread.
struct LocalTimerCore {
    id: u64,
    state: Mutex<LocalTimerState>,
    cond: Condvar,
    shared: Arc<LocalShared>,
}

struct LocalTimerState {
    /// Go `t.when`; `None` is not armed.
    when: Option<Instant>,
    /// Whether a thread is waiting for `when`.
    thread_running: bool,
    /// Due entries of this timer in the queue that have not run yet.
    queued: u32,
}

/// Go `time.AfterFunc(d, f)` when `f` touches dispatch-thread state. After
/// `d`, `f` is queued on this thread (the waker is called) and runs in
/// `run_pending`.
///
/// PORT: Go `f` runs each time the timer fires, and it fires again after a
/// `reset`, so `f` is `FnMut`.
pub fn after_func(d: Duration, f: Box<dyn FnMut()>) -> LocalTimer {
    let id = next_id();
    let shared = LOCAL.with(|l| l.shared.clone());
    let inner = Rc::new(LocalTimerInner {
        id,
        f: RefCell::new(f),
        core: Arc::new(LocalTimerCore {
            id,
            state: Mutex::new(LocalTimerState {
                when: None,
                thread_running: false,
                queued: 0,
            }),
            cond: Condvar::new(),
            shared,
        }),
    });
    inner.arm(when(d));
    LOCAL.with(|l| {
        l.timers.borrow_mut().insert(id, inner.clone());
    });
    LocalTimer { inner }
}

impl LocalTimer {
    /// Go `t.Stop()` of an AfterFunc timer: true if the call stops the
    /// timer, false if the timer has already expired (its function is queued
    /// or has run) or been stopped. Stop does not remove a queued run.
    pub fn stop(&self) -> bool {
        let pending = {
            let mut state = lock(&self.inner.core.state);
            let pending = state.when.is_some();
            state.when = None;
            self.inner.core.cond.notify_all();
            pending
        };
        self.inner.forget_if_idle();
        pending
    }

    /// Go `t.Reset(d)` of an AfterFunc timer: true if the timer had been
    /// active; false if it had expired or been stopped, in which case the
    /// function runs again after `d`.
    pub fn reset(&self, d: Duration) -> bool {
        let pending = self.inner.arm(when(d));
        LOCAL.with(|l| {
            l.timers
                .borrow_mut()
                .entry(self.inner.id)
                .or_insert_with(|| self.inner.clone());
        });
        pending
    }
}

impl std::fmt::Debug for LocalTimer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "LocalTimer(when: {:?})",
            lock(&self.inner.core.state).when
        )
    }
}

impl LocalTimerInner {
    /// Sets `when` and makes sure a thread waits for it. Returns whether the
    /// timer was armed before.
    fn arm(&self, when: Instant) -> bool {
        let mut state = lock(&self.core.state);
        let pending = state.when.is_some();
        state.when = Some(when);
        if state.thread_running {
            self.core.cond.notify_all();
        } else {
            state.thread_running = true;
            let core = self.core.clone();
            std::thread::Builder::new()
                .name("local-timer".to_string())
                .spawn(move || run_local_timer(core))
                .expect("local: failed to start the timer thread");
        }
        pending
    }

    /// Drops this thread's reference when the timer is neither armed nor
    /// queued, so an unreferenced timer is freed.
    fn forget_if_idle(&self) {
        let idle = {
            let state = lock(&self.core.state);
            state.when.is_none() && state.queued == 0
        };
        if idle {
            LOCAL.with(|l| {
                l.timers.borrow_mut().remove(&self.id);
            });
        }
    }
}

/// The waiting thread of one `LocalTimer`: when the timer is due it queues
/// the timer on its thread and calls the waker, then exits unless the timer
/// was armed again.
fn run_local_timer(core: Arc<LocalTimerCore>) {
    let mut state = lock(&core.state);
    loop {
        let Some(w) = state.when else {
            state.thread_running = false;
            return;
        };
        let now = Instant::now();
        if now < w {
            state = core
                .cond
                .wait_timeout(state, w - now)
                .unwrap_or_else(|e| e.into_inner())
                .0;
            continue;
        }
        state.when = None;
        state.queued += 1;
        lock(&core.shared.queue).push_back(Entry::Timer(core.id));
        drop(state);
        let waker = lock(&core.shared.waker).clone();
        if let Some(waker) = waker {
            waker();
        }
        state = lock(&core.state);
    }
}

// Go: time/sleep.go:52 when
fn when(d: Duration) -> Instant {
    let now = Instant::now();
    match now.checked_add(d) {
        Some(t) => t,
        // PORT: Go clamps to MaxInt64 nanoseconds.
        None => {
            let mut d = Duration::from_nanos(i64::MAX as u64);
            loop {
                if let Some(t) = now.checked_add(d) {
                    return t;
                }
                d /= 2;
            }
        }
    }
}
