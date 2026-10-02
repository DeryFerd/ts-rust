//! Go `golang.org/x/sync/errgroup` (v0.21.0 `errgroup/errgroup.go`) on
//! threads.
//!
//! Package errgroup provides synchronization, error propagation, and Context
//! cancellation for groups of goroutines working on subtasks of a common task.
//!
//! PORT: use this only for `Send` work (PORTING.md "Go runtime"). An errgroup
//! over dispatch-thread state runs serially in Go start order instead.

use crate::prelude::*;

use crate::gostd::context::{self, CancelCauseFunc, Context};
use crate::gostd::errors::GoError;
use std::any::Any;
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::sync::{Arc, Condvar, Mutex, MutexGuard, Once};

// PORT: Go mutexes do not poison.
fn lock<T>(m: &Mutex<T>) -> MutexGuard<'_, T> {
    m.lock().unwrap_or_else(|e| e.into_inner())
}

// Go: errgroup/errgroup.go:18 token
// PORT: Go `chan token` with capacity n is a counting semaphore here.
struct TokenChan {
    cap: usize,
    len: Mutex<usize>,
    cond: Condvar,
}

impl TokenChan {
    fn new(cap: usize) -> TokenChan {
        TokenChan {
            cap,
            len: Mutex::new(0),
            cond: Condvar::new(),
        }
    }

    /// Go `sem <- token{}` (blocks while the channel is full).
    fn send(&self) {
        let mut len = lock(&self.len);
        while *len >= self.cap {
            len = self.cond.wait(len).unwrap_or_else(|e| e.into_inner());
        }
        *len += 1;
        self.cond.notify_all();
    }

    /// Go `select { case sem <- token{}: return true; default: return false }`.
    fn try_send(&self) -> bool {
        let mut len = lock(&self.len);
        if *len >= self.cap {
            return false;
        }
        *len += 1;
        self.cond.notify_all();
        true
    }

    /// Go `<-sem`.
    fn recv(&self) {
        let mut len = lock(&self.len);
        while *len == 0 {
            len = self.cond.wait(len).unwrap_or_else(|e| e.into_inner());
        }
        *len -= 1;
        self.cond.notify_all();
    }

    /// Go `len(sem)`.
    fn len(&self) -> usize {
        *lock(&self.len)
    }
}

/// Go `sync.WaitGroup`.
struct WaitGroup {
    count: Mutex<i64>,
    cond: Condvar,
}

impl WaitGroup {
    fn new() -> WaitGroup {
        WaitGroup {
            count: Mutex::new(0),
            cond: Condvar::new(),
        }
    }

    fn add(&self, delta: i64) {
        let mut count = lock(&self.count);
        *count += delta;
        if *count < 0 {
            panic!("sync: negative WaitGroup counter");
        }
        if *count == 0 {
            self.cond.notify_all();
        }
    }

    fn done(&self) {
        self.add(-1);
    }

    fn wait(&self) {
        let mut count = lock(&self.count);
        while *count != 0 {
            count = self.cond.wait(count).unwrap_or_else(|e| e.into_inner());
        }
    }
}

// Go: errgroup/errgroup.go:25 Group
/// A Group is a collection of goroutines working on subtasks that are part of
/// the same overall task. A Group should not be reused for different tasks.
///
/// A zero Group (`Group::default()`) is valid, has no limit on the number of
/// active goroutines, and does not cancel on error.
///
/// PORT: Go `*Group`; clones share the group.
#[derive(Clone)]
pub struct Group(Arc<GroupInner>);

struct GroupInner {
    cancel: Option<CancelCauseFunc>,

    wg: WaitGroup,

    sem: Mutex<Option<Arc<TokenChan>>>,

    err_once: Once,
    err: Mutex<Option<GoError>>,

    /// PORT: the first panic of a goroutine; see `Group::wait`.
    panic: Mutex<Option<Box<dyn Any + Send>>>,
}

impl std::fmt::Debug for Group {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("errgroup.Group")
    }
}

impl Default for Group {
    fn default() -> Group {
        Group::with_cancel(None)
    }
}

impl Group {
    fn with_cancel(cancel: Option<CancelCauseFunc>) -> Group {
        Group(Arc::new(GroupInner {
            cancel,
            wg: WaitGroup::new(),
            sem: Mutex::new(None),
            err_once: Once::new(),
            err: Mutex::new(None),
            panic: Mutex::new(None),
        }))
    }

    // Go: errgroup/errgroup.go:36 done
    fn done(&self) {
        let sem = lock(&self.0.sem).clone();
        if let Some(sem) = sem {
            sem.recv();
        }
        self.0.wg.done();
    }

    // Go: errgroup/errgroup.go:55 Wait
    /// Wait blocks until all function calls from the Go method have returned, then
    /// returns the first non-nil error (if any) from them.
    ///
    /// PORT: in Go a panic in a goroutine ends the process. Here the first
    /// panic is kept and raised again from `wait` after all goroutines
    /// returned, so the caller's panic handling (exit code, unported report)
    /// sees it.
    pub fn wait(&self) -> Result<(), GoError> {
        self.0.wg.wait();
        if let Some(payload) = lock(&self.0.panic).take() {
            resume_unwind(payload);
        }
        let err = lock(&self.0.err).clone();
        if let Some(cancel) = &self.0.cancel {
            cancel(err.clone());
        }
        match err {
            Some(err) => Err(err),
            None => Ok(()),
        }
    }

    // Go: errgroup/errgroup.go:72 Go
    /// Go calls the given function in a new goroutine.
    ///
    /// The first call to Go must happen before a Wait.
    /// It blocks until the new goroutine can be added without the number of
    /// goroutines in the group exceeding the configured limit.
    ///
    /// The first goroutine in the group that returns a non-nil error will
    /// cancel the associated Context, if any. The error will be returned
    /// by Wait.
    pub fn go<F>(&self, f: F)
    where
        F: FnOnce() -> Result<(), GoError> + Send + 'static,
    {
        let sem = lock(&self.0.sem).clone();
        if let Some(sem) = sem {
            sem.send();
        }

        self.0.wg.add(1);
        self.spawn(f);
    }

    // Go: errgroup/errgroup.go:108 TryGo
    /// TryGo calls the given function in a new goroutine only if the number of
    /// active goroutines in the group is currently below the configured limit.
    ///
    /// The return value reports whether the goroutine was started.
    pub fn try_go<F>(&self, f: F) -> bool
    where
        F: FnOnce() -> Result<(), GoError> + Send + 'static,
    {
        let sem = lock(&self.0.sem).clone();
        if let Some(sem) = sem {
            if !sem.try_send() {
                return false;
            }
        }

        self.0.wg.add(1);
        self.spawn(f);
        true
    }

    // PORT: the goroutine body shared by Go and TryGo.
    fn spawn<F>(&self, f: F)
    where
        F: FnOnce() -> Result<(), GoError> + Send + 'static,
    {
        let g = self.clone();
        crate::core::GoThread::new()
            .name("errgroup".to_string())
            .stack_size(crate::gostd::stack::max_stack_size())
            .spawn(move || {
                // It is tempting to propagate panics from f()
                // up to the goroutine that calls Wait, but
                // it creates more problems than it solves:
                // - it delays panics arbitrarily,
                //   making bugs harder to detect;
                // - it turns f's panic stack into a mere value,
                //   hiding it from crash-monitoring tools;
                // - it risks deadlocks that hide the panic entirely,
                //   if f's panic leaves the program in a state
                //   that prevents the Wait call from being reached.
                // See #53757, #74275, #74304, #74306.
                //
                // PORT: a Rust panic only ends this thread, so it is kept
                // for `wait` (see there).
                match catch_unwind(AssertUnwindSafe(f)) {
                    Ok(Ok(())) => {}
                    Ok(Err(err)) => {
                        g.0.err_once.call_once(|| {
                            *lock(&g.0.err) = Some(err.clone());
                            if let Some(cancel) = &g.0.cancel {
                                cancel(Some(err));
                            }
                        });
                    }
                    Err(payload) => {
                        let mut panic = lock(&g.0.panic);
                        if panic.is_none() {
                            *panic = Some(payload);
                        }
                    }
                }
                // Go: defer g.done()
                g.done();
            });
    }

    // Go: errgroup/errgroup.go:142 SetLimit
    /// SetLimit limits the number of active goroutines in this group to at most n.
    /// A negative value indicates no limit.
    /// A limit of zero will prevent any new goroutines from being added.
    ///
    /// Any subsequent call to the Go method will block until it can add an active
    /// goroutine without exceeding the configured limit.
    ///
    /// The limit must not be modified while any goroutines in the group are active.
    pub fn set_limit(&self, n: i32) {
        let mut sem = lock(&self.0.sem);
        if n < 0 {
            *sem = None;
            return;
        }
        if let Some(s) = &*sem {
            let active = s.len();
            if active != 0 {
                panic!(
                    "errgroup: modify limit while {} goroutines in the group are still active",
                    active
                );
            }
        }
        *sem = Some(Arc::new(TokenChan::new(n as usize)));
    }
}

// Go: errgroup/errgroup.go:48 WithContext
/// WithContext returns a new Group and an associated Context derived from ctx.
///
/// The derived Context is canceled the first time a function passed to Go
/// returns a non-nil error or the first time Wait returns, whichever occurs
/// first.
pub fn with_context(ctx: &Context) -> (Group, Context) {
    let (ctx, cancel) = context::with_cancel_cause(ctx);
    (Group::with_cancel(Some(cancel)), ctx)
}
