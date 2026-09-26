//! Go `internal/project/background/queue.go`.
//!
//! PORT: background tasks touch dispatch-thread state, so `wg.Go` posts the
//! task to `gostd::local::go` (PORTING "Go runtime"). The dispatch loop runs
//! it later, in enqueue order. `Wait` runs `gostd::local::run_pending` until
//! this queue's tasks have finished. `mu` is dropped (one thread).

use crate::project::background::prelude::*;
use std::cell::Cell;

// Go: project/background/queue.go:8 Queue
// Queue manages background tasks execution
pub struct Queue {
    // PORT: Go `wg sync.WaitGroup`: the number of enqueued tasks that have
    // not finished. Shared with the posted tasks.
    wg: Rc<Cell<i32>>,
    closed: Cell<bool>,
}

// Go: project/background/queue.go:15 NewQueue
// NewQueue creates a new background queue for managing background tasks execution.
pub fn new_queue() -> Rc<Queue> {
    Rc::new(Queue {
        wg: Rc::new(Cell::new(0)),
        closed: Cell::new(false),
    })
}

// PORT: Go `defer wg.Done()` inside `wg.Go`.
struct WaitGroupDone(Rc<Cell<i32>>);

impl Drop for WaitGroupDone {
    fn drop(&mut self) {
        self.0.set(self.0.get() - 1);
    }
}

impl Queue {
    // Go: project/background/queue.go:20 Enqueue
    pub fn enqueue(&self, ctx: &Context, fn_: impl FnOnce(&Context) + 'static) {
        if self.closed.get() {
            return;
        }

        // Don't start new tasks if context is already cancelled
        if ctx.err().is_some() {
            return;
        }

        // Go: q.wg.Go(func() { ... })
        self.wg.set(self.wg.get() + 1);
        let wg = self.wg.clone();
        let ctx = ctx.clone();
        gostd::local::go(Box::new(move || {
            let _done = WaitGroupDone(wg);
            // Check context again before executing
            if ctx.err().is_some() {
                return;
            }
            fn_(&ctx);
        }));
    }

    // Go: project/background/queue.go:42 Wait
    // Wait waits for all active tasks to complete.
    // It does not prevent new tasks from being enqueued while waiting.
    pub fn wait(&self) {
        while self.wg.get() > 0 {
            // PORT: Go blocks forever when the tasks can never finish (for
            // example, Wait called from inside one of them). The port panics
            // instead of spinning.
            if !gostd::local::has_pending() {
                panic!(
                    "background.Queue.Wait: {} task(s) can not finish on the dispatch thread",
                    self.wg.get()
                );
            }
            gostd::local::run_pending();
        }
    }

    // Go: project/background/queue.go:48 Close
    pub fn close(&self) {
        self.closed.set(true);
    }
}
