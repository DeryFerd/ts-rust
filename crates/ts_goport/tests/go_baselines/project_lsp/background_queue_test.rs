//! Port of Go `internal/project/background/queue_test.go`.
//!
//! PORT: the Rust queue runs its tasks on the calling thread
//! (`gostd::local`), so the Go atomics and mutexes are `Cell`/`RefCell`.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use ts_goport::gostd::context;
use ts_goport::project::background;

// Go: queue_test.go:15 TestQueue/BasicEnqueue
#[test]
fn queue_basic_enqueue() {
    let q = background::new_queue();

    let executed = Rc::new(Cell::new(false));
    let e = executed.clone();
    q.enqueue(&context::background(), move |_ctx| {
        e.set(true);
    });

    q.wait();
    q.close();

    assert!(executed.get());
}

// Go: queue_test.go:30 TestQueue/MultipleTasksExecution
#[test]
fn queue_multiple_tasks_execution() {
    let q = background::new_queue();

    let counter = Rc::new(Cell::new(0i64));
    let num_tasks = 10;

    for _ in 0..num_tasks {
        let c = counter.clone();
        q.enqueue(&context::background(), move |_ctx| {
            c.set(c.get() + 1);
        });
    }

    q.wait();
    q.close();

    assert_eq!(counter.get(), num_tasks);
}

// Go: queue_test.go:49 TestQueue/NestedEnqueue
#[test]
fn queue_nested_enqueue() {
    let q = background::new_queue();

    let executed: Rc<RefCell<Vec<&'static str>>> = Rc::default();

    let outer = executed.clone();
    let q2 = q.clone();
    q.enqueue(&context::background(), move |ctx| {
        outer.borrow_mut().push("parent");

        let inner = outer.clone();
        q2.enqueue(ctx, move |_child_ctx| {
            inner.borrow_mut().push("child");
        });
    });

    q.wait();
    q.close();

    assert_eq!(executed.borrow().len(), 2);
}

// Go: queue_test.go:77 TestQueue/ClosedQueueRejectsNewTasks
#[test]
fn queue_closed_queue_rejects_new_tasks() {
    let q = background::new_queue();
    q.close();

    let executed = Rc::new(Cell::new(false));
    let e = executed.clone();
    q.enqueue(&context::background(), move |_ctx| {
        e.set(true);
    });

    q.wait();

    assert!(
        !executed.get(),
        "Task should not execute after queue is closed"
    );
}
