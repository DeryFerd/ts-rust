//! Port of Go `internal/lsp/dynamic_queue_test.go`.

use ts_goport::gostd::{context, errors};
use ts_goport::lsp::dynamic_queue::new_dynamic_queue;

// Go: dynamic_queue_test.go:9 TestDynamicQueueFIFO
#[test]
fn dynamic_queue_fifo() {
    let ctx = context::background();
    let q = new_dynamic_queue::<i32>();

    for i in 0..1000 {
        q.put(&ctx, i)
            .unwrap_or_else(|err| panic!("{}", err.error()));
    }

    for i in 0..1000 {
        let got = q.get(&ctx).unwrap_or_else(|err| panic!("{}", err.error()));
        assert_eq!(got, i, "Get() = {got}, want {i}");
    }
}

// Go: dynamic_queue_test.go:32 TestDynamicQueueGetCancellation
#[test]
fn dynamic_queue_get_cancellation() {
    let (ctx, cancel) = context::with_cancel(&context::background());
    cancel();

    let q = new_dynamic_queue::<i32>();
    let result = q.get(&ctx);
    match result {
        Err(err) => assert!(
            errors::is(&err, &context::CANCELED),
            "Get() error = {}, want {}",
            err.error(),
            context::CANCELED.error()
        ),
        Ok(got) => panic!("Get() = {got}, want error {}", context::CANCELED.error()),
    }
}

// Go: dynamic_queue_test.go:48 TestDynamicQueuePutCancellationWhileStateUnavailable
// PORT: blocked. The Go test takes the queue state with the private
// `getAny` and puts it back on the private `idle` channel. The Rust queue
// keeps its state behind a private mutex (`DynamicQueue::get_any` is not
// `pub`), so the test cannot hold the state. The cancelled `Put` part runs.
#[test]
fn dynamic_queue_put_cancellation_while_state_unavailable() {
    let q = new_dynamic_queue::<i32>();

    let (ctx, cancel) = context::with_cancel(&context::background());
    cancel();

    let put_err = q.put(&ctx, 1);
    match put_err {
        Err(err) => assert!(
            errors::is(&err, &context::CANCELED),
            "Put() error = {}, want {}",
            err.error(),
            context::CANCELED.error()
        ),
        Ok(()) => panic!("Put() error = nil, want {}", context::CANCELED.error()),
    }

    q.put(&context::background(), 2)
        .unwrap_or_else(|err| panic!("{}", err.error()));
    let got = q
        .get(&context::background())
        .unwrap_or_else(|err| panic!("{}", err.error()));
    assert_eq!(got, 2, "Get() = {got}, want 2");
}
