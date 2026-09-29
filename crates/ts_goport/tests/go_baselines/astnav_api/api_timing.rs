//! Port of internal/ipc/timing_test.go (tsgo#4512; internal/api/timing_test.go
//! before tsgo#4712). The file keeps its `api_timing` name, so the test
//! names do not change.
//!
//! PORT: Go `time.Duration` is signed and a `std::time::Duration` is not, so
//! the Go cases with a negative duration ("negative durations clamp to zero"
//! and `durationToMillis(-5*time.Second)`) have no port.

use super::Subtests;
use std::time::Duration;
use ts_goport::ipc::{
    SERVER_RECENT_REQUEST_CAPACITY, duration_to_millis, new_timing_collector,
    server_timing_snapshot,
};

// Go: ipc/timing_test.go:10 TestTimingCollector
#[test]
fn test_timing_collector() {
    let mut t = Subtests::new("TestTimingCollector");

    t.run("accumulates totals and records recent requests", || {
        let mut c = new_timing_collector();
        c.record("getSourceFile", Duration::from_millis(2));
        c.record("getSymbolAtPosition", Duration::from_micros(500));

        let snap = c.snapshot();
        assert!(snap.enabled);
        assert_eq!(snap.totals.request_count, 2);
        assert_eq!(snap.totals.total_processing_time_ms, 2.5);
        assert_eq!(snap.recent_requests.len(), 2);
        assert_eq!(snap.recent_requests[0].method, "getSourceFile");
        assert_eq!(snap.recent_requests[0].processing_time_ms, 2.0);
        assert_eq!(snap.recent_requests[1].method, "getSymbolAtPosition");
        assert_eq!(snap.recent_requests[1].processing_time_ms, 0.5);
        Ok(())
    });

    t.run(
        "ring buffer retains only the most recent requests, oldest to newest",
        || {
            let mut c = new_timing_collector();
            let methods = ["a", "b", "c", "d", "e", "f", "g"];
            for m in methods {
                c.record(m, Duration::from_millis(1));
            }

            let snap = c.snapshot();
            assert_eq!(snap.totals.request_count, 7);
            assert_eq!(snap.recent_requests.len(), SERVER_RECENT_REQUEST_CAPACITY);

            // Expect the last 5 methods, oldest to newest.
            let want = &methods[methods.len() - SERVER_RECENT_REQUEST_CAPACITY..];
            for (i, w) in want.iter().enumerate() {
                assert_eq!(snap.recent_requests[i].method, *w);
            }
            Ok(())
        },
    );

    t.finish();
}

// Go: ipc/timing_test.go:59 TestServerTimingSnapshotDisabled
#[test]
fn test_server_timing_snapshot_disabled() {
    let snap = server_timing_snapshot(None);
    assert!(!snap.enabled);
    assert_eq!(snap.totals.request_count, 0);
    assert_eq!(snap.recent_requests.len(), 0);
}

// Go: ipc/timing_test.go:67 TestTimingCollectorReset
#[test]
fn test_timing_collector_reset() {
    let mut c = new_timing_collector();
    c.record("a", Duration::from_millis(1));
    c.record("b", Duration::from_millis(1));
    c.reset();

    let snap = c.snapshot();
    assert!(snap.enabled);
    assert_eq!(snap.totals.request_count, 0);
    assert_eq!(snap.totals.total_processing_time_ms, 0.0);
    assert_eq!(snap.recent_requests.len(), 0);

    // The collector remains usable after a reset.
    c.record("c", Duration::from_millis(2));
    let snap = c.snapshot();
    assert_eq!(snap.totals.request_count, 1);
    assert_eq!(snap.recent_requests[0].method, "c");
}

// Go: ipc/timing_test.go:87 TestDurationToMillis
#[test]
fn test_duration_to_millis() {
    assert_eq!(duration_to_millis(Duration::from_micros(1500)), 1.5);
    assert_eq!(duration_to_millis(Duration::ZERO), 0.0);
    // Sub-microsecond durations retain precision rather than truncating to 0.
    assert_eq!(duration_to_millis(Duration::from_nanos(500)), 0.0005);
    assert_eq!(duration_to_millis(Duration::from_nanos(1234)), 0.001234);
}
