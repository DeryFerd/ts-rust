//! Port of internal/api/timing.go.
//!
//! PORT: Go guards `timingCollector` with a mutex so the async connection
//! can record from several request goroutines. The connections here run on
//! the dispatch thread, so the collector has no lock (PORTING "Threads").

use crate::frontend::json::{JsonError, MarshalerTo};
use crate::frontend::json_ext::{marshal_field, write_object_end, write_object_start};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

// Go: api/timing.go:10 serverRecentRequestCapacity
// serverRecentRequestCapacity is the number of most-recent requests retained in
// the server-side timing ring buffer.
pub const SERVER_RECENT_REQUEST_CAPACITY: usize = 5;

// Go: api/timing.go:13 serverRequestTiming
// serverRequestTiming is a single server-side request's processing-time sample.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ServerRequestTiming {
    // Method is the API method that was handled.
    pub method: String,
    // ProcessingTimeMs is the wall-clock time the server spent handling the
    // request, in milliseconds.
    pub processing_time_ms: f64,
    // Timestamp is the Unix time in milliseconds when the request completed.
    pub timestamp: i64,
}

/// Go int64 JSON (v2 `makeIntArshaler`): the decimal digits.
struct Int64(i64);

impl MarshalerTo for Int64 {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        enc.push_str(&self.0.to_string());
        Ok(())
    }
}

impl MarshalerTo for ServerRequestTiming {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        let mut first = true;
        marshal_field(enc, &mut first, "method", &self.method)?;
        marshal_field(
            enc,
            &mut first,
            "processingTimeMs",
            &self.processing_time_ms,
        )?;
        marshal_field(enc, &mut first, "timestamp", &Int64(self.timestamp))?;
        write_object_end(enc);
        Ok(())
    }
}

// Go: api/timing.go:24 serverTimingTotals
// serverTimingTotals holds running totals accumulated across every handled request.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ServerTimingTotals {
    // RequestCount is the total number of requests measured.
    pub request_count: u64,
    // TotalProcessingTimeMs is the sum of server processing time, in milliseconds.
    pub total_processing_time_ms: f64,
}

impl MarshalerTo for ServerTimingTotals {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        let mut first = true;
        marshal_field(enc, &mut first, "requestCount", &self.request_count)?;
        marshal_field(
            enc,
            &mut first,
            "totalProcessingTimeMs",
            &self.total_processing_time_ms,
        )?;
        write_object_end(enc);
        Ok(())
    }
}

// Go: api/timing.go:33 serverTimingInfo
// serverTimingInfo is a point-in-time snapshot of collected server timing,
// returned to clients in response to a getServerTiming request.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ServerTimingInfo {
    // Enabled reports whether server-side timing collection is active.
    pub enabled: bool,
    // Totals are the running totals across every handled request.
    pub totals: ServerTimingTotals,
    // RecentRequests are the most recent requests, oldest to newest, up to
    // serverRecentRequestCapacity.
    pub recent_requests: Vec<ServerRequestTiming>,
}

impl MarshalerTo for ServerTimingInfo {
    fn marshal_json_to(&self, enc: &mut String) -> Result<(), JsonError> {
        write_object_start(enc);
        let mut first = true;
        marshal_field(enc, &mut first, "enabled", &self.enabled)?;
        marshal_field(enc, &mut first, "totals", &self.totals)?;
        marshal_field(enc, &mut first, "recentRequests", &self.recent_requests)?;
        write_object_end(enc);
        Ok(())
    }
}

// Go: api/timing.go:47 timingCollector
// timingCollector accumulates per-request server processing times into running
// totals and a fixed-size ring buffer of the most recent requests.
#[derive(Clone, Debug, Default)]
pub struct TimingCollector {
    totals: ServerTimingTotals,
    // ring holds up to serverRecentRequestCapacity entries; once full, head
    // marks the oldest entry.
    ring: Vec<ServerRequestTiming>,
    head: usize,
}

// Go: api/timing.go:56 newTimingCollector
pub fn new_timing_collector() -> TimingCollector {
    TimingCollector::default()
}

impl TimingCollector {
    // Go: api/timing.go:61 record
    // record adds a single request's processing time to the totals and ring buffer.
    pub fn record(&mut self, method: &str, d: Duration) {
        let processing_ms = duration_to_millis(d);

        self.totals.request_count += 1;
        self.totals.total_processing_time_ms += processing_ms;

        let entry = ServerRequestTiming {
            method: method.to_string(),
            processing_time_ms: processing_ms,
            timestamp: unix_milli_now(),
        };
        if self.ring.len() < SERVER_RECENT_REQUEST_CAPACITY {
            self.ring.push(entry);
        } else {
            self.ring[self.head] = entry;
            self.head = (self.head + 1) % SERVER_RECENT_REQUEST_CAPACITY;
        }
    }

    // Go: api/timing.go:85 snapshot
    // snapshot returns a copy of the currently collected timing information, with
    // recent requests ordered from oldest to newest.
    pub fn snapshot(&self) -> ServerTimingInfo {
        let mut recent = Vec::with_capacity(self.ring.len());
        for i in 0..self.ring.len() {
            recent.push(self.ring[(self.head + i) % self.ring.len()].clone());
        }
        ServerTimingInfo {
            enabled: true,
            totals: self.totals.clone(),
            recent_requests: recent,
        }
    }

    // Go: api/timing.go:101 reset
    // reset clears all accumulated totals and recent-request history.
    pub fn reset(&mut self) {
        self.totals = ServerTimingTotals::default();
        self.ring = Vec::new();
        self.head = 0;
    }
}

// Go: api/timing.go:112 serverTimingSnapshot
// serverTimingSnapshot returns the collector's snapshot, or a disabled snapshot
// when timing collection is not enabled (collector is nil).
pub fn server_timing_snapshot(c: Option<&TimingCollector>) -> ServerTimingInfo {
    let Some(c) = c else {
        return disabled_server_timing_info();
    };
    c.snapshot()
}

// Go: api/timing.go:121 disabledServerTimingInfo
// disabledServerTimingInfo is the snapshot returned when timing collection is
// not enabled.
pub fn disabled_server_timing_info() -> ServerTimingInfo {
    ServerTimingInfo {
        enabled: false,
        totals: ServerTimingTotals::default(),
        recent_requests: Vec::new(),
    }
}

// Go: api/timing.go:131 durationToMillis
// durationToMillis converts a duration to fractional milliseconds, clamped to be
// non-negative. It preserves sub-microsecond precision by converting from the
// full nanosecond duration.
// PORT: Go `time.Duration` is signed; a `Duration` is never negative, so the
// clamp has no case here. Go `float64(d)` converts the int64 nanoseconds.
#[allow(clippy::cast_possible_truncation, clippy::cast_precision_loss)]
pub fn duration_to_millis(d: Duration) -> f64 {
    d.as_nanos() as i64 as f64 / 1_000_000.0
}

/// Go `time.Now().UnixMilli()`.
#[allow(clippy::cast_possible_truncation, clippy::cast_possible_wrap)]
fn unix_milli_now() -> i64 {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(d) => d.as_millis() as i64,
        Err(err) => -(err.duration().as_millis() as i64),
    }
}
