//! Go `time.Timer`, `time.Ticker`, `time.AfterFunc` and `time.After`
//! (go1.26.8 `src/time/sleep.go`, `src/time/tick.go`) for `Send` data, with
//! the runtime timer rules of `src/runtime/time.go` (Go 1.23+ synchronous
//! timer channels: after `Stop` or `Reset` returns, no stale value is
//! received).
//!
//! PORT: the Go runtime keeps all timers in per-P heaps. Here each armed
//! timer has one waiting thread that exits when the timer is stopped or has
//! fired. Go `time.Time` is `Instant` and `time.Duration` is `Duration`
//! (never negative). Timers whose callback touches dispatch-thread state use
//! `gostd::local::after_func` instead.

use crate::prelude::*;

use std::sync::mpsc::{Receiver, SyncSender, TrySendError, sync_channel};
use std::sync::{Arc, Condvar, Mutex, MutexGuard};
use std::time::{Duration, Instant};

// PORT: Go stacks grow to 1 GB; the goroutine that runs an AfterFunc
// callback gets the same maximum stack as the crate's checker threads.
const GOROUTINE_STACK_SIZE: usize = 1 << 30;

// PORT: Go mutexes do not poison.
fn lock<T>(m: &Mutex<T>) -> MutexGuard<'_, T> {
    m.lock().unwrap_or_else(|e| e.into_inner())
}

/// The runtime timer behind a `Timer` or `Ticker` (Go `runtime.timer`).
struct TimerShared {
    state: Mutex<TimerState>,
    cond: Condvar,
    /// Go `t.f` and `t.arg`: `sendTime` on this channel, or `goFunc` of `f`.
    f: TimerFunc,
}

enum TimerFunc {
    /// Go `sendTime` on the timer channel (`t.isChan`).
    SendTime(SyncSender<Instant>),
    /// Go `goFunc`: start `f` in its own goroutine.
    GoFunc(Arc<Mutex<Box<dyn FnMut() + Send>>>),
}

struct TimerState {
    /// Go `t.when`; `None` is Go `0` (not armed).
    when: Option<Instant>,
    /// Go `t.period`; zero for a one-shot timer.
    period: Duration,
    /// Whether a thread is waiting for `when`.
    thread_running: bool,
}

impl TimerShared {
    fn is_chan(&self) -> bool {
        matches!(self.f, TimerFunc::SendTime(_))
    }
}

// Go: time/sleep.go:52 when
/// when is a helper function for setting the 'when' field of a runtimeTimer.
/// It returns what the time will be, in nanoseconds, Duration d in the future.
/// If d is negative, it is ignored. If the returned value would be less than
/// zero because of an overflow, MaxInt64 is returned.
fn when(d: Duration) -> Instant {
    let now = Instant::now();
    if d.is_zero() {
        return now;
    }
    match now.checked_add(d) {
        Some(t) => t,
        None => max_when(now),
    }
}

// PORT: Go clamps to MaxInt64 nanoseconds (about 292 years). This returns
// the latest Instant up to that distance that the platform can hold.
fn max_when(now: Instant) -> Instant {
    let mut d = Duration::from_nanos(i64::MAX as u64);
    loop {
        if let Some(t) = now.checked_add(d) {
            return t;
        }
        d /= 2;
    }
}

// Go: time/sleep.go:72 newTimer
fn new_timer(when: Instant, period: Duration, f: TimerFunc) -> Arc<TimerShared> {
    let t = Arc::new(TimerShared {
        state: Mutex::new(TimerState {
            when: None,
            period,
            thread_running: false,
        }),
        cond: Condvar::new(),
        f,
    });
    {
        let mut state = lock(&t.state);
        state.when = Some(when);
        maybe_add(&t, &mut state);
    }
    t
}

// Go: runtime/time.go maybeAdd
// PORT: start the waiting thread when none is running.
fn maybe_add(t: &Arc<TimerShared>, state: &mut TimerState) {
    if state.thread_running {
        t.cond.notify_all();
        return;
    }
    state.thread_running = true;
    let t = t.clone();
    std::thread::Builder::new()
        .name("timer".to_string())
        .spawn(move || run_timer(t))
        .expect("time: failed to start the timer thread");
}

// Go: runtime/time.go unlockAndRun
// PORT: the waiting thread of one timer. It fires the timer when `when`
// passes and exits once the timer is stopped or a one-shot timer fired.
fn run_timer(t: Arc<TimerShared>) {
    let mut state = lock(&t.state);
    loop {
        let Some(w) = state.when else {
            state.thread_running = false;
            return;
        };
        let now = Instant::now();
        if now < w {
            state = t
                .cond
                .wait_timeout(state, w - now)
                .unwrap_or_else(|e| e.into_inner())
                .0;
            continue;
        }
        let delay = now - w;
        if !state.period.is_zero() {
            // Leave in heap but adjust next time to fire.
            let period = state.period.as_nanos();
            let steps = 1 + delay.as_nanos() / period;
            let next = u64::try_from(period * steps)
                .ok()
                .and_then(|n| w.checked_add(Duration::from_nanos(n)));
            state.when = Some(next.unwrap_or_else(|| max_when(w)));
        } else {
            // Remove from heap.
            state.when = None;
        }
        match &t.f {
            // Go: time/sleep.go:180 sendTime
            // sendTime does a non-blocking send of the current time on c.
            // PORT: Go sends `Now().Add(-delta)`, the time the timer was due.
            TimerFunc::SendTime(c) => {
                if let Err(TrySendError::Disconnected(_)) = c.try_send(w) {
                    // PORT: nobody can receive from C any more (Go would
                    // have collected the timer); stop it so the thread ends.
                    state.when = None;
                }
            }
            // Go: time/sleep.go:214 goFunc
            TimerFunc::GoFunc(f) => {
                let f = f.clone();
                std::thread::Builder::new()
                    .name("goroutine".to_string())
                    .stack_size(GOROUTINE_STACK_SIZE)
                    .spawn(move || {
                        // PORT: Go may run two calls of f at once after a
                        // Reset; here they take turns.
                        let mut f = lock(&f);
                        (*f)();
                    })
                    .expect("time: failed to start a goroutine");
            }
        }
    }
}

// Go: time/sleep.go:75 stopTimer
// Go: runtime/time.go stop
fn stop_timer(t: &Arc<TimerShared>, c: Option<&Receiver<Instant>>) -> bool {
    let mut pending;
    {
        let mut state = lock(&t.state);
        pending = state.when.is_some();
        state.when = None;
        t.cond.notify_all();
    }
    if t.is_chan() {
        // Stop any future sends with stale values.
        if let Some(c) = c {
            if c.try_recv().is_ok() {
                pending = true;
            }
        }
    }
    pending
}

// Go: time/sleep.go:78 resetTimer
// Go: runtime/time.go modify
fn reset_timer(
    t: &Arc<TimerShared>,
    c: Option<&Receiver<Instant>>,
    when: Instant,
    period: Duration,
) -> bool {
    let mut pending;
    {
        let mut state = lock(&t.state);
        state.period = period;
        pending = state.when.is_some();
        state.when = Some(when);
        if t.is_chan() {
            if let Some(c) = c {
                if c.try_recv().is_ok() {
                    pending = true;
                }
            }
        }
        maybe_add(t, &mut state);
    }
    pending
}

// Go: time/sleep.go:89 Timer
/// The Timer type represents a single event. When the Timer expires, the
/// current time will be sent on C, unless the Timer was created by
/// [AfterFunc].
pub struct Timer {
    /// Go `C`.
    /// PORT: Go leaves C nil for an AfterFunc timer; here it is a channel
    /// that never receives a value, which behaves the same.
    pub c: Receiver<Instant>,
    r: Arc<TimerShared>,
    /// The sender of the unused C of an AfterFunc timer, kept so that C
    /// blocks instead of reporting a closed channel.
    nil_c: Option<SyncSender<Instant>>,
}

impl Timer {
    // Go: time/sleep.go:143 NewTimer
    /// NewTimer creates a new Timer that will send
    /// the current time on its channel after at least duration d.
    pub fn new(d: Duration) -> Timer {
        let (tx, c) = sync_channel(1);
        let r = new_timer(when(d), Duration::ZERO, TimerFunc::SendTime(tx));
        Timer { c, r, nil_c: None }
    }

    // Go: time/sleep.go:113 Stop
    /// Stop prevents the [Timer] from firing.
    /// It returns true if the call stops the timer, false if the timer has already
    /// expired or been stopped.
    ///
    /// For a func-based timer created with [AfterFunc](d, f),
    /// if t.Stop returns false, then the timer has already expired
    /// and the function f has been started in its own goroutine;
    /// Stop does not wait for f to complete before returning.
    ///
    /// For a chan-based timer created with NewTimer(d), any receive from t.C
    /// after Stop has returned is guaranteed to block rather than receive a
    /// stale time value from before the Stop.
    pub fn stop(&self) -> bool {
        stop_timer(&self.r, Some(&self.c))
    }

    // Go: time/sleep.go:171 Reset
    /// Reset changes the timer to expire after duration d.
    /// It returns true if the timer had been active, false if the timer had
    /// expired or been stopped.
    ///
    /// For a func-based timer created with [AfterFunc](d, f), Reset either reschedules
    /// when f will run, in which case Reset returns true, or schedules f
    /// to run again, in which case it returns false.
    pub fn reset(&self, d: Duration) -> bool {
        let w = when(d);
        reset_timer(&self.r, Some(&self.c), w, Duration::ZERO)
    }
}

impl std::fmt::Debug for Timer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Timer(when: {:?})", lock(&self.r.state).when)
    }
}

// Go: time/sleep.go:202 After
/// After waits for the duration to elapse and then sends the current time
/// on the returned channel.
/// It is equivalent to [NewTimer](d).C.
pub fn after(d: Duration) -> Receiver<Instant> {
    Timer::new(d).c
}

// Go: time/sleep.go:210 AfterFunc
/// AfterFunc waits for the duration to elapse and then calls f
/// in its own goroutine. It returns a [Timer] that can
/// be used to cancel the call using its Stop method.
/// The returned Timer's C field is not used and will be nil.
///
/// PORT: `f` runs on a new thread each time the timer fires (it fires again
/// after a `reset`), so it is `FnMut + Send`.
pub fn after_func<F: FnMut() + Send + 'static>(d: Duration, f: F) -> Timer {
    let (tx, c) = sync_channel(1);
    let r = new_timer(
        when(d),
        Duration::ZERO,
        TimerFunc::GoFunc(Arc::new(Mutex::new(Box::new(f)))),
    );
    Timer {
        c,
        r,
        nil_c: Some(tx),
    }
}

// Go: time/tick.go:16 Ticker
/// A Ticker holds a channel that delivers “ticks” of a clock
/// at intervals.
pub struct Ticker {
    /// Go `C`: the channel on which the ticks are delivered.
    pub c: Receiver<Instant>,
    r: Arc<TimerShared>,
}

impl Ticker {
    // Go: time/tick.go:36 NewTicker
    /// NewTicker returns a new [Ticker] containing a channel that will send
    /// the current time on the channel after each tick. The period of the
    /// ticks is specified by the duration argument. The ticker will adjust
    /// the time interval or drop ticks to make up for slow receivers.
    /// The duration d must be greater than zero; if not, NewTicker will
    /// panic.
    pub fn new(d: Duration) -> Ticker {
        if d.is_zero() {
            panic!("non-positive interval for NewTicker");
        }
        // Give the channel a 1-element time buffer.
        // If the client falls behind while reading, we drop ticks
        // on the floor until the client catches up.
        let (tx, c) = sync_channel(1);
        let r = new_timer(when(d), d, TimerFunc::SendTime(tx));
        Ticker { c, r }
    }

    // Go: time/tick.go:52 Stop
    /// Stop turns off a ticker. After Stop, no more ticks will be sent.
    /// Stop does not close the channel, to prevent a concurrent goroutine
    /// reading from the channel from seeing an erroneous "tick".
    pub fn stop(&self) {
        stop_timer(&self.r, Some(&self.c));
    }

    // Go: time/tick.go:65 Reset
    /// Reset stops a ticker and resets its period to the specified duration.
    /// The next tick will arrive after the new period elapses. The duration d
    /// must be greater than zero; if not, Reset will panic.
    pub fn reset(&self, d: Duration) {
        if d.is_zero() {
            panic!("non-positive interval for Ticker.Reset");
        }
        reset_timer(&self.r, Some(&self.c), when(d), d);
    }
}

impl std::fmt::Debug for Ticker {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let state = lock(&self.r.state);
        write!(
            f,
            "Ticker(when: {:?}, period: {:?})",
            state.when, state.period
        )
    }
}

// Go: time/tick.go:86 Tick
/// Tick is a convenience wrapper for [NewTicker] providing access to the
/// ticking channel only. Unlike NewTicker, Tick will return nil if d <= 0.
///
/// PORT: Go returns a nil channel for d <= 0; the port returns `None`.
pub fn tick(d: Duration) -> Option<Receiver<Instant>> {
    if d.is_zero() {
        return None;
    }
    Some(Ticker::new(d).c)
}
