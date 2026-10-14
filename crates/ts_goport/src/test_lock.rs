//! Test builds only: one thread at a time builds node stores.
//!
//! A thread builds its node stores at the file ids after the published ones
//! (`ast/store.rs` `BuildStores`). When another thread publishes while it
//! builds, that publish takes the same ids, and the build panics ("another
//! thread published ..."). The loader never builds on two threads at once,
//! but the lib tests run on parallel test threads, and each loads programs
//! or parses files. So in a test build a thread takes this lock with its
//! first build store (`BuildStores::next_id`) and gives it back when it
//! publishes (`publish_file_stores`) or ends. A thread that builds stores
//! and never publishes them holds the lock until it ends.
//!
//! A test that needs more (no other publish or pin release while it runs)
//! holds the lock to its end (`hold`). A pin release of another thread
//! waits for it (`pin_release`).

use std::cell::{Cell, RefCell};
use std::sync::{Condvar, Mutex, PoisonError};
use std::time::Duration;

/// True while a thread holds the lock.
static TAKEN: Mutex<bool> = Mutex::new(false);
/// Notified when the lock is given back.
static FREED: Condvar = Condvar::new();

/// How long a thread waits for the lock before it panics. The whole lib
/// runs in about 11 s on one test thread, so a longer wait is a test that
/// waits for a thread that waits for the lock.
const WAIT_LIMIT: Duration = Duration::from_secs(120);

/// The lock, taken. Its drop gives the lock back, so a thread that ends
/// with build stores does not keep it.
pub(crate) struct Held;

impl Drop for Held {
    fn drop(&mut self) {
        *TAKEN.lock().unwrap_or_else(PoisonError::into_inner) = false;
        FREED.notify_one();
    }
}

thread_local! {
    /// The lock of this thread, while it builds stores or `hold`s it.
    static HELD: RefCell<Option<Held>> = const { RefCell::new(None) };
    /// Set by `hold`: a publish does not give the lock back.
    static KEEP: Cell<bool> = const { Cell::new(false) };
}

/// Waits until no thread holds the lock, and takes it.
fn take() -> Held {
    let taken = TAKEN.lock().unwrap_or_else(PoisonError::into_inner);
    let (mut taken, wait) = FREED
        .wait_timeout_while(taken, WAIT_LIMIT, |taken| *taken)
        .unwrap_or_else(PoisonError::into_inner);
    assert!(
        !wait.timed_out(),
        "waited {WAIT_LIMIT:?} for the store build lock: does a test wait for a thread that builds stores or releases pins?"
    );
    *taken = true;
    Held
}

/// True when this thread holds the lock. `try_with`: false while the
/// thread-locals of this thread drop.
fn holds() -> bool {
    HELD.try_with(|held| held.borrow().is_some())
        .unwrap_or(false)
}

/// Takes the lock for this thread, unless it holds it already. Called
/// before the first build store of a thread gets its id.
pub(crate) fn begin_build() {
    if !holds() {
        let held = take();
        HELD.with(|slot| *slot.borrow_mut() = Some(held));
    }
}

/// Takes the lock for this thread and keeps it until the thread ends. For a
/// test that reads process state of the store registry past one build: the
/// published count, the block pool, file version deaths, the pin epoch or
/// the free thread. Its other threads must not build stores or release
/// pins.
pub(crate) fn hold() {
    begin_build();
    KEEP.set(true);
}

/// Called by a pin release (`file_version::take_file_version_pins`), which
/// raises the pin epoch of every thread: it waits while another thread
/// holds the lock, and the lock goes back when the value drops. `None`
/// when this thread holds the lock.
pub(crate) fn pin_release() -> Option<Held> {
    (!holds()).then(take)
}

/// Gives the lock back when it drops, if this thread holds it and does not
/// `hold` it. A publish makes one first, so the lock goes back after the
/// whole publish, also when the publish panics.
pub(crate) struct BuildEnd;

impl Drop for BuildEnd {
    fn drop(&mut self) {
        // `try_with`: a publish while the thread-locals of this thread drop
        // finds no lock to give back.
        if !KEEP.try_with(Cell::get).unwrap_or(true) {
            let _ = HELD.try_with(|held| held.borrow_mut().take());
        }
    }
}
