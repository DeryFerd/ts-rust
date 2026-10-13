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
//! and never publishes them holds the lock until it ends. A test that needs
//! more (no other publish, file version or block pool change while it
//! runs) holds the lock to its end (`hold`).

use std::cell::{Cell, RefCell};
use std::sync::{Condvar, Mutex, PoisonError};
use std::time::Duration;

/// True while a thread holds the lock.
static TAKEN: Mutex<bool> = Mutex::new(false);
/// Notified when the lock is given back.
static FREED: Condvar = Condvar::new();

/// How long a thread waits for the lock before it panics. The whole lib
/// runs in about 11 s on one test thread, so a longer wait is a test that
/// builds stores on a second thread while its first thread holds the lock.
const WAIT_LIMIT: Duration = Duration::from_secs(120);

/// The lock of this thread. Its drop gives the lock back, so a thread that
/// ends with build stores does not keep it.
struct Held;

impl Drop for Held {
    fn drop(&mut self) {
        *TAKEN.lock().unwrap_or_else(PoisonError::into_inner) = false;
        FREED.notify_one();
    }
}

thread_local! {
    static HELD: RefCell<Option<Held>> = const { RefCell::new(None) };
    /// Set by `hold`: a publish does not give the lock back.
    static KEEP: Cell<bool> = const { Cell::new(false) };
}

/// Takes the lock for this thread, unless it holds it already. Called
/// before the first build store of a thread gets its id.
pub(crate) fn begin_build() {
    if HELD.with(|held| held.borrow().is_some()) {
        return;
    }
    let taken = TAKEN.lock().unwrap_or_else(PoisonError::into_inner);
    let (mut taken, wait) = FREED
        .wait_timeout_while(taken, WAIT_LIMIT, |taken| *taken)
        .unwrap_or_else(PoisonError::into_inner);
    assert!(
        !wait.timed_out(),
        "waited {WAIT_LIMIT:?} for the store build lock: does a test build stores on two threads at once?"
    );
    *taken = true;
    drop(taken);
    HELD.with(|held| *held.borrow_mut() = Some(Held));
}

/// Takes the lock for this thread and keeps it until the thread ends. For a
/// test that reads or changes process state of the store registry beyond
/// one build: the published count, file versions and their deaths, pin
/// releases or the block pool. Its other threads must not build stores.
pub(crate) fn hold() {
    begin_build();
    KEEP.set(true);
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
