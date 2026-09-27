//! Port of Go `internal/project/watchtimeout_test.go`.
//!
//! PORT: Go runs the test in a `synctest` bubble with fake time. The port
//! uses real time: the slow client waits for its call context (the 1 s
//! `watchRequestTimeout`) to end. `synctest.Wait()` and the fake sleeps
//! are `session.wait_for_background_tasks()`, which runs the queued
//! background tasks (the Rust session runs them on this thread).

use std::cell::{Cell, RefCell};
use std::collections::HashSet;
use std::rc::Rc;
use std::time::Duration;

use ts_goport::project::{self, WatcherID};

use super::projecttestutil::{self, TypingsInstallerOptions, files};
use super::util::*;

child_test! {
    // Go: watchtimeout_test.go:31 TestUpdateWatchTimeoutAndRollback/watch retries on next snapshot update after timeout with same watcher identity
    fn watch_retries_on_next_snapshot_update_after_timeout_with_same_watcher_identity() {
        let files = files(&[
            (
                "/home/projects/TS/p1/tsconfig.json",
                r#"{
			"compilerOptions": { "noLib": true, "strict": true }
		}"#,
            ),
            ("/home/projects/TS/p1/src/index.ts", "export const x = 1;"),
        ]);
        let (init, utils) =
            projecttestutil::get_session_init_options(files, None, TypingsInstallerOptions::default());

        // Track WatchFiles calls: record which watcher IDs were attempted
        // and which succeeded.
        let attempted_ids: Rc<RefCell<Vec<WatcherID>>> = Rc::default();
        let successful_ids: Rc<RefCell<Vec<WatcherID>>> = Rc::default();
        let first_batch_done = Rc::new(Cell::new(false));
        {
            let attempted_ids = attempted_ids.clone();
            let successful_ids = successful_ids.clone();
            let first_batch_done = first_batch_done.clone();
            *utils.client().watch_files_func.borrow_mut() = Some(Box::new(move |ctx, id, _watchers| {
                attempted_ids.borrow_mut().push(id.clone());
                if !first_batch_done.get() {
                    // Block until the context times out to simulate a slow client.
                    loop {
                        if let Some(err) = ctx.err() {
                            return Err(err);
                        }
                        std::thread::sleep(Duration::from_millis(5));
                    }
                }
                // After the first batch, succeed immediately.
                successful_ids.borrow_mut().push(id.clone());
                Ok(())
            }));
        }

        let session = project::new_session(&init);

        let u = "file:///home/projects/TS/p1/src/index.ts";

        // Step 1: Open the file. This creates the project and triggers
        // updateWatches. All WatchFiles calls block and time out because
        // the client is slow, so the registry is rolled back and the
        // watchers are marked as pending.
        open(&session, u, "export const x = 1;");

        session.wait_for_background_tasks();

        let first_attempt_ids = attempted_ids.borrow().clone();
        assert!(
            !first_attempt_ids.is_empty(),
            "expected at least one WatchFiles call during initial open, got {}",
            first_attempt_ids.len()
        );

        // No watcher IDs should have succeeded.
        assert_eq!(successful_ids.borrow().len(), 0, "expected no successful watches after timeout");

        // Step 2: Allow subsequent WatchFiles calls to succeed.
        first_batch_done.set(true);

        // Step 3: Make a single character change to the open file.
        edit(&session, u, 2, (0, 18), (0, 19), "2");

        // Step 4: Flush the pending change by requesting the language service.
        let _ = language_service(&session, u);

        // Let the background task run updateWatches.
        session.wait_for_background_tasks();

        // Verify: WatchFiles was called again with the same watcher IDs,
        // and this time the calls succeeded.
        let attempted = attempted_ids.borrow().clone();
        let retry_ids = &attempted[first_attempt_ids.len()..];
        assert!(
            !retry_ids.is_empty(),
            "expected WatchFiles to be retried after character change, got {} new calls (total {}, first batch {})",
            retry_ids.len(),
            attempted.len(),
            first_attempt_ids.len()
        );

        // Verify that the retry used the same watcher IDs as the first attempt.
        let first_attempt_set: HashSet<String> = first_attempt_ids.iter().map(|id| id.0.clone()).collect();
        let retry_set: HashSet<String> = retry_ids.iter().map(|id| id.0.clone()).collect();
        for id in &retry_set {
            assert!(
                first_attempt_set.contains(id),
                "retry watcher ID {id} was not in the first attempt; first attempt IDs={first_attempt_set:?} retry IDs={retry_set:?}"
            );
        }

        // Verify at least one retried watcher succeeded.
        let successful_retried_count = successful_ids
            .borrow()
            .iter()
            .filter(|id| retry_set.contains(&id.0))
            .count();
        assert!(
            successful_retried_count >= 1,
            "expected at least one retried watcher to succeed, got {successful_retried_count}"
        );
        session.close();
    }
}
