//! Go `internal/project/api.go`.
//!
//! PORT: the Go `snapshotUpdateMu` lock is dropped (one thread). These
//! methods are on `Session` (see session.rs) and take `self: &Rc<Self>`
//! because snapshot updates queue work that captures the session.

use crate::project::prelude::*;

impl Session {
    // Go: project/api.go:14 APIUpdate
    // APIUpdate creates a new snapshot incorporating the given file changes and the
    // supplied API open/close request. The apiRequest may open or close projects and
    // files; opens are tracked in the snapshot (ref-counted) so they persist across
    // future updates, and closes release a previously taken ref. Even an empty
    // apiRequest ensures all API-opened projects and files are kept up to date.
    // Returns a ref'd snapshot (which the caller must Deref when done) and any error
    // encountered while applying the request, e.g. failing to load a project to open.
    // PORT: Go returns `(*Snapshot, error)` and returns the ref'd snapshot also
    // with an error, so the caller can Deref it. The port returns both values.
    pub fn api_update(
        self: &Rc<Self>,
        ctx: &Context,
        api_file_changes: &FileChangeSummary,
        api_request: APISnapshotRequest,
    ) -> (Rc<Snapshot>, Option<GoError>) {
        self.cancel_scheduled_snapshot_update();

        let (mut file_changes, overlays, ata_changes, _) = self.flush_changes(ctx);
        merge_file_change_summary(&mut file_changes, api_file_changes);

        let new_snapshot = self.update_snapshot_ref(
            ctx,
            overlays,
            SnapshotChange {
                api_request: Some(api_request),
                file_changes,
                ata_changes,
                ..Default::default()
            },
        );
        let api_error = new_snapshot.api_error.clone();
        (new_snapshot, api_error)
    }
}
