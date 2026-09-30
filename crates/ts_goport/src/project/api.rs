//! Go `internal/project/api.go`.
//!
//! PORT: the Go `snapshotUpdateMu` lock is dropped (one thread). These
//! methods are on `Session` (see session.rs) and take `self: &Rc<Self>`
//! because snapshot updates queue work that captures the session.

use crate::project::prelude::*;

impl Session {
    // Go: project/api.go:25 APIUpdate
    // APIUpdate creates a new snapshot incorporating the given file changes and the
    // supplied API open/close request. The apiRequest may open or close projects and
    // files; opens are tracked in the snapshot (ref-counted) so they persist across
    // future updates, and closes release a previously taken ref. Programs are updated
    // only when explicitly requested by an open or ensure operation.
    // On success, returns a ref'd snapshot which the caller must Deref when done.
    // On failure, releases the rejected snapshot and returns nil and the error.
    // A snapshot with an API error is never adopted as canonical session state;
    // host changes flushed alongside it are adopted separately.
    // PORT: Go `(*Snapshot, error)` with a nil snapshot on error is a
    // `Result` (ts#64204). Go `*APISnapshotRequest` is
    // `Option<APISnapshotRequest>` (nil is `None`).
    pub fn api_update(
        self: &Rc<Self>,
        ctx: &Context,
        api_file_changes: &FileChangeSummary,
        api_request: Option<APISnapshotRequest>,
    ) -> Result<Rc<Snapshot>, GoError> {
        self.cancel_scheduled_snapshot_update();

        let (host_file_changes, overlays, ata_changes, _) = self.flush_changes(ctx);
        // Go: hostFileChanges.Clone()
        let mut file_changes = host_file_changes.clone();
        merge_file_change_summary(&mut file_changes, api_file_changes);
        // ts#64115
        let mut fs: Option<Rc<dyn vfs::Fs>> = None;
        let mut replace_file_system = false;
        if let Some(api_request) = &api_request {
            fs = api_request.file_system.clone();
            replace_file_system = api_request.replace_file_system;
        }

        let new_snapshot = self.update_snapshot_ref(
            ctx,
            overlays.clone(),
            SnapshotChange {
                api_request,
                file_system_override: fs.is_some(),
                fs,
                replace_file_system,
                file_changes,
                ata_changes: ata_changes.clone(),
                ..Default::default()
            },
        );
        // ts#64204
        if let Some(api_error) = new_snapshot.api_error.clone() {
            new_snapshot.deref();
            if !host_file_changes.is_empty() || !ata_changes.is_empty() {
                // The API request is rejected as a unit, but host changes were already
                // flushed and must still advance the canonical session snapshot.
                self.update_snapshot_exported(
                    ctx,
                    overlays,
                    SnapshotChange {
                        file_changes: host_file_changes,
                        ata_changes,
                        ..Default::default()
                    },
                );
            }
            return Err(api_error);
        }
        Ok(new_snapshot)
    }

    // Go: project/api.go:30 TryAdoptSnapshotInBackground (ts#64163)
    // TryAdoptSnapshotInBackground retains a derived snapshot and attempts to adopt it
    // as the session's current snapshot without blocking the caller.
    pub fn try_adopt_snapshot_in_background(
        self: &Rc<Self>,
        base_snapshot: &Rc<Snapshot>,
        new_snapshot: &Rc<Snapshot>,
    ) {
        self.retain_snapshot(new_snapshot);
        self.try_adopt_snapshot_change_in_background(base_snapshot, new_snapshot);
    }
}
