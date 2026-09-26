//! Go `internal/project/api.go`.
//!
//! PORT: the Go `snapshotUpdateMu` lock is dropped (one thread). These
//! methods are on `Session` (see session.rs) and take `self: &Rc<Self>`
//! because snapshot updates queue work that captures the session.

use crate::project::prelude::*;

impl Session {
    // Go: project/api.go:11 APIOpenProject
    // APIOpenProject opens a project and returns a ref'd snapshot.
    // The caller must call snapshot.Deref(s) when done.
    // PORT: Go returns `(*Project, *Snapshot, error)` and returns the ref'd
    // snapshot also with an error, so the caller can Deref it. The port
    // keeps the three values: the snapshot is never nil, the project is
    // `None` and the error `Some` on failure.
    pub fn api_open_project(
        self: &Rc<Self>,
        ctx: &Context,
        config_file_name: &str,
        api_file_changes: &FileChangeSummary,
    ) -> (Option<Rc<RefCell<Project>>>, Rc<Snapshot>, Option<GoError>) {
        self.cancel_scheduled_snapshot_update();

        let (mut file_changes, overlays, ata_changes, _) = self.flush_changes(ctx);
        merge_file_change_summary(&mut file_changes, api_file_changes);
        let new_snapshot = self.update_snapshot_ref(
            ctx,
            overlays,
            SnapshotChange {
                file_changes,
                ata_changes,
                api_request: Some(APISnapshotRequest {
                    open_projects: Some(
                        [config_file_name.to_string()]
                            .into_iter()
                            .collect::<FxHashSet<String>>(),
                    ),
                    ..Default::default()
                }),
                ..Default::default()
            },
        );

        if let Some(api_error) = new_snapshot.api_error.clone() {
            return (None, new_snapshot, Some(api_error));
        }

        let project = new_snapshot
            .project_collection
            .configured_project(&(self.to_path)(config_file_name));
        if project.is_none() {
            panic!("OpenProject request returned no error but project not present in snapshot");
        }

        (project, new_snapshot, None)
    }

    // Go: project/api.go:40 APIUpdateWithFileChanges
    // APIUpdateWithFileChanges creates a new snapshot incorporating the given
    // file changes. Returns a ref'd snapshot; caller must Deref when done.
    pub fn api_update_with_file_changes(
        self: &Rc<Self>,
        ctx: &Context,
        api_file_changes: &FileChangeSummary,
    ) -> Rc<Snapshot> {
        self.cancel_scheduled_snapshot_update();

        let (mut file_changes, overlays, ata_changes, _) = self.flush_changes(ctx);
        merge_file_change_summary(&mut file_changes, api_file_changes);

        self.update_snapshot_ref(
            ctx,
            overlays,
            SnapshotChange {
                api_request: Some(APISnapshotRequest::default()),
                file_changes,
                ata_changes,
                ..Default::default()
            },
        )
    }
}
