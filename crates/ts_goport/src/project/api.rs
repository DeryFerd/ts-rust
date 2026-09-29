//! Go `internal/project/api.go`.
//!
//! PORT: the Go `snapshotUpdateMu` lock is dropped (one thread). These
//! methods are on `Session` (see session.rs) and take `self: &Rc<Self>`
//! because snapshot updates queue work that captures the session.

use crate::frontend::core_ext::get_script_kind_from_file_name;
use crate::project::prelude::*;

impl Session {
    // Go: project/api.go:19 APIUpdate
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

    // Go: project/api.go:41 APIUpdateTemporary
    // APIUpdateTemporary creates a snapshot that layers a temporary in-memory content
    // override for a file on top of baseSnapshot.
    // The caller must retain baseSnapshot for the duration of this call.
    // An error is returned if the file name does not have a recognized script extension.
    // On success, the returned snapshot carries a single reference (the clone ref);
    // the caller must call snapshot.Deref(s) when done.
    pub fn api_update_temporary(
        self: &Rc<Self>,
        ctx: &Context,
        base_snapshot: &Rc<Snapshot>,
        uri: &lsproto::DocumentUri,
        new_text: String,
    ) -> Result<Rc<Snapshot>, GoError> {
        let path = uri.path(base_snapshot.use_case_sensitive_file_names());

        let mut overlays = base_snapshot.fs.overlays.clone();
        let mut version: i32 = 0;
        let mut file_changes = FileChangeSummary::default();
        let existing = overlays.get(&path).cloned();
        let script_kind;
        if let Some(existing) = existing {
            version = existing.version() + 1;
            script_kind = existing.kind();
            file_changes.changed.insert(uri.clone());
        } else {
            script_kind = get_script_kind_from_file_name(&uri.file_name());
            if script_kind == ScriptKind::UNKNOWN {
                return Err(gostd::errors::errorf(
                    format!("unsupported file extension: {}", uri.file_name()),
                    vec![],
                ));
            }
            file_changes.opened = uri.clone();
        }
        overlays.insert(
            path,
            Rc::new(new_overlay(
                &uri.file_name(),
                new_text,
                version,
                script_kind,
            )),
        );

        let new_snapshot = Snapshot::clone_(
            base_snapshot,
            ctx,
            SnapshotChange {
                file_changes,
                resource_request: ResourceRequest {
                    documents: vec![uri.clone()],
                    ..Default::default()
                },
                ..Default::default()
            },
            &overlays,
            self,
        );
        Ok(new_snapshot)
    }
}
