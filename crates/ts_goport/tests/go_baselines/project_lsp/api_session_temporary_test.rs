//! Port of Go `internal/api/session_temporary_test.go` (tsgo#4642, with the
//! tsgo#4552 `Files` edit): `TestUpdateTemporarySnapshot`,
//! `TestUpdateTemporarySnapshotAddsUnopenedFile`,
//! `TestUpdateTemporarySnapshotRejectsUnsupportedExtension`,
//! `TestUpdateTemporarySnapshotUsesClientSnapshotAsBase`.
//!
//! PORT: the tests are in `project_lsp` because they use `projecttestutil`
//! and `child_test!`. Go `bundled.Embedded` is always true in the port, so
//! the skip is dropped. Go `defer projectSession.Close()` and
//! `defer session.Close()` are the two `close` calls at the end of each
//! test, in Go's defer order. Go `session.latestSnapshot` is the
//! `latest_snapshot` field.

use ts_goport::api::{
    self, DocumentIdentifier, GetDiagnosticsParams, ReleaseParams, UpdateSnapshotParams,
    UpdateTemporarySnapshotParams,
};
use ts_goport::gostd::GoError;
use ts_goport::lsp::lsproto;

use super::projecttestutil::{self, files};
use super::util::*;

/// Go `assert.NilError(t, err)` on a result.
fn nil_error<T>(result: Result<T, GoError>) -> T {
    result.unwrap_or_else(|err| panic!("unexpected error: {}", err.error()))
}

/// Go `DocumentIdentifier{FileName: name}`.
fn doc(name: &str) -> DocumentIdentifier {
    DocumentIdentifier {
        file_name: name.to_string(),
        ..Default::default()
    }
}

// Go: session_temporary_test.go:17 TestUpdateTemporarySnapshot
// TestUpdateTemporarySnapshot verifies that a temporary snapshot reflects an
// overridden file content, leaves the session's latest snapshot untouched, and
// does not disturb the original snapshot's view of the file.
child_test! {
    fn update_temporary_snapshot() {
        const FILE_NAME: &str = "/home/projects/p/src/index.ts";
        // Valid content: no type errors.
        const CONTENT: &str = "export const x: number = 1;";

        let (project_session, _) = projecttestutil::setup(files(&[
            (
                "/home/projects/p/tsconfig.json",
                r#"{ "compilerOptions": { "strict": true } }"#,
            ),
            (FILE_NAME, CONTENT),
        ]));
        let session = api::new_session(project_session.clone(), None);

        let ctx = bg();

        let base_resp = nil_error(session.handle_update_snapshot(
            &ctx,
            &UpdateSnapshotParams {
                open_files: vec![doc(FILE_NAME)],
                ..Default::default()
            },
        ));
        assert!(
            !base_resp.projects.is_empty(),
            "expected at least one project"
        );
        let project_id = base_resp.projects[0].id.clone();

        // The base snapshot should be the session's latest snapshot.
        let base_handle = base_resp.snapshot;
        assert_eq!(session.latest_snapshot.get(), base_handle);

        // Sanity: the original content type-checks cleanly.
        let base_diags = nil_error(session.handle_get_semantic_diagnostics(
            &ctx,
            &GetDiagnosticsParams {
                snapshot: base_handle,
                project: project_id.clone(),
                files: Some(vec![doc(FILE_NAME)]),
            },
        ));
        assert_eq!(
            base_diags.len(),
            0,
            "original content should have no semantic errors"
        );

        // Create a temporary snapshot whose content introduces a type error.
        const BAD_TEXT: &str = "export const x: string = 1;";
        let temp_resp = nil_error(session.handle_update_temporary_snapshot(
            &ctx,
            &UpdateTemporarySnapshotParams {
                snapshot: base_handle,
                file: doc(FILE_NAME),
                new_text: BAD_TEXT.to_string(),
            },
        ));
        assert!(
            temp_resp.snapshot != base_handle,
            "temporary snapshot should have a distinct handle"
        );

        // The temporary snapshot must NOT become the session's latest snapshot.
        assert_eq!(
            session.latest_snapshot.get(),
            base_handle,
            "latest snapshot must be unchanged by a temporary update"
        );

        // The temporary snapshot reflects the overridden content and reports the error.
        let temp_project_id = temp_resp.projects[0].id.clone();
        let temp_diags = nil_error(session.handle_get_semantic_diagnostics(
            &ctx,
            &GetDiagnosticsParams {
                snapshot: temp_resp.snapshot,
                project: temp_project_id,
                files: Some(vec![doc(FILE_NAME)]),
            },
        ));
        assert!(
            !temp_diags.is_empty(),
            "temporary content should have a semantic error"
        );

        // The original snapshot is unaffected: still no errors.
        let base_diags_again = nil_error(session.handle_get_semantic_diagnostics(
            &ctx,
            &GetDiagnosticsParams {
                snapshot: base_handle,
                project: project_id.clone(),
                files: Some(vec![doc(FILE_NAME)]),
            },
        ));
        assert_eq!(
            base_diags_again.len(),
            0,
            "original snapshot must be unaffected by the temporary update"
        );

        // Releasing the temporary snapshot cleans it up without affecting the base.
        nil_error(session.handle_release(
            &ctx,
            Some(&ReleaseParams {
                snapshot: temp_resp.snapshot,
            }),
        ));

        let base_diags_final = nil_error(session.handle_get_semantic_diagnostics(
            &ctx,
            &GetDiagnosticsParams {
                snapshot: base_handle,
                project: project_id,
                files: Some(vec![doc(FILE_NAME)]),
            },
        ));
        assert_eq!(
            base_diags_final.len(),
            0,
            "base snapshot should remain valid after releasing the temporary snapshot"
        );

        session.close();
        project_session.close();
    }
}

// Go: session_temporary_test.go:103 TestUpdateTemporarySnapshotAddsUnopenedFile
child_test! {
    fn update_temporary_snapshot_adds_unopened_file() {
        const EXISTING_FILE_NAME: &str = "/home/projects/p/src/index.ts";
        const TEMPORARY_FILE_NAME: &str = "/home/projects/p/src/temporary.ts";
        let (project_session, _) = projecttestutil::setup(files(&[
            (
                "/home/projects/p/tsconfig.json",
                r#"{ "include": ["src/**/*.ts"] }"#,
            ),
            (EXISTING_FILE_NAME, "export const existing = 1;"),
        ]));
        let session = api::new_session(project_session.clone(), None);

        let ctx = bg();
        let base_resp = nil_error(session.handle_update_snapshot(
            &ctx,
            &UpdateSnapshotParams {
                open_files: vec![doc(EXISTING_FILE_NAME)],
                ..Default::default()
            },
        ));
        assert_eq!(base_resp.projects.len(), 1);
        assert!(
            !base_resp.projects[0]
                .root_files
                .iter()
                .any(|f| f == TEMPORARY_FILE_NAME)
        );

        let temp_resp = nil_error(session.handle_update_temporary_snapshot(
            &ctx,
            &UpdateTemporarySnapshotParams {
                snapshot: base_resp.snapshot,
                file: doc(TEMPORARY_FILE_NAME),
                new_text: "export const temporary = 1;".to_string(),
            },
        ));
        assert_eq!(temp_resp.projects.len(), 1);
        assert!(
            temp_resp.projects[0]
                .root_files
                .iter()
                .any(|f| f == TEMPORARY_FILE_NAME),
            "temporary file should be included in the configured project"
        );
        assert!(
            !base_resp.projects[0]
                .root_files
                .iter()
                .any(|f| f == TEMPORARY_FILE_NAME),
            "base snapshot should remain unchanged"
        );

        nil_error(session.handle_release(
            &ctx,
            Some(&ReleaseParams {
                snapshot: temp_resp.snapshot,
            }),
        ));

        session.close();
        project_session.close();
    }
}

// Go: session_temporary_test.go:142 TestUpdateTemporarySnapshotRejectsUnsupportedExtension
child_test! {
    fn update_temporary_snapshot_rejects_unsupported_extension() {
        let (project_session, _) = projecttestutil::setup(files(&[]));
        let session = api::new_session(project_session.clone(), None);

        let ctx = bg();
        const FILE_NAME: &str = "/home/projects/p/src/temporary.custom";
        let base_resp = nil_error(session.handle_update_snapshot(
            &ctx,
            &UpdateSnapshotParams::default(),
        ));
        let err = session
            .handle_update_temporary_snapshot(
                &ctx,
                &UpdateTemporarySnapshotParams {
                    snapshot: base_resp.snapshot,
                    file: doc(FILE_NAME),
                    new_text: "export const temporary = 1;".to_string(),
                },
            )
            .err()
            .expect("expected an error");
        assert!(
            err.error().contains("unsupported file extension"),
            "expected error containing \"unsupported file extension\", got {:?}",
            err.error()
        );

        session.close();
        project_session.close();
    }
}

// Go: session_temporary_test.go:165 TestUpdateTemporarySnapshotUsesClientSnapshotAsBase
child_test! {
    fn update_temporary_snapshot_uses_client_snapshot_as_base() {
        const FILE_NAME: &str = "/home/projects/p/src/index.ts";
        const LATER_FILE_NAME: &str = "/home/projects/p/src/later.ts";
        let (project_session, _) = projecttestutil::setup(files(&[
            (
                "/home/projects/p/tsconfig.json",
                r#"{ "include": ["src/**/*.ts"] }"#,
            ),
            (FILE_NAME, "export const existing = 1;"),
        ]));
        let session = api::new_session(project_session.clone(), None);

        let ctx = bg();
        let base_resp = nil_error(session.handle_update_snapshot(
            &ctx,
            &UpdateSnapshotParams {
                open_files: vec![doc(FILE_NAME)],
                ..Default::default()
            },
        ));

        let later_uri = doc(LATER_FILE_NAME).to_uri(&project_session.get_current_directory());
        project_session.did_open_file(
            &ctx,
            &later_uri,
            1,
            "export const later = 1;",
            &lsproto::LanguageKind::TYPE_SCRIPT,
        );

        let temp_resp = nil_error(session.handle_update_temporary_snapshot(
            &ctx,
            &UpdateTemporarySnapshotParams {
                snapshot: base_resp.snapshot,
                file: doc(FILE_NAME),
                new_text: "export const existing = 2;".to_string(),
            },
        ));
        assert_eq!(temp_resp.projects.len(), 1);
        assert!(
            !temp_resp.projects[0]
                .root_files
                .iter()
                .any(|f| f == LATER_FILE_NAME),
            "temporary snapshot should not include files opened after the client snapshot"
        );

        nil_error(session.handle_release(
            &ctx,
            Some(&ReleaseParams {
                snapshot: temp_resp.snapshot,
            }),
        ));

        session.close();
        project_session.close();
    }
}
