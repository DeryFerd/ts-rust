//! Port of Go `internal/api/session_apistate_test.go`
//! (`TestSessionTracksAndReleasesAPIRefs`,
//! `TestUpdateSnapshotResponseSkipsUnloadedAncestorProject`).
//!
//! PORT: the tests are in `project_lsp` because they use `projecttestutil`
//! and `child_test!`. Go `bundled.Embedded` is always true in the port, so
//! the skip is dropped. Go `session.openProjects` and `session.openFiles`
//! are the `open_projects` and `open_files` fields.

use ts_goport::api::{
    self, DocumentIdentifier, GetDefaultProjectForFileParams, UpdateSnapshotParams,
};
use ts_goport::gostd::GoError;

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

// Go: session_apistate_test.go:24 TestSessionTracksAndReleasesAPIRefs/project opens are idempotent and released on close
child_test! {
    fn project_opens_are_idempotent_and_released_on_close() {
        const CONFIG_FILE_NAME: &str = "/home/projects/p/tsconfig.json";
        let (project_session, _) = projecttestutil::setup(files(&[
            (CONFIG_FILE_NAME, r#"{ "compilerOptions": { "strict": true } }"#),
            ("/home/projects/p/src/index.ts", "export const x = 1;"),
        ]));
        let session = api::new_session(project_session.clone(), None);

        nil_error(session.handle_update_snapshot(
            &bg(),
            &UpdateSnapshotParams {
                open_projects: vec![doc(CONFIG_FILE_NAME)],
                ..Default::default()
            },
        ));
        assert_eq!(session.open_projects.borrow().len(), 1);

        // Opening the same project again must not take an additional ref.
        nil_error(session.handle_update_snapshot(
            &bg(),
            &UpdateSnapshotParams {
                open_projects: vec![doc(CONFIG_FILE_NAME)],
                ..Default::default()
            },
        ));
        assert_eq!(session.open_projects.borrow().len(), 1);

        assert!(has_configured_project(&project_session, CONFIG_FILE_NAME));

        // Closing the session releases the single API ref, so the project is no
        // longer kept loaded.
        session.close();
        assert_eq!(session.open_projects.borrow().len(), 0);
        assert!(!has_configured_project(&project_session, CONFIG_FILE_NAME));
        project_session.close();
    }
}

// Go: session_apistate_test.go:57 TestSessionTracksAndReleasesAPIRefs/explicit close releases the project ref
child_test! {
    fn explicit_close_releases_the_project_ref() {
        const CONFIG_FILE_NAME: &str = "/home/projects/p/tsconfig.json";
        let (project_session, _) = projecttestutil::setup(files(&[
            (CONFIG_FILE_NAME, r#"{ "compilerOptions": { "strict": true } }"#),
            ("/home/projects/p/src/index.ts", "export const x = 1;"),
        ]));
        let session = api::new_session(project_session.clone(), None);

        nil_error(session.handle_update_snapshot(
            &bg(),
            &UpdateSnapshotParams {
                open_projects: vec![doc(CONFIG_FILE_NAME)],
                ..Default::default()
            },
        ));
        assert_eq!(session.open_projects.borrow().len(), 1);
        assert!(has_configured_project(&project_session, CONFIG_FILE_NAME));

        // Closing a project we hold releases the ref and unloads the project.
        nil_error(session.handle_update_snapshot(
            &bg(),
            &UpdateSnapshotParams {
                close_projects: vec![doc(CONFIG_FILE_NAME)],
                ..Default::default()
            },
        ));
        assert_eq!(session.open_projects.borrow().len(), 0);
        assert!(!has_configured_project(&project_session, CONFIG_FILE_NAME));

        // Closing a project we don't hold is a no-op (never over-releases).
        nil_error(session.handle_update_snapshot(
            &bg(),
            &UpdateSnapshotParams {
                close_projects: vec![doc(CONFIG_FILE_NAME)],
                ..Default::default()
            },
        ));
        assert_eq!(session.open_projects.borrow().len(), 0);
        session.close();
        project_session.close();
    }
}

// Go: session_apistate_test.go:92 TestSessionTracksAndReleasesAPIRefs/file opens are idempotent and released on close
child_test! {
    fn file_opens_are_idempotent_and_released_on_close() {
        const FILE_NAME: &str = "/home/projects/p/src/index.ts";
        let (project_session, _) = projecttestutil::setup(files(&[
            (
                "/home/projects/p/tsconfig.json",
                r#"{ "compilerOptions": { "strict": true } }"#,
            ),
            (FILE_NAME, "export const x = 1;"),
        ]));
        let session = api::new_session(project_session.clone(), None);

        nil_error(session.handle_update_snapshot(
            &bg(),
            &UpdateSnapshotParams {
                open_files: vec![doc(FILE_NAME)],
                ..Default::default()
            },
        ));
        assert_eq!(session.open_files.borrow().len(), 1);

        // Re-opening the same file must not take an additional ref.
        nil_error(session.handle_update_snapshot(
            &bg(),
            &UpdateSnapshotParams {
                open_files: vec![doc(FILE_NAME)],
                ..Default::default()
            },
        ));
        assert_eq!(session.open_files.borrow().len(), 1);

        // The file should resolve to the configured project via ancestor search.
        assert!(has_configured_project(
            &project_session,
            "/home/projects/p/tsconfig.json"
        ));

        // Closing a file we don't hold is a no-op (never over-releases).
        nil_error(session.handle_update_snapshot(
            &bg(),
            &UpdateSnapshotParams {
                close_files: vec![doc("/home/projects/p/other.ts")],
                ..Default::default()
            },
        ));
        assert_eq!(session.open_files.borrow().len(), 1);

        // Explicitly closing the held file releases the ref.
        nil_error(session.handle_update_snapshot(
            &bg(),
            &UpdateSnapshotParams {
                close_files: vec![doc(FILE_NAME)],
                ..Default::default()
            },
        ));
        assert_eq!(session.open_files.borrow().len(), 0);

        // Closing the file also tears down the configured project that was
        // auto-loaded to serve it, instead of leaking it.
        assert!(
            !has_configured_project(&project_session, "/home/projects/p/tsconfig.json"),
            "configured project auto-loaded for the API-opened file should be unloaded after close"
        );

        session.close();
        assert_eq!(session.open_files.borrow().len(), 0);
        project_session.close();
    }
}

// Go: session_apistate_test.go:144 TestSessionTracksAndReleasesAPIRefs/relative file paths normalize consistently for open and close
child_test! {
    fn relative_file_paths_normalize_consistently_for_open_and_close() {
        // The project session's current directory is "/", so a relative path
        // resolves to the corresponding absolute path.
        let (project_session, _) = projecttestutil::setup(files(&[
            ("/src/tsconfig.json", r#"{ "compilerOptions": { "strict": true } }"#),
            ("/src/index.ts", "export const x = 1;"),
        ]));
        let session = api::new_session(project_session.clone(), None);

        // Open via a relative path; it should be tracked under the absolute path
        // and resolve to the containing configured project.
        let open_resp = nil_error(session.handle_update_snapshot(
            &bg(),
            &UpdateSnapshotParams {
                open_files: vec![doc("src/index.ts")],
                ..Default::default()
            },
        ));
        assert_eq!(session.open_files.borrow().len(), 1);
        assert!(session.open_files.borrow().contains(&path("/src/index.ts")));
        assert!(has_configured_project(&project_session, "/src/tsconfig.json"));

        // getDefaultProjectForFile must also resolve a relative path to the same
        // configured project (it builds a URI from the identifier internally).
        let proj = nil_error(session.handle_get_default_project_for_file(
            &bg(),
            &GetDefaultProjectForFileParams {
                snapshot: open_resp.snapshot,
                file: doc("src/index.ts"),
            },
        ));
        let proj = proj.expect("relative path should resolve to a default project");
        assert_eq!(proj.config_file_name, "/src/tsconfig.json");

        // Re-opening via the absolute path must match the relative open (no new ref).
        nil_error(session.handle_update_snapshot(
            &bg(),
            &UpdateSnapshotParams {
                open_files: vec![doc("/src/index.ts")],
                ..Default::default()
            },
        ));
        assert_eq!(session.open_files.borrow().len(), 1);

        // Closing via a relative path must match the path stored when opening.
        nil_error(session.handle_update_snapshot(
            &bg(),
            &UpdateSnapshotParams {
                close_files: vec![doc("src/index.ts")],
                ..Default::default()
            },
        ));
        assert_eq!(session.open_files.borrow().len(), 0);
        assert!(
            !has_configured_project(&project_session, "/src/tsconfig.json"),
            "configured project should be unloaded after closing the relatively-pathed file"
        );
        session.close();
        project_session.close();
    }
}

// Go: session_apistate_test.go:202 TestUpdateSnapshotResponseSkipsUnloadedAncestorProject
// TestUpdateSnapshotResponseSkipsUnloadedAncestorProject verifies that API
// updateSnapshot does not report unloaded ancestor project placeholders. This
// covers the case where opening a file loads its nearest configured project
// while solution search discovers an ancestor tsconfig placeholder whose command
// line is still nil.
child_test! {
    fn update_snapshot_response_skips_unloaded_ancestor_project() {
        const NESTED_CONFIG_FILE_NAME: &str = "/repo/packages/app/tsconfig.json";
        const ANCESTOR_CONFIG_FILE_NAME: &str = "/repo/packages/tsconfig.json";
        const FILE_NAME: &str = "/repo/packages/app/src/index.ts";
        const FILE_TEXT: &str = "let s: string = 1234;";
        let (project_session, _) = projecttestutil::setup(files(&[
            (ANCESTOR_CONFIG_FILE_NAME, r#"{ "files": [] }"#),
            (
                NESTED_CONFIG_FILE_NAME,
                r#"{
			"compilerOptions": { "composite": true },
			"include": ["**/*"]
		}"#,
            ),
            (FILE_NAME, FILE_TEXT),
        ]));

        open(&project_session, &format!("file://{FILE_NAME}"), FILE_TEXT);
        let nested_project = configured_project(&project_session, NESTED_CONFIG_FILE_NAME)
            .expect("nested project");
        assert!(nested_project.borrow().command_line.is_some());
        let ancestor_project = configured_project(&project_session, ANCESTOR_CONFIG_FILE_NAME)
            .expect("ancestor project");
        assert!(ancestor_project.borrow().command_line.is_none());

        let session = api::new_session(project_session.clone(), None);

        let response = nil_error(session.handle_update_snapshot(
            &bg(),
            &UpdateSnapshotParams {
                open_projects: vec![doc(NESTED_CONFIG_FILE_NAME)],
                ..Default::default()
            },
        ));

        let mut found_nested_project = false;
        let mut found_ancestor_project = false;
        for project in &response.projects {
            match project.config_file_name.as_str() {
                NESTED_CONFIG_FILE_NAME => {
                    found_nested_project = true;
                    // PORT: Go checks `RootFiles != nil`; a Rust `Vec` has no nil.
                    assert!(project.compiler_options.is_some());
                }
                ANCESTOR_CONFIG_FILE_NAME => found_ancestor_project = true,
                _ => {}
            }
        }
        assert!(found_nested_project);
        assert!(!found_ancestor_project);
        session.close();
        project_session.close();
    }
}
