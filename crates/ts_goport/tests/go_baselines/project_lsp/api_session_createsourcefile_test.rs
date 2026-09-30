//! Port of Go `internal/api/session_createsourcefile_test.go` (ts#64216,
//! ts#64434).
//!
//! PORT: the tests are in `project_lsp` because they use `projecttestutil`
//! and `child_test!`. Each Go subtest is one `#[test]`, so each one sets up
//! its own session with the parent's files (the Go subtests share the
//! parent's session). A Go `t.Cleanup` is a call at the end of the test.
//!
//! PORT: a lease's `SourceFile()` is the root node of the parse; the Go
//! `*ast.SourceFile` fields and methods are the `ast::source_file_*` reads
//! of that node. Go compares `*ast.SourceFile` pointers; the port compares
//! the root nodes.

use std::rc::Rc;

use ts_goport::api::{
    self, CreateSourceFileFromFileParams, CreateSourceFileOptions, CreateSourceFileParams,
    ReleaseSourceFileParams, SourceFileLeaseID,
};
use ts_goport::ast;
use ts_goport::flags::ScriptKind;
use ts_goport::lsp::lsproto;
use ts_goport::project;

use super::api_util::{error_contains, nil_error};
use super::projecttestutil::{self, files};
use super::util::{bg, program, uri};

/// The Go parent test's setup: its project session and API session.
fn setup() -> (Rc<project::Session>, Rc<api::Session>) {
    let (project_session, _) =
        projecttestutil::setup(files(&[("/src/input.ts", "export const fromFile = 1;")]));
    let session = api::new_lsp_session(project_session.clone(), None);
    (project_session, session)
}

// Go: session_createsourcefile_test.go:24 TestCreateSourceFile/text
child_test! {
    fn text() {
        let (project_session, session) = setup();
        let lease = nil_error(session.create_source_file(
            "src/input.tsx",
            "export const element = <div />;",
            &CreateSourceFileOptions::default(),
        ));

        let source_file = lease.source_file();
        assert_eq!(ast::source_file_file_name(source_file), "/src/input.tsx");
        assert_eq!(ast::source_file_info(source_file).path, "/src/input.tsx");
        assert_eq!(
            ast::source_file_text(source_file),
            "export const element = <div />;"
        );
        assert_eq!(ast::source_file_info(source_file).script_kind, ScriptKind::TSX);
        assert_eq!(source_file.statements().len(), 1);
        assert!(ast::source_file_is_bound(source_file));
        lease.release();
        session.close();
        project_session.close();
    }
}

// Go: session_createsourcefile_test.go:43 TestCreateSourceFile/script kind override
child_test! {
    fn script_kind_override() {
        let (project_session, session) = setup();
        let lease = nil_error(session.create_source_file(
            "/src/component.txt",
            "export const element = <div />;",
            &CreateSourceFileOptions {
                script_kind: ScriptKind::TSX,
            },
        ));

        let source_file = lease.source_file();
        assert_eq!(ast::source_file_info(source_file).script_kind, ScriptKind::TSX);
        assert_eq!(ast::source_file_diagnostics(source_file).len(), 0);
        lease.release();
        session.close();
        project_session.close();
    }
}

// Go: session_createsourcefile_test.go:58 TestCreateSourceFile/shares parse cache with programs
child_test! {
    fn shares_parse_cache_with_programs() {
        let (project_session, session) = setup();

        const FILE_NAME: &str = "/src/shared.ts";
        const SOURCE_TEXT: &str = "export const shared = 1;";
        let (cache_project_session, _) = projecttestutil::setup(files(&[(FILE_NAME, SOURCE_TEXT)]));
        let cache_session = api::new_lsp_session(cache_project_session.clone(), None);

        cache_project_session.did_open_file(
            &bg(),
            &uri("file:///src/shared.ts"),
            1,
            SOURCE_TEXT,
            &lsproto::LanguageKind::TYPE_SCRIPT,
        );
        let language_service_program = program(&cache_project_session, "file:///src/shared.ts");
        cache_project_session.wait_for_background_tasks();

        let program_file = language_service_program.get_source_file(FILE_NAME).unwrap();
        let direct = cache_session.acquire_source_file(
            program_file.parse_options.clone(),
            SOURCE_TEXT,
            program_file.script_kind,
        );
        assert_eq!(program_file.root, direct.source_file());
        direct.release();
        cache_session.close();
        cache_project_session.close();
        session.close();
        project_session.close();
    }
}

// Go: session_createsourcefile_test.go:79 TestCreateSourceFile/lease release
child_test! {
    fn lease_release() {
        let (project_session, session) = setup();

        let find_lease = |file_name: &str| -> SourceFileLeaseID {
            for (id, lease) in session.source_file_leases.borrow().iter() {
                if ast::source_file_file_name(lease.source_file()) == file_name {
                    return *id;
                }
            }
            SourceFileLeaseID(0)
        };

        let first = nil_error(session.handle_create_source_file(
            &bg(),
            &CreateSourceFileParams {
                file_name: "/src/lease-1.ts".to_string(),
                source_text: "export {};".to_string(),
                ..Default::default()
            },
        ));
        assert!(first.is_some());
        let first_lease = find_lease("/src/lease-1.ts");
        assert!(first_lease != SourceFileLeaseID(0));

        let second = nil_error(session.handle_create_source_file(
            &bg(),
            &CreateSourceFileParams {
                file_name: "/src/lease-2.ts".to_string(),
                source_text: "export {};".to_string(),
                ..Default::default()
            },
        ));
        assert!(second.is_some());
        let second_lease = find_lease("/src/lease-2.ts");
        assert!(second_lease != SourceFileLeaseID(0));
        assert!(first_lease != second_lease);

        nil_error(session.handle_release_source_file(Some(&ReleaseSourceFileParams {
            lease: first_lease,
        })));
        assert_eq!(find_lease("/src/lease-1.ts"), SourceFileLeaseID(0));

        error_contains(
            session.handle_release_source_file(Some(&ReleaseSourceFileParams {
                lease: first_lease,
            })),
            "source file lease",
        );

        nil_error(session.handle_release_source_file(Some(&ReleaseSourceFileParams {
            lease: second_lease,
        })));
        session.close();
        project_session.close();
    }
}

// Go: session_createsourcefile_test.go:123 TestCreateSourceFile/unknown extension defaults to TypeScript
child_test! {
    fn unknown_extension_defaults_to_type_script() {
        let (project_session, session) = setup();
        let lease = nil_error(session.create_source_file(
            "/src/component.txt",
            r#"export const value: string = "ok";"#,
            &CreateSourceFileOptions::default(),
        ));

        let source_file = lease.source_file();
        assert_eq!(ast::source_file_info(source_file).script_kind, ScriptKind::TS);
        assert_eq!(ast::source_file_diagnostics(source_file).len(), 0);
        lease.release();
        session.close();
        project_session.close();
    }
}

// Go: session_createsourcefile_test.go:138 TestCreateSourceFile/from file
child_test! {
    fn from_file() {
        let (project_session, session) = setup();
        let result = nil_error(session.handle_create_source_file_from_file(
            &bg(),
            &CreateSourceFileFromFileParams {
                file_name: "/src/input.ts".to_string(),
                ..Default::default()
            },
        ));

        assert!(result.is_some());
        session.close();
        project_session.close();
    }
}

// Go: session_createsourcefile_test.go:148 TestCreateSourceFile/invalid script kind
child_test! {
    fn invalid_script_kind() {
        let (project_session, session) = setup();
        error_contains(
            session.create_source_file(
                "/src/input.ts",
                "",
                &CreateSourceFileOptions {
                    script_kind: ScriptKind(999),
                },
            ),
            "invalid scriptKind 999",
        );
        session.close();
        project_session.close();
    }
}

// Go: session_createsourcefile_test.go:159 TestCreateSourceFile/missing file
child_test! {
    fn missing_file() {
        let (project_session, session) = setup();
        error_contains(
            session.handle_create_source_file_from_file(
                &bg(),
                &CreateSourceFileFromFileParams {
                    file_name: "/src/missing.ts".to_string(),
                    ..Default::default()
                },
            ),
            r#"could not read file "/src/missing.ts""#,
        );
        session.close();
        project_session.close();
    }
}
