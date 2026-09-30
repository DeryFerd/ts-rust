//! Port of Go `internal/project/projectlifetime_test.go` (`TestProjectLifetime`).

use super::projecttestutil::{self, files};
use super::util::*;

const TSCONFIG: &str = r#"{
				"compilerOptions": {
					"noLib": true,
					"module": "nodenext",
					"strict": true
				},
				"include": ["src"]
			}"#;

child_test! {
    // Go: projectlifetime_test.go:20 TestProjectLifetime/configured project
    fn configured_project() {
        let mut entries = Vec::new();
        for p in ["p1", "p2", "p3"] {
            entries.push((format!("/home/projects/TS/{p}/tsconfig.json"), TSCONFIG));
            entries.push((format!("/home/projects/TS/{p}/src/index.ts"), r#"import { x } from "./x";"#));
            entries.push((format!("/home/projects/TS/{p}/src/x.ts"), "export const x = 1;"));
            entries.push((format!("/home/projects/TS/{p}/config.ts"), "let x = 1, y = 2;"));
        }
        let entries: Vec<(&str, &str)> = entries.iter().map(|(p, t)| (p.as_str(), *t)).collect();
        let (session, utils) = projecttestutil::setup(files(&entries));
        assert_eq!(projects_len(&session), 0);

        // Open files in two projects
        let uri1 = "file:///home/projects/TS/p1/src/index.ts";
        let uri2 = "file:///home/projects/TS/p2/src/index.ts";
        open(&session, uri1, r#"import { x } from "./x";"#);
        open(&session, uri2, r#"import { x } from "./x";"#);
        session.wait_for_background_tasks();
        assert_eq!(projects_len(&session), 2);
        assert!(has_configured_project(&session, "/home/projects/ts/p1/tsconfig.json"));
        assert!(has_configured_project(&session, "/home/projects/ts/p2/tsconfig.json"));
        assert_eq!(utils.client().watch_files_calls().len(), 1);
        assert!(has_config(&session, "/home/projects/ts/p1/tsconfig.json"));
        assert!(has_config(&session, "/home/projects/ts/p2/tsconfig.json"));

        // Close p1 file and open p3 file
        close(&session, uri1);
        let uri3 = "file:///home/projects/TS/p3/src/index.ts";
        open(&session, uri3, r#"import { x } from "./x";"#);
        session.wait_for_background_tasks();
        // Should still have two projects, but p1 replaced by p3
        assert_eq!(projects_len(&session), 2);
        assert!(!has_configured_project(&session, "/home/projects/ts/p1/tsconfig.json"));
        assert!(has_configured_project(&session, "/home/projects/ts/p2/tsconfig.json"));
        assert!(has_configured_project(&session, "/home/projects/ts/p3/tsconfig.json"));
        assert!(!has_config(&session, "/home/projects/ts/p1/tsconfig.json"));
        assert!(has_config(&session, "/home/projects/ts/p2/tsconfig.json"));
        assert!(has_config(&session, "/home/projects/ts/p3/tsconfig.json"));
        assert_eq!(utils.client().watch_files_calls().len(), 1);
        assert_eq!(utils.client().unwatch_files_calls().len(), 0);

        // Close p2 and p3 files, open p1 file again
        close(&session, uri2);
        close(&session, uri3);
        open(&session, uri1, r#"import { x } from "./x";"#);
        session.wait_for_background_tasks();
        // Should have one project (p1)
        assert_eq!(projects_len(&session), 1);
        assert!(has_configured_project(&session, "/home/projects/ts/p1/tsconfig.json"));
        assert!(has_config(&session, "/home/projects/ts/p1/tsconfig.json"));
        assert!(!has_config(&session, "/home/projects/ts/p2/tsconfig.json"));
        assert!(!has_config(&session, "/home/projects/ts/p3/tsconfig.json"));
        assert_eq!(utils.client().watch_files_calls().len(), 1);
        assert_eq!(utils.client().unwatch_files_calls().len(), 0);
    }
}

child_test! {
    // Go: projectlifetime_test.go:108 TestProjectLifetime/unrooted inferred projects
    fn unrooted_inferred_projects() {
        let mut entries = Vec::new();
        for p in ["p1", "p2", "p3"] {
            entries.push((format!("/home/projects/TS/{p}/src/index.ts"), r#"import { x } from "./x";"#));
            entries.push((format!("/home/projects/TS/{p}/src/x.ts"), "export const x = 1;"));
            entries.push((format!("/home/projects/TS/{p}/config.ts"), "let x = 1, y = 2;"));
        }
        let entries: Vec<(&str, &str)> = entries.iter().map(|(p, t)| (p.as_str(), *t)).collect();
        let (session, _) = projecttestutil::setup(files(&entries));
        assert_eq!(projects_len(&session), 0);

        // Open files without workspace roots (empty string) - should create single inferred project
        let uri1 = "file:///home/projects/TS/p1/src/index.ts";
        let uri2 = "file:///home/projects/TS/p2/src/index.ts";
        open(&session, uri1, r#"import { x } from "./x";"#);
        open(&session, uri2, r#"import { x } from "./x";"#);

        // Should have one inferred project
        assert_eq!(projects_len(&session), 1);
        assert!(has_inferred_project(&session));

        // Close p1 file and open p3 file
        close(&session, uri1);
        let uri3 = "file:///home/projects/TS/p3/src/index.ts";
        open(&session, uri3, r#"import { x } from "./x";"#);

        // Should still have one inferred project
        assert_eq!(projects_len(&session), 1);
        assert!(has_inferred_project(&session));

        // Close p2 and p3 files, open p1 file again
        close(&session, uri2);
        close(&session, uri3);
        open(&session, uri1, r#"import { x } from "./x";"#);

        // Should still have one inferred project
        assert_eq!(projects_len(&session), 1);
        assert!(has_inferred_project(&session));
    }
}

child_test! {
    // Go: projectlifetime_test.go:157 TestProjectLifetime/file moves from inferred to configured project
    fn file_moves_from_inferred_to_configured_project() {
        let files = files(&[
            ("/home/projects/ts/foo.ts", "export const foo = 1;"),
            (
                "/home/projects/ts/p1/tsconfig.json",
                r#"{
				"compilerOptions": {
					"noLib": true,
					"module": "nodenext",
					"strict": true
				},
				"include": ["main.ts"]
			}"#,
            ),
            (
                "/home/projects/ts/p1/main.ts",
                r#"import { foo } from "../foo"; console.log(foo);"#,
            ),
        ]);
        let (session, _) = projecttestutil::setup(files);

        // Open foo.ts first - should create inferred project since no tsconfig found initially
        let foo_uri = "file:///home/projects/ts/foo.ts";
        open(&session, foo_uri, "export const foo = 1;");

        // Should have one inferred project
        assert_eq!(projects_len(&session), 1);
        assert!(has_inferred_project(&session));
        assert!(!has_configured_project(&session, "/home/projects/ts/p1/tsconfig.json"));

        // Now open main.ts - should trigger discovery of tsconfig.json and move foo.ts to configured project
        let main_uri = "file:///home/projects/ts/p1/main.ts";
        open(&session, main_uri, r#"import { foo } from "../foo"; console.log(foo);"#);

        // Should now have one configured project and no inferred project
        assert_eq!(projects_len(&session), 1);
        assert!(!has_inferred_project(&session));
        assert!(has_configured_project(&session, "/home/projects/ts/p1/tsconfig.json"));

        // Config file should be present
        assert!(has_config(&session, "/home/projects/ts/p1/tsconfig.json"));

        // Close main.ts - configured project should remain because foo.ts is still open
        close(&session, main_uri);
        assert_eq!(projects_len(&session), 1);
        assert!(has_configured_project(&session, "/home/projects/ts/p1/tsconfig.json"));

        // Close foo.ts - configured project should be retained until next file open
        close(&session, foo_uri);
        assert_eq!(projects_len(&session), 1);
        assert!(has_config(&session, "/home/projects/ts/p1/tsconfig.json"));
    }
}

child_test! {
    // Go: projectlifetime_test.go:209 TestProjectLifetime/file move from inferred to configured via didOpen/didClose sequence
    fn file_move_from_inferred_to_configured_via_did_open_did_close_sequence() {
        // Start with tsconfig.json that includes "src" but file is at root level
        let files = files(&[
            (
                "/home/projects/TS/p1/tsconfig.json",
                r#"{
				"compilerOptions": {
					"noLib": true
				},
				"include": ["src"]
			}"#,
            ),
            ("/home/projects/TS/p1/index.ts", "export const x = 1;"),
        ]);
        let (session, utils) = projecttestutil::setup(files);

        // Open index.ts at root level - should create inferred project since it's not under src/
        let index_uri = "file:///home/projects/TS/p1/index.ts";
        open(&session, index_uri, "export const x = 1;");

        // Should have one inferred project only (file is not included by tsconfig)
        assert_eq!(projects_len(&session), 1);
        assert!(has_inferred_project(&session));
        assert!(!has_configured_project(&session, "/home/projects/ts/p1/tsconfig.json"));

        // Simulate file move: create src/index.ts on disk
        utils
            .fs()
            .write_file("/home/projects/TS/p1/src/index.ts", "export const x = 1;")
            .unwrap();
        utils.fs().remove("/home/projects/TS/p1/index.ts").unwrap();

        // 1. didOpen src/index.ts (new location)
        let src_index_uri = "file:///home/projects/TS/p1/src/index.ts";
        open(&session, src_index_uri, "export const x = 1;");

        // 2. didClose index.ts (old location)
        close(&session, index_uri);

        // 3. didChangeWatchedFiles: create src/index.ts and delete index.ts
        watch(&session, &[(CREATED, src_index_uri), (DELETED, index_uri)]);

        // Should now have one configured project only (file is now under src/)
        let _ = language_service(&session, src_index_uri);
        assert_eq!(projects_len(&session), 1);
        assert!(!has_inferred_project(&session));
        assert!(has_configured_project(&session, "/home/projects/ts/p1/tsconfig.json"));
    }
}

child_test! {
    // Go: projectlifetime_test.go:356 TestProjectLifetime/tsconfig move from subdirectory to parent via didChangeWatchedFiles (ts#64081)
    fn tsconfig_move_from_subdirectory_to_parent_via_did_change_watched_files() {
        let tsconfig_content = r#"{
				"compilerOptions": {
					"noLib": true
				},
				"include": ["src"]
			}"#;
        let files = files(&[
            ("/home/projects/TS/p1/src/tsconfig.json", tsconfig_content),
            ("/home/projects/TS/p1/src/index.ts", "export const x = 1;"),
            ("/home/projects/TS/p1/src/other.ts", "export const y = 2;"),
        ]);
        let (session, utils) = projecttestutil::setup(files);

        // Open src/index.ts - should create inferred project since tsconfig.json includes "src"
        // relative to its location (src/src/ which doesn't exist)
        let index_uri = "file:///home/projects/TS/p1/src/index.ts";
        open(&session, index_uri, "export const x = 1;");

        // Should have one inferred project only (file is not included by tsconfig at src/tsconfig.json)
        assert_eq!(projects_len(&session), 1);
        assert!(has_inferred_project(&session));
        assert!(!has_configured_project(&session, "/home/projects/ts/p1/src/tsconfig.json"));

        // Simulate tsconfig.json move: create tsconfig.json at parent level, delete from src/
        utils
            .fs()
            .write_file("/home/projects/TS/p1/tsconfig.json", tsconfig_content)
            .unwrap();
        utils.fs().remove("/home/projects/TS/p1/src/tsconfig.json").unwrap();

        // Simulate file move via didChangeWatchedFiles
        watch(
            &session,
            &[
                (CREATED, "file:///home/projects/TS/p1/tsconfig.json"),
                (DELETED, "file:///home/projects/TS/p1/src/tsconfig.json"),
            ],
        );
        session.wait_for_background_tasks();

        // The background update should route index.ts to the new configured project,
        // but project cleanup is deferred until the next file open.
        let _ = language_service(&session, index_uri);
        assert_eq!(projects_len(&session), 2);
        assert!(has_inferred_project(&session));
        assert_eq!(
            default_project_config_file_name(&session, index_uri),
            "/home/projects/TS/p1/tsconfig.json"
        );

        let other_uri = "file:///home/projects/TS/p1/src/other.ts";
        open(&session, other_uri, "export const y = 2;");
        assert_eq!(projects_len(&session), 1);
        assert!(!has_inferred_project(&session));
        assert!(has_configured_project(&session, "/home/projects/ts/p1/tsconfig.json"));
    }
}

child_test! {
    // Go: projectlifetime_test.go:332 TestProjectLifetime/deleted open file remains in project until closed
    fn deleted_open_file_remains_in_project_until_closed() {
        let files = files(&[
            (
                "/home/projects/TS/p1/tsconfig.json",
                r#"{
				"compilerOptions": {
					"noLib": true
				},
				"include": ["src"]
			}"#,
            ),
            ("/home/projects/TS/p1/src/index.ts", ""),
            ("/home/projects/TS/p1/src/x.ts", "export const x = 1;"),
        ]);
        let (session, utils) = projecttestutil::setup(files);

        // Step 1: Open both files
        let index_uri = "file:///home/projects/TS/p1/src/index.ts";
        let x_uri = "file:///home/projects/TS/p1/src/x.ts";
        open(&session, index_uri, "");
        open(&session, x_uri, "export const x = 1;");

        // Verify initial state - both files should be in the project
        let p = program(&session, index_uri);
        assert!(has_file(&p, "/home/projects/TS/p1/src/index.ts"), "index.ts should be in project");
        assert!(has_file(&p, "/home/projects/TS/p1/src/x.ts"), "x.ts should be in project");

        // Step 2: In a single batch change:
        // - Delete x.ts from disk (but leave it open)
        // - Create a new file y.ts on disk
        utils.fs().remove("/home/projects/TS/p1/src/x.ts").unwrap();
        utils
            .fs()
            .write_file("/home/projects/TS/p1/src/y.ts", "export const y = 2;")
            .unwrap();

        // Send both events in a single batch
        watch(
            &session,
            &[(DELETED, x_uri), (CREATED, "file:///home/projects/TS/p1/src/y.ts")],
        );

        // Step 3 & 4: Request LS for the deleted but still open file
        let p = program(&session, x_uri);
        assert!(has_file(&p, "/home/projects/TS/p1/src/index.ts"), "index.ts should still be in project");
        assert!(
            has_file(&p, "/home/projects/TS/p1/src/x.ts"),
            "x.ts should still be in project (open overlay)"
        );
        assert!(has_file(&p, "/home/projects/TS/p1/src/y.ts"), "y.ts should be in project (new file)");

        // Step 5: Close the deleted file
        close(&session, x_uri);

        // Step 6: On next LS request, x.ts should be excluded
        let p = program(&session, index_uri);
        assert!(has_file(&p, "/home/projects/TS/p1/src/index.ts"), "index.ts should still be in project");
        assert!(
            !has_file(&p, "/home/projects/TS/p1/src/x.ts"),
            "x.ts should no longer be in project (closed and deleted)"
        );
        assert!(has_file(&p, "/home/projects/TS/p1/src/y.ts"), "y.ts should still be in project");
    }
}
