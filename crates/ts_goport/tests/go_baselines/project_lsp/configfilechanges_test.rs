//! Port of Go `internal/project/configfilechanges_test.go` (`TestConfigFileChanges`).

use std::rc::Rc;

use ts_goport::flags::ScriptTarget;
use ts_goport::options::Tristate;

use super::projecttestutil::{self, FileMap, files};
use super::util::*;

// Go: configfilechanges_test.go:21 files
fn config_files() -> FileMap {
    files(&[
        ("/tsconfig.more-base.json", "{}"),
        (
            "/tsconfig.base.json",
            r#"{"extends": "../tsconfig.more-base.json", "compilerOptions": {"strict": true}}"#,
        ),
        (
            "/src/tsconfig.json",
            r#"{"extends": "../tsconfig.base.json", "compilerOptions": {"target": "es6"}, "references": [{"path": "../utils"}]}"#,
        ),
        ("/src/index.ts", r#"console.log("Hello, world!");"#),
        ("/src/subfolder/foo.ts", r#"export const foo = "bar";"#),
        (
            "/utils/tsconfig.json",
            r#"{"compilerOptions": {"composite": true}}"#,
        ),
        ("/utils/index.ts", r#"console.log("Hello, test!");"#),
    ])
}

const INDEX: &str = r#"console.log("Hello, world!");"#;

child_test! {
    // Go: configfilechanges_test.go:32 TestConfigFileChanges/should update program options on config file change
    fn should_update_program_options_on_config_file_change() {
        let (session, utils) = projecttestutil::setup(config_files());
        open(&session, "file:///src/index.ts", INDEX);

        utils
            .fs()
            .write_file(
                "/src/tsconfig.json",
                r#"{"extends": "../tsconfig.base.json", "compilerOptions": {"target": "esnext"}, "references": [{"path": "../utils"}]}"#,
            )
            .unwrap();
        watch(&session, &[(CHANGED, "file:///src/tsconfig.json")]);

        let p = program(&session, "file:///src/index.ts");
        assert_eq!(p.options().target, ScriptTarget::ES_NEXT);
    }
}

child_test! {
    // Go: configfilechanges_test.go:51 TestConfigFileChanges/should update project on extended config file change
    fn should_update_project_on_extended_config_file_change() {
        let (session, utils) = projecttestutil::setup(config_files());
        open(&session, "file:///src/index.ts", INDEX);

        utils
            .fs()
            .write_file("/tsconfig.base.json", r#"{"compilerOptions": {"strict": false}}"#)
            .unwrap();
        watch(&session, &[(CHANGED, "file:///tsconfig.base.json")]);

        let p = program(&session, "file:///src/index.ts");
        assert_eq!(p.options().strict, Tristate::False);
    }
}

child_test! {
    // Go: configfilechanges_test.go:70 TestConfigFileChanges/should update project on doubly extended config file change
    fn should_update_project_on_doubly_extended_config_file_change() {
        let (session, utils) = projecttestutil::setup(config_files());
        open(&session, "file:///src/index.ts", INDEX);

        utils
            .fs()
            .write_file(
                "/tsconfig.more-base.json",
                r#"{"compilerOptions": {"verbatimModuleSyntax": true}}"#,
            )
            .unwrap();
        watch(&session, &[(CHANGED, "file:///tsconfig.more-base.json")]);

        let p = program(&session, "file:///src/index.ts");
        assert_eq!(p.options().verbatim_module_syntax, Tristate::True);
    }
}

child_test! {
    // Go: configfilechanges_test.go:89 TestConfigFileChanges/should update project on referenced config file change
    fn should_update_project_on_referenced_config_file_change() {
        let (session, utils) = projecttestutil::setup(config_files());
        open(&session, "file:///src/index.ts", INDEX);
        let snapshot_before = session.snapshot();

        utils
            .fs()
            .write_file(
                "/utils/tsconfig.json",
                r#"{"compilerOptions": {"composite": true, "target": "esnext"}}"#,
            )
            .unwrap();
        watch(&session, &[(CHANGED, "file:///utils/tsconfig.json")]);

        let _ = language_service(&session, "file:///src/index.ts");
        let snapshot_after = session.snapshot();
        assert!(
            !Rc::ptr_eq(&snapshot_after, &snapshot_before),
            "Snapshot should be updated after config file change"
        );
    }
}

child_test! {
    // Go: configfilechanges_test.go:110 TestConfigFileChanges/should close project on config file deletion
    fn should_close_project_on_config_file_deletion() {
        let (session, utils) = projecttestutil::setup(config_files());
        open(&session, "file:///src/index.ts", INDEX);

        utils.fs().remove("/src/tsconfig.json").unwrap();
        watch(&session, &[(DELETED, "file:///src/tsconfig.json")]);

        let _ = language_service(&session, "file:///src/index.ts");
        assert!(projects_len(&session) == 1);
        assert!(has_inferred_project(&session));
    }
}

child_test! {
    // Go: configfilechanges_test.go:131 TestConfigFileChanges/config file creation then deletion
    fn config_file_creation_then_deletion() {
        let (session, utils) = projecttestutil::setup(config_files());
        open(&session, "file:///src/subfolder/foo.ts", r#"export const foo = "bar";"#);

        utils.fs().write_file("/src/subfolder/tsconfig.json", "{}").unwrap();
        watch(&session, &[(CREATED, "file:///src/subfolder/tsconfig.json")]);

        let _ = language_service(&session, "file:///src/subfolder/foo.ts");
        assert_eq!(projects_len(&session), 2);
        assert_eq!(
            default_project_name(&session, "file:///src/subfolder/foo.ts"),
            "/src/subfolder/tsconfig.json"
        );

        utils.fs().remove("/src/subfolder/tsconfig.json").unwrap();
        watch(&session, &[(DELETED, "file:///src/subfolder/tsconfig.json")]);

        let _ = language_service(&session, "file:///src/subfolder/foo.ts");
        assert_eq!(
            default_project_name(&session, "file:///src/subfolder/foo.ts"),
            "/src/tsconfig.json"
        );
        assert_eq!(projects_len(&session), 2); // Old project will be cleaned up on next file open

        open(&session, "file:///src/index.ts", INDEX);
        assert_eq!(projects_len(&session), 1);
    }
}

child_test! {
    // Go: configfilechanges_test.go:171 TestConfigFileChanges/should update project when missing extended config is created
    fn should_update_project_when_missing_extended_config_is_created() {
        // Start with a project whose tsconfig extends a base config that doesn't exist yet
        let mut missing_base_files = config_files();
        missing_base_files.remove("/tsconfig.base.json");

        let (session, utils) = projecttestutil::setup(missing_base_files);
        open(&session, "file:///src/index.ts", INDEX);

        // Create the previously-missing base config file that is extended by /src/tsconfig.json
        utils
            .fs()
            .write_file("/tsconfig.base.json", r#"{"compilerOptions": {"strict": true}}"#)
            .unwrap();
        watch(&session, &[(CREATED, "file:///tsconfig.base.json")]);

        // Accessing the language service should trigger project update
        let p = program(&session, "file:///src/index.ts");
        assert_eq!(p.options().strict, Tristate::True);
    }
}
