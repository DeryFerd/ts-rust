//! Port of Go `internal/project/customconfigfilename_test.go` (`TestCustomConfigFileName`).

use ts_goport::frontend::json_ext::LspAny;
use ts_goport::ls::lsutil;
use ts_goport::options::Tristate;

use super::projecttestutil::{self, FileMap, files};
use super::util::*;

// Go: customconfigfilename_test.go:21 files
fn config_files() -> FileMap {
    files(&[
        (
            "/src/tsconfig.json",
            r#"{"compilerOptions": {"strict": false}}"#,
        ),
        (
            "/src/tsconfig.all.json",
            r#"{"compilerOptions": {"strict": true}}"#,
        ),
        ("/src/index.ts", "export const x = 1;"),
    ])
}

const URI: &str = "file:///src/index.ts";

fn prefs_with_custom_config(name: &str) -> lsutil::UserPreferences {
    let mut prefs = lsutil::new_default_user_preferences();
    prefs.custom_config_file_name = name.to_string();
    prefs
}

child_test! {
    // Go: customconfigfilename_test.go:28 TestCustomConfigFileName/picks up custom config and switches on preference change
    fn picks_up_custom_config_and_switches_on_preference_change() {
        let (session, _) = projecttestutil::setup(config_files());

        open(&session, URI, "export const x = 1;");
        let p = program(&session, URI);

        assert_eq!(default_project_name(&session, URI), "/src/tsconfig.json");
        assert_eq!(p.options().strict, Tristate::False);

        session.configure(prefs_with_custom_config("tsconfig.all.json"));

        let p = program(&session, URI);

        assert_eq!(default_project_name(&session, URI), "/src/tsconfig.all.json");
        assert_eq!(p.options().strict, Tristate::True);
    }
}

child_test! {
    // Go: customconfigfilename_test.go:52 TestCustomConfigFileName/uses tsconfig.json when customConfigFileName is empty
    fn uses_tsconfig_json_when_custom_config_file_name_is_empty() {
        let (session, _) = projecttestutil::setup(config_files());

        let prefs = lsutil::new_default_user_preferences();
        // default for CustomConfigFileName is "".
        assert_eq!(prefs.custom_config_file_name, "");
        session.configure(prefs);

        open(&session, URI, "export const x = 1;");
        let _ = language_service(&session, URI);

        assert_eq!(default_project_name(&session, URI), "/src/tsconfig.json");
    }
}

child_test! {
    // Go: customconfigfilename_test.go:69 TestCustomConfigFileName/falls back to tsconfig.json when custom config missing
    fn falls_back_to_tsconfig_json_when_custom_config_missing() {
        let (session, _) = projecttestutil::setup(config_files());

        session.configure(prefs_with_custom_config("tsconfig.nonexistent.json"));

        open(&session, URI, "export const x = 1;");
        let _ = language_service(&session, URI);

        assert_eq!(default_project_name(&session, URI), "/src/tsconfig.json");
    }
}

child_test! {
    // Go: customconfigfilename_test.go:85 TestCustomConfigFileName/reverts to tsconfig.json when custom config preference is cleared
    fn reverts_to_tsconfig_json_when_custom_config_preference_is_cleared() {
        let (session, _) = projecttestutil::setup(config_files());

        // Step 1: Open file, verify it uses tsconfig.json (strict: false)
        open(&session, URI, "export const x = 1;");
        let p = program(&session, URI);

        assert_eq!(default_project_name(&session, URI), "/src/tsconfig.json");
        assert_eq!(p.options().strict, Tristate::False);

        // Step 2: Switch to custom config (strict: true)
        session.configure(prefs_with_custom_config("tsconfig.all.json"));

        let p = program(&session, URI);

        assert_eq!(default_project_name(&session, URI), "/src/tsconfig.all.json");
        assert_eq!(p.options().strict, Tristate::True);

        // Step 3: Clear custom config preference, should revert to tsconfig.json (strict: false)
        session.configure(prefs_with_custom_config(""));

        let p = program(&session, URI);

        assert_eq!(default_project_name(&session, URI), "/src/tsconfig.json");
        assert_eq!(p.options().strict, Tristate::False);
    }
}

child_test! {
    // Go: customconfigfilename_test.go:126 TestCustomConfigFileName/schedules diagnostics refresh when custom config preference changes
    #[ignore = "bug: S4-001 flaky: WaitForBackgroundTasks can return before the debounced RefreshDiagnostics runs"]
    fn schedules_diagnostics_refresh_when_custom_config_preference_changes() {
        let (session, utils) = projecttestutil::setup(config_files());

        open(&session, URI, "export const x = 1;");
        let _ = language_service(&session, URI);
        session.wait_for_background_tasks();

        // Record baseline refresh call count
        let baseline_refresh_count = utils.client().refresh_diagnostics_calls();

        // Change the custom config preference
        session.configure(prefs_with_custom_config("tsconfig.all.json"));

        // GetLanguageService triggers the snapshot update with the new config
        let _ = language_service(&session, URI);
        session.wait_for_background_tasks();

        // The server should have scheduled a diagnostics refresh to tell the client
        // to re-pull diagnostics with the new project configuration.
        let refresh_count = utils.client().refresh_diagnostics_calls();
        assert!(
            refresh_count > baseline_refresh_count,
            "expected RefreshDiagnostics to be called after customConfigFileName change, got {refresh_count} calls (baseline {baseline_refresh_count})"
        );
    }
}

/// Go `lsutil.ParseUserPreferences(map[string]any{"js/ts": {"customConfigFileName": name}})`.
fn parse_custom_config_file_name(name: &str) -> lsutil::UserPreferences {
    let mut items = indexmap::IndexMap::new();
    items.insert(
        "js/ts".to_string(),
        lsp_object(vec![(
            "customConfigFileName",
            LspAny::String(name.to_string()),
        )]),
    );
    lsutil::parse_user_preferences(&items)
}

// Go: customconfigfilename_test.go:156 TestCustomConfigFileName/rejects path traversal in customConfigFileName
#[test]
fn rejects_path_traversal_in_custom_config_file_name() {
    for invalid_name in [
        "/etc/passwd",
        "../tsconfig.json",
        "configs/tsconfig.all.json",
        "..\\tsconfig.json",
        "sub\\dir\\tsconfig.json",
        "..",
        ".",
    ] {
        let prefs = parse_custom_config_file_name(invalid_name);
        assert_eq!(
            prefs.custom_config_file_name, "",
            "expected customConfigFileName to be cleared for invalid value {invalid_name:?}"
        );
    }
}

// Go: customconfigfilename_test.go:177 TestCustomConfigFileName/accepts plain base file names in customConfigFileName
#[test]
fn accepts_plain_base_file_names_in_custom_config_file_name() {
    for valid_name in [
        "tsconfig.all.json",
        "tsconfig.editor.json",
        "jsconfig.custom.json",
    ] {
        let prefs = parse_custom_config_file_name(valid_name);
        assert_eq!(
            prefs.custom_config_file_name, valid_name,
            "expected customConfigFileName to be {valid_name:?}"
        );
    }
}

child_test! {
    // Go: customconfigfilename_test.go:194 TestCustomConfigFileName/cleans up inferred project when custom config covers file
    fn cleans_up_inferred_project_when_custom_config_covers_file() {
        let files_no_config = files(&[
            (
                "/src/tsconfig.all.json",
                r#"{"compilerOptions": {"strict": true}, "include": ["./**/*"]}"#,
            ),
            ("/src/index.ts", "export const x = 1;"),
        ]);
        let (session, _) = projecttestutil::setup(files_no_config);

        open(&session, URI, "export const x = 1;");
        let _ = language_service(&session, URI);

        // Without any config, the file should be in the inferred project only.
        assert_eq!(default_project_name(&session, URI), "/dev/null/inferred");
        let projects = session.snapshot().get_projects_containing_file(&uri(URI));
        assert_eq!(
            projects.len(),
            1,
            "expected file to be in exactly 1 project before config change, got {}",
            projects.len()
        );

        // Now set custom config to pick up tsconfig.all.json
        session.configure(prefs_with_custom_config("tsconfig.all.json"));

        let _ = language_service(&session, URI);

        // File should now be in the configured project only, not duplicated in inferred.
        assert_eq!(default_project_name(&session, URI), "/src/tsconfig.all.json");
        let projects = session.snapshot().get_projects_containing_file(&uri(URI));
        assert_eq!(
            projects.len(),
            1,
            "expected file to be in exactly 1 project after config change, got {}",
            projects.len()
        );
    }
}
