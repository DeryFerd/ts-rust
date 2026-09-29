//! Port of the typescript-go `internal/execute/tsctests/tscbuild_test.go`
//! content mapper tests (tsgo#4712): `TestBuildContentMapperIdentity` and
//! `TestBuildContentMapperOptionDiagnostics`.
//!
//! PORT: Go backtick literals in `stringtestutil.Dedent` keep their relative
//! indentation here (a Go tab is 4 spaces after `Dedent`).

use crate::support::contentmappertest;
use crate::support::runner::{
    FileMap, TscEdit, TscInput, WatchFilter, edit, no_change, run_tsc_inputs,
};
use crate::support::stringtestutil::dedent;
use crate::support::vfstest::MapFile;

/// Go `FileMap{path: value, ...}`. Each value goes through `MapFile::from`.
macro_rules! files {
    ($($path:expr => $value:expr),* $(,)?) => {{
        let mut map = FileMap::new();
        $(map.insert(String::from($path), MapFile::from($value));)*
        map
    }};
}

/// Go `[]string{...}`.
fn argv(args: &[&str]) -> Vec<String> {
    args.iter().map(std::string::ToString::to_string).collect()
}

// Go: tscbuild_test.go:301 TestBuildContentMapperIdentity
#[test]
fn build_content_mapper_identity() {
    let inputs = vec![TscInput {
        sub_scenario: "content mapper identity change forces rebuild".to_string(),
        files: files! {
            "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
            {
                "compilerOptions": {
                    "incremental": true
                },
                "contentMappers": [
                    { "package": "vue-ts-mapper", "extensions": [".vue"] }
                ]
            }"#),
            "/home/src/workspaces/project/index.ts" => "export const local = 1;",
            "/home/src/workspaces/project/app.vue" => "export const app = 1;",
            "/home/src/workspaces/project/node_modules/vue-ts-mapper/package.json" => dedent(r#"
            {
                "name": "vue-ts-mapper",
                "version": "1.0.0",
                "typescript": { "contentMapper": { "exec": ["verbatim-mapper"] } }
            }"#),
        },
        command_line_args: argv(&["--build", "--verbose", "--runExternalCode"]),
        edits: vec![
            no_change(),
            TscEdit {
                caption: "upgrade the content mapper package to a new version".to_string(),
                edit: edit(|sys| {
                    sys.replace_file_text(
                        "/home/src/workspaces/project/node_modules/vue-ts-mapper/package.json",
                        r#""version": "1.0.0""#,
                        r#""version": "2.0.0""#,
                    );
                }),
                ..Default::default()
            },
            no_change(),
        ],
        ..Default::default()
    }];
    run_tsc_inputs("contentMapperIdentity", inputs, WatchFilter::NonWatch);
}

// Go: tscbuild_test.go:347 TestBuildContentMapperOptionDiagnostics
#[test]
fn build_content_mapper_option_diagnostics() {
    // Verify that mapper option diagnostics are represented by the standard build
    // info errors flag and are reported again when that flag triggers a rebuild.
    let inputs = vec![TscInput {
        sub_scenario: "rebuild to report mapper option diagnostics".to_string(),
        files: files! {
            "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
            {
                "compilerOptions": { "incremental": true, "noCheck": true },
                "contentMappers": [
                    {
                        "package": "mapper",
                        "extensions": [".vue"],
                        "options": { "plugins": [{ "name": 1 }] }
                    }
                ]
            }"#),
            "/home/src/workspaces/project/app.vue" => "export const value = 1;",
            "/home/src/workspaces/project/node_modules/mapper/package.json" =>
                contentmappertest::package_json(contentmappertest::VERBATIM_MAPPER),
        },
        command_line_args: argv(&[
            "--build",
            "--verbose",
            "--runExternalCode",
            "--pretty",
            "false",
        ]),
        edits: vec![no_change()],
        ..Default::default()
    }];
    run_tsc_inputs(
        "contentMapperOptionDiagnostics",
        inputs,
        WatchFilter::NonWatch,
    );
}
