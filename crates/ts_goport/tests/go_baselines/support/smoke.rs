//! Harness smoke test of the tsc runner (unit U05): two Go inputs copied
//! as they are, one `tsc -b` build and one incremental `tsc` with an edit.
//! Both must match the reference baselines before the scenario ports run.

use crate::support::runner::{
    TscEdit, TscInput, WatchFilter, args, check_results, edit, file_map, no_change,
    run_tsc_input_results,
};
use crate::support::stringtestutil::dedent;

// Go: tscbuild_test.go:300 TestBuildClean, input "tsx with dts emit"
fn build_clean_tsx_with_dts_emit() -> TscInput {
    TscInput {
        sub_scenario: "tsx with dts emit".to_string(),
        files: file_map! {
            "/home/src/workspaces/solution/project/src/main.tsx" => "export const x = 10;",
            "/home/src/workspaces/solution/project/tsconfig.json" => dedent(r#"
				{
					"compilerOptions": { "declaration": true },
					"include": ["src/**/*.tsx", "src/**/*.ts"]
				}"#),
        },
        cwd: "/home/src/workspaces/solution".to_string(),
        command_line_args: args!["--b", "project", "-v", "--explainFiles"],
        edits: vec![
            no_change(),
            TscEdit {
                caption: "clean build".to_string(),
                command_line_args: Some(args!["-b", "project", "--clean"]),
                ..TscEdit::default()
            },
        ],
        ..TscInput::default()
    }
}

// Go: tsc_test.go:300 TestTscComposite, input "converting to modules"
fn tsc_composite_converting_to_modules() -> TscInput {
    TscInput {
        sub_scenario: "converting to modules".to_string(),
        files: file_map! {
            "/home/src/workspaces/project/src/main.ts" => "const x = 10;",
            "/home/src/workspaces/project/tsconfig.json" => dedent(r#"
				{
					"compilerOptions": {
						"module": "none",
						"composite": true,
					},
				}"#),
        },
        edits: vec![TscEdit {
            caption: "convert to modules".to_string(),
            edit: edit(|sys| {
                sys.replace_file_text(
                    "/home/src/workspaces/project/tsconfig.json",
                    "none",
                    "es2015",
                );
            }),
            ..TscEdit::default()
        }],
        ..TscInput::default()
    }
}

/// Runs both inputs (scenarios "clean" and "composite") and fails once
/// with every difference.
#[test]
fn harness_smoke() {
    let mut results = run_tsc_input_results(
        "clean",
        vec![build_clean_tsx_with_dts_emit()],
        WatchFilter::NonWatch,
    );
    results.extend(run_tsc_input_results(
        "composite",
        vec![tsc_composite_converting_to_modules()],
        WatchFilter::NonWatch,
    ));
    check_results("harness_smoke", &results);
}
