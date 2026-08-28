use std::{env, path::Path};

use ts_fixture::{RunnerOptions, run_upstream_diagnostic_baselines};

#[test]
fn class_side_inheritance_three_matches_the_full_original_error_artifact() {
    let Ok(repository) = env::var("TS_GO_REPO") else {
        return;
    };
    let options = RunnerOptions {
        diagnostics: true,
        canonical_checker: true,
        filter: Some(
            "_submodules/TypeScript/tests/cases/compiler/classSideInheritance3.ts".to_owned(),
        ),
        ..RunnerOptions::default()
    };
    let mut output = Vec::new();
    let summary =
        run_upstream_diagnostic_baselines(Path::new(&repository), &options, &mut output).unwrap();
    assert_eq!(summary.selected_cases, 1);
    assert_eq!(summary.executed_variants, 1);
    assert_eq!(summary.matched, 1, "{}", String::from_utf8_lossy(&output));
    assert!(summary.is_success(), "{}", String::from_utf8_lossy(&output));
}
