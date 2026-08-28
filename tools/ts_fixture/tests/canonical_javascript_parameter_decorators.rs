use std::{env, path::Path};

use ts_fixture::{RunnerOptions, run_upstream_diagnostic_baselines};

#[test]
fn original_javascript_parameter_decorator_variants_match_full_error_artifacts() {
    let Ok(repository) = env::var("TS_GO_REPO") else {
        return;
    };
    let options = RunnerOptions {
        diagnostics: true,
        canonical_checker: true,
        filter: Some("testdata/tests/cases/compiler/parameterDecoratorInJsFile.ts".to_owned()),
        ..RunnerOptions::default()
    };
    let mut output = Vec::new();
    let summary = run_upstream_diagnostic_baselines(Path::new(&repository), &options, &mut output)
        .unwrap_or_else(|error| {
            panic!("the original parameter decorator fixture must run: {error}")
        });
    assert_eq!(summary.selected_cases, 1);
    assert_eq!(summary.executed_variants, 2);
    assert_eq!(summary.matched, 2, "{}", String::from_utf8_lossy(&output));
    assert!(summary.is_success(), "{}", String::from_utf8_lossy(&output));
}
