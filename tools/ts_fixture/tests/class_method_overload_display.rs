use std::{collections::BTreeMap, env, fs, path::PathBuf};

use ts_fixture::{
    Case, OptionVariant, RunnerOptions, expand_option_matrix, run_upstream_diagnostic_baselines,
};

#[test]
fn original_ambiguous_calls_match_complete_diagnostic_type_and_symbol_artifacts() {
    let repository = PathBuf::from(
        env::var_os("TS_GO_REPO")
            .expect("TS_GO_REPO must point to the pinned typescript-go checkout"),
    );
    let relative_case =
        "_submodules/TypeScript/tests/cases/compiler/ambiguousCallsWhereReturnTypesAgree.ts";
    let case_path = repository.join(relative_case);
    let case = Case::parse(&case_path, fs::read(&case_path).unwrap()).unwrap();
    assert_eq!(case.units.len(), 1);
    assert_eq!(case.directives.len(), 1);
    assert_eq!(
        expand_option_matrix(&case),
        [OptionVariant {
            values: BTreeMap::from([("target".to_owned(), "es2015".to_owned())]),
            ..OptionVariant::default()
        }]
    );

    let baseline_root = repository.join("testdata/baselines/reference/submodule/compiler");
    for extension in ["types", "symbols"] {
        let baseline =
            baseline_root.join(format!("ambiguousCallsWhereReturnTypesAgree.{extension}"));
        assert!(
            baseline.is_file(),
            "the original baseline is required: {}",
            baseline.display()
        );
    }
    // The pinned case expects an empty diagnostic artifact and both semantic artifacts.
    assert!(
        !baseline_root
            .join("ambiguousCallsWhereReturnTypesAgree.errors.txt")
            .try_exists()
            .unwrap()
    );

    let mut output = Vec::new();
    let summary = run_upstream_diagnostic_baselines(
        &repository,
        &RunnerOptions {
            filter: Some(relative_case.to_owned()),
            diagnostics: true,
            canonical_checker: true,
            semantic_artifacts: true,
            ..RunnerOptions::default()
        },
        &mut output,
    )
    .unwrap();
    let output = String::from_utf8(output).unwrap();
    assert_eq!(summary.selected_cases, 1, "{output}");
    assert_eq!(summary.executed_variants, 1, "{output}");
    assert_eq!(summary.upstream_skipped_variants, 0, "{output}");
    assert_eq!(summary.matched, 1, "{output}");
    assert_eq!(summary.diagnostic_failures, 0, "{output}");
    assert!(summary.is_success(), "{output}");
}
