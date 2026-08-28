use std::{env, path::Path};

use ts_fixture::{RunnerOptions, run_upstream_diagnostic_baselines};

fn assert_original_augmentation_artifacts(case: &str) {
    let Ok(repository) = env::var("TS_GO_REPO") else {
        return;
    };
    let options = RunnerOptions {
        diagnostics: true,
        canonical_checker: true,
        semantic_artifacts: true,
        filter: Some(case.to_owned()),
        limit: Some(1),
        ..RunnerOptions::default()
    };
    let mut output = Vec::new();
    let summary = run_upstream_diagnostic_baselines(Path::new(&repository), &options, &mut output)
        .unwrap_or_else(|error| panic!("the original augmentation fixture must run: {error}"));
    assert_eq!(summary.selected_cases, 1);
    assert_eq!(summary.executed_variants, 1);
    assert_eq!(summary.matched, 1, "{}", String::from_utf8_lossy(&output));
    assert!(summary.is_success(), "{}", String::from_utf8_lossy(&output));
}

#[test]
fn canonical_reexported_interface_augmentation_matches_all_artifacts() {
    assert_original_augmentation_artifacts("moduleAugmentationDoesInterfaceMergeOfReexport.ts");
}

#[test]
fn canonical_reexported_enum_class_collision_matches_all_artifacts() {
    assert_original_augmentation_artifacts("moduleAugmentationEnumClassMergeOfReexportIsError.ts");
}
