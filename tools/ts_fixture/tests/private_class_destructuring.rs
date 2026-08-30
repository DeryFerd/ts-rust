use std::{collections::BTreeMap, env, fs, path::PathBuf};

use ts_fixture::{
    Case, OptionVariant, RunnerOptions, expand_option_matrix, parse_error_baseline_header,
    run_upstream_diagnostic_baselines,
};

#[test]
fn original_private_class_destructuring_matches_complete_diagnostic_artifact() {
    let repository = PathBuf::from(
        env::var_os("TS_GO_REPO")
            .expect("TS_GO_REPO must point to the pinned typescript-go checkout"),
    );
    let relative_case = "testdata/tests/cases/compiler/privateIdentifierPropertyAccessDestructuringAssignmentES6.ts";
    let case_path = repository.join(relative_case);
    let case = Case::parse(&case_path, fs::read(&case_path).unwrap()).unwrap();
    assert_eq!(
        case.units
            .iter()
            .map(|unit| unit.path.to_str().unwrap())
            .collect::<Vec<_>>(),
        [
            "/privateIdentifierPropertyAccessDestructuringAssignmentES6.ts",
            "/node_modules/tslib/package.json",
            "/node_modules/tslib/tslib.d.ts",
            "/node_modules/tslib/tslib.js",
        ]
    );
    assert_eq!(case.directives.len(), 8);
    assert_eq!(
        case.directive_values("noTypesAndSymbols")
            .collect::<Vec<_>>(),
        ["true"]
    );
    assert_eq!(
        expand_option_matrix(&case),
        [OptionVariant {
            values: BTreeMap::from([
                ("importHelpers".to_owned(), "true".to_owned()),
                ("module".to_owned(), "commonjs".to_owned()),
                ("target".to_owned(), "es6".to_owned()),
            ]),
            ..OptionVariant::default()
        }]
    );

    let baseline = fs::read_to_string(repository.join(
        "testdata/baselines/reference/compiler/privateIdentifierPropertyAccessDestructuringAssignmentES6.errors.txt",
    ))
    .unwrap();
    let header = parse_error_baseline_header(&baseline);
    assert!(header.contains("error TS6504:"));
    assert!(header.contains("error TS2343:"));

    // Compare the complete original artifact, including all four source sections.
    let mut output = Vec::new();
    let summary = run_upstream_diagnostic_baselines(
        &repository,
        &RunnerOptions {
            filter: Some(relative_case.to_owned()),
            diagnostics: true,
            canonical_checker: true,
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
