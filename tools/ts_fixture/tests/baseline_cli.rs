use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct TestRepository(PathBuf);

impl TestRepository {
    fn new() -> Self {
        let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("ts-fixture-cli-{}-{sequence}", std::process::id()));
        let _ = fs::remove_dir_all(&path);
        for directory in [
            "testdata/tests/cases/compiler",
            "testdata/tests/cases/conformance",
            "testdata/baselines/reference/compiler",
            "testdata/baselines/reference/conformance",
            "_submodules/TypeScript/tests/cases/compiler",
            "_submodules/TypeScript/tests/cases/conformance",
            "testdata/baselines/reference/submodule/compiler",
            "testdata/baselines/reference/submodule/conformance",
        ] {
            fs::create_dir_all(path.join(directory)).unwrap();
        }
        Self(path)
    }

    fn write_case(&self, name: &str, source: &str, baseline: Option<&str>) {
        fs::write(
            self.0
                .join("testdata/tests/cases/compiler")
                .join(format!("{name}.ts")),
            source,
        )
        .unwrap();
        if let Some(baseline) = baseline {
            fs::write(
                self.0
                    .join("testdata/baselines/reference/compiler")
                    .join(format!("{name}.js")),
                baseline,
            )
            .unwrap();
        }
    }

    fn write_baseline(&self, file_name: &str, baseline: &str) {
        fs::write(
            self.0
                .join("testdata/baselines/reference/compiler")
                .join(file_name),
            baseline,
        )
        .unwrap();
    }
}

impl Drop for TestRepository {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn run(repository: &Path, arguments: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_ts_fixture_baseline"))
        .args(arguments)
        .env("TS_GO_REPO", repository)
        .output()
        .unwrap()
}

#[test]
fn filters_limits_and_reports_matches() {
    let repository = TestRepository::new();
    repository.write_case(
        "matching",
        "// @target: esnext\n// @module: esnext\n// @noLib: true\nconst value: number = 1;\n",
        Some("//// [matching.js] ////\n\"use strict\";\nconst value = 1;\n"),
    );
    repository.write_case("ignored", "// @noLib: true\nconst ignored = 1;\n", None);
    let output = run(&repository.0, &["--filter", "matching", "--limit", "1"]);
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "summary: discovered_cases=2 upstream_skipped_cases=0 selected_cases=1 executed_variants=1 matched=1 mismatched=0 missing=0 content=0 missing_sections=0 unexpected_sections=0 diagnostics=0\n"
    );
}

#[test]
fn manifest_is_deterministic_and_excludes_unrelated_suites() {
    let repository = TestRepository::new();
    repository.write_case("zeta", "// @noLib: true\nconst zeta = 1;\n", None);
    repository.write_case(
        "APILibCheck",
        "// This basename is skipped by the pinned Go runner.\n",
        None,
    );
    repository.write_case("alpha", "// @noLib: true\nconst alpha = 1;\n", None);
    repository.write_baseline("alpha.errors.txt", "error baseline\n");
    repository.write_baseline("alpha.types", "type baseline\n");
    repository.write_baseline("alpha.symbols", "symbol baseline\n");
    repository.write_baseline("alpha.js", "emit baseline\n");

    let unrelated = repository.0.join("testdata/baselines/reference/fourslash");
    fs::create_dir_all(&unrelated).unwrap();
    fs::write(
        unrelated.join("alpha.errors.txt"),
        "not a compiler oracle\n",
    )
    .unwrap();
    fs::write(
        repository
            .0
            .join("testdata/tests/cases/compiler/not-a-fixture.js"),
        "const ignored = true;\n",
    )
    .unwrap();

    let output = run(&repository.0, &["--manifest"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        concat!(
            "oracle-manifest\t1\n",
            "suite\tgo\tcompiler\tcases=3\trunnable=2\tupstream_skipped=1\terrors=1\ttypes=1\tsymbols=1\temit=1\tcase_root=testdata/tests/cases/compiler\toracle_root=testdata/baselines/reference/compiler\n",
            "case\tgo\tcompiler\tupstream-skip\ttestdata/tests/cases/compiler/APILibCheck.ts\n",
            "case\tgo\tcompiler\trunnable\ttestdata/tests/cases/compiler/alpha.ts\n",
            "case\tgo\tcompiler\trunnable\ttestdata/tests/cases/compiler/zeta.ts\n",
            "suite\tgo\tconformance\tcases=0\trunnable=0\tupstream_skipped=0\terrors=0\ttypes=0\tsymbols=0\temit=0\tcase_root=testdata/tests/cases/conformance\toracle_root=testdata/baselines/reference/conformance\n",
            "suite\tsubmodule\tcompiler\tcases=0\trunnable=0\tupstream_skipped=0\terrors=0\ttypes=0\tsymbols=0\temit=0\tcase_root=_submodules/TypeScript/tests/cases/compiler\toracle_root=testdata/baselines/reference/submodule/compiler\n",
            "suite\tsubmodule\tconformance\tcases=0\trunnable=0\tupstream_skipped=0\terrors=0\ttypes=0\tsymbols=0\temit=0\tcase_root=_submodules/TypeScript/tests/cases/conformance\toracle_root=testdata/baselines/reference/submodule/conformance\n",
            "manifest-summary: suites=4 discovered_cases=3 runnable_cases=2 upstream_skipped_cases=1 errors=1 types=1 symbols=1 emit=1\n",
        )
    );
}

#[test]
fn explicit_run_fails_when_a_required_oracle_root_is_missing() {
    let repository = TestRepository::new();
    fs::remove_dir_all(
        repository
            .0
            .join("testdata/baselines/reference/submodule/conformance"),
    )
    .unwrap();

    let output = run(&repository.0, &["--manifest"]);
    assert_eq!(output.status.code(), Some(2));
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("incomplete typescript-go compiler oracle"));
    assert!(stderr.contains("oracle"));
    assert!(stderr.contains("reference/submodule/conformance"));
}

#[test]
fn upstream_skips_are_visible_but_never_executed() {
    let repository = TestRepository::new();
    repository.write_case(
        "APILibCheck",
        "const deliberatelyInvalid: string = 1;\n",
        None,
    );

    let output = run(&repository.0, &["--diagnostics"]);
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "summary: discovered_cases=1 upstream_skipped_cases=1 selected_cases=0 executed_variants=0 matched=0 mismatched=0 missing=0 content=0 missing_sections=0 unexpected_sections=0 diagnostics=0 diagnostic_comparison=header-only exact_matches=0 header_only_matches=0 header_mismatches=0\n"
    );
}

#[test]
fn compares_diagnostic_headers_without_changing_emit_mode() {
    let repository = TestRepository::new();
    repository.write_case(
        "diagnosticParity",
        concat!(
            "// @noLib: true\n",
            "// @noEmit: true\n",
            "const value: string = 1;\n",
        ),
        None,
    );
    repository.write_baseline(
        "diagnosticParity.errors.txt",
        concat!(
            "diagnosticParity.ts(1,7): error TS2322: Type 'number' is not assignable to type 'string'.\r\n",
            "\r\n",
            "\r\n",
            "==== diagnosticParity.ts (1 errors) ====\r\n",
        ),
    );

    let output = run(
        &repository.0,
        &["--diagnostics", "--filter", "diagnosticParity"],
    );
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "summary: discovered_cases=1 upstream_skipped_cases=0 selected_cases=1 executed_variants=1 matched=1 mismatched=0 missing=0 content=0 missing_sections=0 unexpected_sections=0 diagnostics=0 diagnostic_comparison=header-only exact_matches=0 header_only_matches=1 header_mismatches=0\n"
    );
}

#[test]
fn writes_deterministic_structured_header_only_scorecard() {
    let repository = TestRepository::new();
    repository.write_case(
        "aHeaderMatch",
        "// @noLib: true\nconst value: string = 1;\n",
        None,
    );
    repository.write_baseline(
        "aHeaderMatch.errors.txt",
        concat!(
            "aHeaderMatch.ts(1,7): error TS2322: Type 'number' is not assignable to type 'string'.\n",
            "\n",
            "==== aHeaderMatch.ts (1 errors) ====\n",
        ),
    );
    repository.write_case(
        "bHeaderMismatch",
        "// @noLib: true\nconst value: string = 1;\n",
        None,
    );
    repository.write_baseline(
        "bHeaderMismatch.errors.txt",
        "bHeaderMismatch.ts(1,7): error TS9999: deliberately wrong\n",
    );

    let first_path = repository.0.join("scorecard-first.json");
    let first = run(
        &repository.0,
        &[
            "--diagnostics",
            "--scorecard-json",
            first_path.to_str().unwrap(),
        ],
    );
    assert_eq!(first.status.code(), Some(1));
    let first_json = fs::read_to_string(&first_path).unwrap();

    let second_path = repository.0.join("scorecard-second.json");
    let second = run(
        &repository.0,
        &[
            "--diagnostics",
            "--scorecard-json",
            second_path.to_str().unwrap(),
        ],
    );
    assert_eq!(second.status.code(), Some(1));
    assert_eq!(first_json, fs::read_to_string(second_path).unwrap());

    let scorecard: serde_json::Value = serde_json::from_str(&first_json).unwrap();
    assert_eq!(scorecard["schemaVersion"], 1);
    assert_eq!(scorecard["comparisonScope"], "header_only");
    assert_eq!(scorecard["fullArtifactComparison"], false);
    assert_eq!(scorecard["summary"]["executedVariants"], 2);
    assert_eq!(scorecard["summary"]["exactMatches"], 0);
    assert_eq!(scorecard["summary"]["headerOnlyMatches"], 1);
    assert_eq!(scorecard["summary"]["headerMismatches"], 1);
    assert_eq!(scorecard["summary"]["actualDiagnostics"], 2);

    let variants = scorecard["variants"].as_array().unwrap();
    assert_eq!(
        variants[0]["case"],
        "testdata/tests/cases/compiler/aHeaderMatch.ts"
    );
    assert_eq!(variants[0]["status"], "header_only_match");
    assert_eq!(variants[0]["comparisonScope"], "header_only");
    assert_eq!(
        variants[0]["expectedBaseline"],
        "testdata/baselines/reference/compiler/aHeaderMatch.errors.txt"
    );
    assert_eq!(variants[1]["status"], "header_mismatch");

    let diagnostic = &variants[0]["diagnostics"][0];
    assert_eq!(diagnostic["fileName"], "/case/aHeaderMatch.ts");
    assert_eq!(diagnostic["range"]["start"], 6);
    assert_eq!(diagnostic["range"]["length"], 17);
    assert_eq!(diagnostic["code"], 2322);
    assert_eq!(diagnostic["category"], "error");
    assert_eq!(
        diagnostic["message"],
        "Type 'number' is not assignable to type 'string'."
    );
}

#[test]
fn diagnostics_mode_treats_a_missing_error_baseline_as_no_expected_errors() {
    let repository = TestRepository::new();
    repository.write_case(
        "unexpectedDiagnostic",
        "// @noLib: true\nconst value: string = 1;\n",
        None,
    );

    let output = run(
        &repository.0,
        &["--diagnostics", "--filter", "unexpectedDiagnostic"],
    );
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("MISMATCH testdata/tests/cases/compiler/unexpectedDiagnostic.ts"));
    assert!(stdout.contains("expected \"\""));
    assert!(stdout.contains("actual \"unexpectedDiagnostic.ts(1,7): error TS2322"));
    assert!(stdout.contains("matched=0 mismatched=1"));
    assert!(stdout.contains("diagnostics=1"));
}

#[test]
fn reports_the_first_actionable_mismatch() {
    let repository = TestRepository::new();
    repository.write_case(
        "mismatch",
        "// @target: esnext\n// @module: esnext\n// @noLib: true\nconst value: number = 1;\n",
        Some("//// [mismatch.js] ////\n\"use strict\";\nconst value = 2;\n"),
    );
    let output = run(&repository.0, &[]);
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("MISMATCH testdata/tests/cases/compiler/mismatch.ts"));
    assert!(stdout.contains("differs at line 2"));
    assert!(stdout.contains("expected \"const value = 2;\""));
    assert!(stdout.contains("actual \"const value = 1;\""));
    assert!(stdout.contains(
        "discovered_cases=1 upstream_skipped_cases=0 selected_cases=1 executed_variants=1 matched=0 mismatched=1 missing=0 content=1 missing_sections=0 unexpected_sections=0 diagnostics=0"
    ));
}

#[test]
fn reports_missing_baselines() {
    let repository = TestRepository::new();
    repository.write_case("missing", "// @noLib: true\nconst value = 1;\n", None);
    let output = run(&repository.0, &[]);
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("MISSING testdata/tests/cases/compiler/missing.ts"));
    assert!(stdout.contains(
        "discovered_cases=1 upstream_skipped_cases=0 selected_cases=1 executed_variants=1 matched=0 mismatched=0 missing=1 content=0 missing_sections=0 unexpected_sections=0 diagnostics=0"
    ));
}

#[test]
fn accepts_a_missing_emit_baseline_when_virtual_project_disables_emit() {
    let repository = TestRepository::new();
    repository.write_case(
        "projectNoEmit",
        concat!(
            "// @target: es2015\n",
            "// @filename: /packages/main/tsconfig.json\n",
            "{ \"compilerOptions\": { \"noEmit\": true } }\n",
            "// @filename: /packages/main/index.ts\n",
            "const value = 1;\n",
        ),
        None,
    );

    let output = run(&repository.0, &["--filter", "projectNoEmit"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "summary: discovered_cases=1 upstream_skipped_cases=0 selected_cases=1 executed_variants=1 matched=1 mismatched=0 missing=0 content=0 missing_sections=0 unexpected_sections=0 diagnostics=0\n"
    );
}

#[test]
fn compiles_and_matches_option_variants() {
    let repository = TestRepository::new();
    repository.write_case(
        "matrix",
        "// @target: es5, esnext\n// @module: esnext\n// @noLib: true\nconst value = 1;\n",
        None,
    );
    repository.write_baseline(
        "matrix(target=es5).js",
        "//// [matrix.js] ////\n\"use strict\";\nvar value = 1;\n",
    );
    repository.write_baseline(
        "matrix(target=esnext).js",
        "//// [matrix.js] ////\n\"use strict\";\nconst value = 1;\n",
    );
    let output = run(&repository.0, &[]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "summary: discovered_cases=1 upstream_skipped_cases=0 selected_cases=1 executed_variants=2 matched=2 mismatched=0 missing=0 content=0 missing_sections=0 unexpected_sections=0 diagnostics=0\n"
    );
}

#[test]
fn reports_compilation_diagnostic_for_missing_emitted_section() {
    let repository = TestRepository::new();
    repository.write_case(
        "diagnostic",
        concat!(
            "// @noLib: true\n",
            "// @noEmitOnError: true\n",
            "const value: string = 1;\n",
        ),
        Some("//// [diagnostic.js] ////\nvar value = 1;\n"),
    );
    let output = run(&repository.0, &[]);
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains("MISMATCH testdata/tests/cases/compiler/diagnostic.ts: diagnostic TS2322")
    );
    assert!(stdout.contains("/case/diagnostic.ts"));
    assert!(stdout.contains("Type 'number' is not assignable to type 'string'."));
    assert!(stdout.contains(
        "matched=0 mismatched=1 missing=0 content=0 missing_sections=0 unexpected_sections=0 diagnostics=1"
    ));
}

#[test]
fn reports_output_mismatch_after_delete_expression_support() {
    let repository = TestRepository::new();
    repository.write_case(
        "unsupported",
        concat!(
            "// @noLib: true\n",
            "// @target: es2015\n",
            "const value = {};\n",
            "delete value.missing;\n",
        ),
        Some("//// [unsupported.js] ////\nvar N;\n"),
    );
    let output = run(&repository.0, &[]);
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("MISMATCH testdata/tests/cases/compiler/unsupported.ts"));
    assert!(stdout.contains("section unsupported.js differs at line 1"));
    assert!(stdout.contains("diagnostics=0"));
}

#[test]
fn counts_missing_and_unexpected_output_sections() {
    let repository = TestRepository::new();
    repository.write_case(
        "missingSection",
        "// @noEmit: true\nconst value = 1;\n",
        Some("//// [missingSection.js] ////\nvar value = 1;\n"),
    );
    let missing = run(&repository.0, &["--filter", "missingSection"]);
    assert_eq!(missing.status.code(), Some(1));
    assert!(
        String::from_utf8(missing.stdout)
            .unwrap()
            .contains("content=0 missing_sections=1 unexpected_sections=0 diagnostics=0")
    );

    repository.write_case(
        "unexpectedSection",
        "// @declaration: true\n// @target: es5\nconst value = 1;\n",
        Some("//// [unexpectedSection.js] ////\n\"use strict\";\nvar value = 1;\n"),
    );
    let unexpected = run(&repository.0, &["--filter", "unexpectedSection"]);
    assert_eq!(unexpected.status.code(), Some(1));
    assert!(
        String::from_utf8(unexpected.stdout)
            .unwrap()
            .contains("content=0 missing_sections=0 unexpected_sections=1 diagnostics=0")
    );
}
