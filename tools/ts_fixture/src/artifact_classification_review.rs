use std::{
    cell::RefCell,
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ts_compiler::CanonicalProgramCheckFailureClass;

use crate::{
    ArtifactRenderError, Case, Compilation, DiagnosticScorecardDiagnostic, FixtureChecker,
    GeneratedSemanticArtifacts, RunnerOptions, RunnerSummary, SemanticArtifactError,
    compile_case_variant, expand_option_matrix, render_error_baseline,
    run_upstream_diagnostic_baselines,
};

#[path = "../tests/support/artifact_review_inputs.rs"]
mod inputs;

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

thread_local! {
    static ARTIFACT_OVERRIDE: RefCell<Option<(SemanticArtifactError, SemanticArtifactError)>> =
        const { RefCell::new(None) };
}

pub(super) fn override_artifacts(mut compilation: Compilation) -> Compilation {
    ARTIFACT_OVERRIDE.with_borrow_mut(|slot| {
        if let Some((types, symbols)) = slot.take() {
            let artifacts = compilation
                .semantic_artifacts
                .as_mut()
                .expect("the mixed-error test must request real artifact generation");
            artifacts.types = Err(types);
            artifacts.symbols = Err(symbols);
        }
    });
    compilation
}

struct ResetOverride;

impl Drop for ResetOverride {
    fn drop(&mut self) {
        ARTIFACT_OVERRIDE.with_borrow_mut(|slot| *slot = None);
    }
}

struct ReviewRepository(PathBuf);

impl ReviewRepository {
    fn new() -> Self {
        let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "ts-fixture-artifact-classification-review-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
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

    fn write_baseline(&self, extension: &str, text: &str) {
        fs::write(
            self.0
                .join("testdata/baselines/reference/compiler")
                .join(format!("review.{extension}")),
            text,
        )
        .unwrap();
    }
}

impl Drop for ReviewRepository {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

struct ReviewRun {
    summary: RunnerSummary,
    scorecard: serde_json::Value,
    output: String,
    generated: GeneratedSemanticArtifacts,
    diagnostics: serde_json::Value,
}

fn retain_output(label: &str, scorecard: &serde_json::Value, output: &str) {
    let Some(directory) = std::env::var_os("TS_ARTIFACT_CLASS_REVIEW_DIR") else {
        return;
    };
    let directory = Path::new(&directory);
    fs::create_dir_all(directory).unwrap();
    fs::write(
        directory.join(format!("{label}.json")),
        serde_json::to_vec_pretty(scorecard).unwrap(),
    )
    .unwrap();
    fs::write(directory.join(format!("{label}.stdout")), output).unwrap();
}

fn run_case(label: &str, source: &str, requested: bool, matching_diagnostics: bool) -> ReviewRun {
    let repository = ReviewRepository::new();
    let path = repository.0.join("testdata/tests/cases/compiler/review.ts");
    fs::write(&path, source).unwrap();
    let case = Case::parse(&path, source).unwrap();
    let variant = expand_option_matrix(&case).remove(0);
    let diagnostics_only = compile_case_variant(
        &case,
        &mut variant.clone(),
        FixtureChecker::Canonical,
        false,
    )
    .unwrap();
    assert!(diagnostics_only.semantic_artifacts.is_none());
    let expected = render_error_baseline(&case, &diagnostics_only.diagnostics).text;
    repository.write_baseline(
        "errors.txt",
        if matching_diagnostics { &expected } else { "" },
    );
    let generated =
        compile_case_variant(&case, &mut variant.clone(), FixtureChecker::Canonical, true)
            .unwrap()
            .semantic_artifacts
            .unwrap();
    for (extension, artifact) in [("types", &generated.types), ("symbols", &generated.symbols)] {
        repository.write_baseline(
            extension,
            artifact.as_deref().unwrap_or("expected artifact\n"),
        );
    }
    let scorecard_path = repository.0.join("scorecard.json");
    let mut output = Vec::new();
    let summary = run_upstream_diagnostic_baselines(
        &repository.0,
        &RunnerOptions {
            diagnostics: true,
            canonical_checker: true,
            semantic_artifacts: requested,
            scorecard_json: Some(scorecard_path.clone()),
            ..RunnerOptions::default()
        },
        &mut output,
    )
    .unwrap();
    let scorecard = serde_json::from_slice(&fs::read(&scorecard_path).unwrap()).unwrap();
    let output = String::from_utf8(output).unwrap();
    retain_output(label, &scorecard, &output);
    ReviewRun {
        summary,
        scorecard,
        output,
        generated,
        diagnostics: serde_json::to_value(
            diagnostics_only
                .diagnostics
                .iter()
                .map(DiagnosticScorecardDiagnostic::from)
                .collect::<Vec<_>>(),
        )
        .unwrap(),
    }
}

fn assert_single_failed_variant(run: &ReviewRun, status: &str, outcome: &str) {
    assert!(!run.summary.is_success(), "{}", run.output);
    assert_eq!(run.summary.executed_variants, 1);
    assert_eq!(run.summary.matched, 0);
    assert_eq!(run.summary.mismatched, 1);
    assert_eq!(run.summary.diagnostic_failures, 1);
    assert_eq!(run.scorecard["summary"]["executedVariants"], 1);
    assert_eq!(run.scorecard["summary"]["exactMatches"], 0);
    assert_eq!(run.scorecard["variants"][0]["status"], status);
    assert_eq!(run.scorecard["variants"][0]["outcomeClass"], outcome);
    assert_eq!(run.scorecard["variants"][0]["diagnostics"], run.diagnostics);
    assert_eq!(
        run.scorecard["summary"]["actualDiagnostics"],
        run.diagnostics.as_array().unwrap().len()
    );
}

fn assert_rendered_namespace_diagnostics(run: &ReviewRun, requested: bool) {
    let types = run.generated.types.as_deref().unwrap();
    assert!(types.contains(">foo : typeof foo\r\n"));
    assert!(types.contains(">items.customMethod() : string\r\n"));
    assert!(!run.generated.symbols.as_deref().unwrap().is_empty());
    assert!(run.summary.is_success(), "{}", run.output);
    assert_eq!(run.summary.executed_variants, 1);
    assert_eq!(run.summary.matched, 1);
    assert_eq!(run.summary.mismatched, 0);
    assert_eq!(run.summary.diagnostic_failures, 0);
    for (field, expected) in [
        ("executedVariants", 1),
        ("exactMatches", 1),
        ("fatalInvariants", 0),
        ("unsupportedDetails", 0),
        ("headerMismatches", 0),
        ("actualDiagnostics", 2),
    ] {
        assert_eq!(run.scorecard["summary"][field], expected, "{field}");
    }
    let result = &run.scorecard["variants"][0];
    assert_eq!(result["status"], "exact_match");
    assert_eq!(result["outcomeClass"], "exact");
    assert!(result["frontierBlocker"].is_null());
    assert!(result["firstDifference"].is_null());
    assert_eq!(result["mismatchKinds"], serde_json::json!([]));
    assert_eq!(result["unsupportedDetails"], serde_json::json!([]));
    assert_eq!(result["diagnostics"], run.diagnostics);
    let diagnostics = run.diagnostics.as_array().unwrap();
    assert_eq!(diagnostics.len(), 2);
    for diagnostic in diagnostics {
        assert_eq!(diagnostic["code"], 2451);
        assert_eq!(
            diagnostic["relatedInformation"].as_array().unwrap().len(),
            1
        );
        assert_eq!(diagnostic["relatedInformation"][0]["code"], 6203);
    }
    if requested {
        for kind in ["types", "symbols"] {
            for (field, expected) in [
                ("expectedBaselines", 1),
                ("exactMatches", 1),
                ("mismatches", 0),
                ("unsupported", 0),
                ("notReached", 0),
            ] {
                assert_eq!(
                    run.scorecard["semanticArtifacts"][kind][field], expected,
                    "{kind}.{field}"
                );
            }
            let artifact = &result["semanticArtifacts"][kind];
            assert_eq!(artifact["status"], "exact_match");
            assert!(artifact["visitedNodes"].as_u64().unwrap() > 0);
            assert!(artifact.get("unsupportedDetail").is_none());
            assert!(artifact.get("firstDifference").is_none());
        }
    } else {
        assert!(run.scorecard.get("semanticArtifacts").is_none());
        assert!(result.get("semanticArtifacts").is_none());
    }
    assert!(!run.output.contains("FATAL "));
    assert!(!run.output.contains("MISMATCH "));
}

#[test]
fn review_artifact_execution_preserves_real_typed_failures_and_diagnostics() {
    for (label, source, expected_class) in [
        (
            "missing-type",
            inputs::MISSING_TYPE,
            CanonicalProgramCheckFailureClass::Unsupported {
                capability_code: "ARTIFACT.MISSING_TYPE",
            },
        ),
        (
            "callable-display",
            inputs::CALLABLE_DISPLAY,
            CanonicalProgramCheckFailureClass::Unsupported {
                capability_code: "T07.TYPE_DISPLAY",
            },
        ),
    ] {
        let run = run_case(label, source, true, true);
        let Err(SemanticArtifactError::Checker(error)) = &run.generated.types else {
            panic!(
                "{label}: expected a real typed render failure: {:?}",
                run.generated.types
            )
        };
        assert_eq!(error.class, expected_class, "{label}");
        let unsupported = expected_class.is_unsupported();
        assert_single_failed_variant(
            &run,
            if unsupported {
                "unsupported_detail"
            } else {
                "fatal_invariant"
            },
            if unsupported {
                "checker_capability"
            } else {
                "fatal_invariant"
            },
        );
        assert_eq!(run.scorecard["summary"]["headerMismatches"], 0);
        assert_eq!(
            run.scorecard["summary"]["fatalInvariants"],
            usize::from(!unsupported)
        );
        assert_eq!(
            run.scorecard["summary"]["unsupportedDetails"],
            usize::from(unsupported)
        );
        let result = &run.scorecard["variants"][0];
        assert_eq!(result["frontierBlocker"]["code"], expected_class.code());
        assert_eq!(
            result["frontierBlocker"]["detail"],
            result["semanticArtifacts"]["types"]["unsupportedDetail"]
        );
        assert_eq!(
            run.scorecard["semanticArtifacts"]["types"]["expectedBaselines"],
            1
        );
        assert_eq!(
            run.scorecard["semanticArtifacts"]["types"]["unsupported"],
            1
        );
        assert_eq!(
            run.scorecard["semanticArtifacts"]["types"]["exactMatches"],
            0
        );
        assert_eq!(
            run.scorecard["semanticArtifacts"]["symbols"]["exactMatches"],
            1
        );
    }
    let run = run_case(
        "fatal-with-diagnostics",
        inputs::FATAL_WITH_DIAGNOSTICS,
        true,
        true,
    );
    assert_rendered_namespace_diagnostics(&run, true);
}

#[test]
fn review_artifact_execution_ignores_unrequested_render_failures() {
    for (label, source) in [
        ("diagnostics-only-missing-type", inputs::MISSING_TYPE),
        (
            "diagnostics-only-callable-display",
            inputs::CALLABLE_DISPLAY,
        ),
        ("diagnostics-only-no-check", inputs::DISABLED_CHECKER),
    ] {
        let run = run_case(label, source, false, true);
        assert!(
            run.generated.types.is_err(),
            "the control must really fail to render"
        );
        assert!(run.summary.is_success(), "{}", run.output);
        assert_eq!(run.summary.executed_variants, 1);
        assert_eq!(run.summary.matched, 1);
        assert_eq!(run.scorecard["summary"]["exactMatches"], 1);
        assert_eq!(run.scorecard["summary"]["fatalInvariants"], 0);
        assert_eq!(run.scorecard["variants"][0]["status"], "exact_match");
        assert_eq!(run.scorecard["variants"][0]["diagnostics"], run.diagnostics);
        assert!(run.scorecard.get("semanticArtifacts").is_none());
        assert!(
            run.scorecard["variants"][0]
                .get("semanticArtifacts")
                .is_none()
        );
    }
    let run = run_case(
        "diagnostics-only-fatal",
        inputs::FATAL_WITH_DIAGNOSTICS,
        false,
        true,
    );
    assert_rendered_namespace_diagnostics(&run, false);
}

#[test]
fn review_artifact_execution_keeps_disabled_checker_as_harness_config() {
    for (label, source) in [
        ("no-check", inputs::DISABLED_CHECKER),
        ("no-check-empty", "// @noCheck: true\n"),
    ] {
        let run = run_case(label, source, true, true);
        let Err(SemanticArtifactError::HarnessConfig(detail)) = &run.generated.types else {
            panic!("expected a real disabled-checker result")
        };
        assert_single_failed_variant(&run, "unsupported_detail", "harness_config");
        assert_eq!(run.scorecard["summary"]["fatalInvariants"], 0);
        assert_eq!(run.scorecard["summary"]["unsupportedDetails"], 1);
        assert!(run.scorecard["variants"][0]["frontierBlocker"]["code"].is_null());
        for kind in ["types", "symbols"] {
            assert_eq!(run.scorecard["semanticArtifacts"][kind]["unsupported"], 1);
            assert_eq!(run.scorecard["semanticArtifacts"][kind]["exactMatches"], 0);
            assert_eq!(
                run.scorecard["variants"][0]["semanticArtifacts"][kind]["unsupportedDetail"],
                *detail
            );
        }
    }
}

#[test]
fn review_artifact_execution_prefers_fatal_in_both_orders_and_keeps_full_details() {
    let fatal = SemanticArtifactError::Checker(ArtifactRenderError {
        class: CanonicalProgramCheckFailureClass::Fatal {
            invariant_code: "INV.SOURCE.TYPE_DISPLAY",
        },
        detail: format!(
            "unsupported-looking first line\n{}\nlast fatal detail",
            "f".repeat(2048)
        ),
    });
    let unsupported = SemanticArtifactError::Checker(ArtifactRenderError {
        class: CanonicalProgramCheckFailureClass::Unsupported {
            capability_code: "ARTIFACT.MISSING_TYPE",
        },
        detail: format!(
            "FATAL-looking first line\n{}\nlast unsupported detail",
            "u".repeat(2048)
        ),
    });
    for (order, types, symbols) in [
        ("types-fatal", fatal.clone(), unsupported.clone()),
        ("symbols-fatal", unsupported.clone(), fatal.clone()),
    ] {
        for matching in [false, true] {
            ARTIFACT_OVERRIDE.with_borrow_mut(|slot| {
                assert!(slot.is_none());
                *slot = Some((types.clone(), symbols.clone()));
            });
            let _reset = ResetOverride;
            let run = run_case(
                &format!("{order}-matching-{matching}"),
                "const value: number = \"wrong\";\n",
                true,
                matching,
            );
            ARTIFACT_OVERRIDE.with_borrow(|slot| assert!(slot.is_none(), "override was not used"));
            assert_single_failed_variant(&run, "fatal_invariant", "fatal_invariant");
            assert_eq!(run.scorecard["summary"]["fatalInvariants"], 1);
            assert_eq!(run.scorecard["summary"]["unsupportedDetails"], 0);
            assert_eq!(
                run.scorecard["summary"]["headerMismatches"],
                usize::from(!matching)
            );
            let result = &run.scorecard["variants"][0];
            assert_eq!(result["frontierBlocker"]["code"], "INV.SOURCE.TYPE_DISPLAY");
            assert_eq!(result["frontierBlocker"]["detail"], fatal.to_string());
            assert_eq!(
                result["semanticArtifacts"]["types"]["unsupportedDetail"],
                types.to_string()
            );
            assert_eq!(
                result["semanticArtifacts"]["symbols"]["unsupportedDetail"],
                symbols.to_string()
            );
            assert!(
                result["mismatchKinds"]
                    .as_array()
                    .unwrap()
                    .contains(&serde_json::json!("fatal_invariant"))
            );
            assert!(run.output.contains(&fatal.to_string()));
            for kind in ["types", "symbols"] {
                assert_eq!(run.scorecard["semanticArtifacts"][kind]["unsupported"], 1);
                assert_eq!(run.scorecard["semanticArtifacts"][kind]["exactMatches"], 0);
                assert_eq!(
                    run.scorecard["semanticArtifacts"][kind]["expectedBaselines"],
                    1
                );
            }
        }
    }
}
