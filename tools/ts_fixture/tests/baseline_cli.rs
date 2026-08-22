use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct TestRepository(PathBuf);

struct TestArtifacts(PathBuf);

impl TestArtifacts {
    fn new() -> Self {
        let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "ts-fixture-cli-artifacts-{}-{sequence}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir_all(&path).unwrap();
        Self(path)
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

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
        self.write_case_with_extension(name, "ts", source, baseline);
    }

    fn write_case_with_extension(
        &self,
        name: &str,
        extension: &str,
        source: &str,
        baseline: Option<&str>,
    ) {
        fs::write(
            self.0
                .join("testdata/tests/cases/compiler")
                .join(format!("{name}.{extension}")),
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

    fn commit_all(&self) -> String {
        let commands: &[&[&str]] = &[
            &["init", "--quiet"],
            &["config", "user.name", "Fixture Test"],
            &["config", "user.email", "fixture@example.invalid"],
            &["add", "."],
            &[
                "-c",
                "commit.gpgSign=false",
                "commit",
                "--quiet",
                "-m",
                "fixture",
            ],
        ];
        for arguments in commands {
            let output = Command::new("git")
                .arg("-C")
                .arg(&self.0)
                .args(*arguments)
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "git stderr: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        let output = Command::new("git")
            .arg("-C")
            .arg(&self.0)
            .args(["rev-parse", "HEAD"])
            .output()
            .unwrap();
        assert!(output.status.success());
        String::from_utf8(output.stdout).unwrap().trim().to_owned()
    }
}

#[test]
fn canonical_scorecard_retains_capabilities_then_continues_to_exact_case() {
    let repository = TestRepository::new();
    repository.write_case(
        "functionExpandoPropertyDeclaration",
        concat!(
            "// @declaration: true\n",
            "const foo = () => {}\n",
            "foo.bar = 42\n",
            "export {}\n",
        ),
        None,
    );
    repository.write_case(
        "javascriptUnsupported",
        concat!(
            "// @allowJs: true\n",
            "// @filename: unsupported.js\n",
            "const value = 1;\n",
        ),
        None,
    );
    repository.write_case("zzExact", "const value: number = 1;\n", None);
    let scorecard_path = repository.0.join("canonical-frontier.json");

    let output = run(
        &repository.0,
        &[
            "--diagnostics",
            "--canonical-checker",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains(
            "MISMATCH testdata/tests/cases/compiler/functionExpandoPropertyDeclaration.ts"
        )
    );
    assert!(stdout.contains("unsupported_details=2"));
    assert!(stdout.contains("fatal_invariants=0"));
    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    assert_eq!(scorecard["schemaVersion"], 5);
    assert_eq!(scorecard["summary"]["executedVariants"], 3);
    assert_eq!(scorecard["summary"]["exactMatches"], 1, "{scorecard:#}");
    assert_eq!(scorecard["summary"]["unsupportedDetails"], 2);
    assert_eq!(scorecard["summary"]["fatalInvariants"], 0);

    let variants = scorecard["variants"].as_array().unwrap();
    assert_eq!(variants.len(), 3);
    assert_eq!(
        variants[0]["case"],
        "testdata/tests/cases/compiler/functionExpandoPropertyDeclaration.ts"
    );
    assert_eq!(variants[0]["status"], "unsupported_detail");
    assert_eq!(variants[0]["outcomeClass"], "checker_capability");
    assert_eq!(
        variants[0]["frontierBlocker"]["outcomeClass"],
        "checker_capability"
    );
    assert_eq!(variants[0]["frontierBlocker"]["code"], "E00.SOURCE_SYNTAX");
    assert_eq!(
        variants[1]["case"],
        "testdata/tests/cases/compiler/javascriptUnsupported.ts"
    );
    assert_eq!(variants[1]["status"], "unsupported_detail");
    assert_eq!(variants[1]["outcomeClass"], "checker_capability");
    assert_eq!(
        variants[1]["frontierBlocker"]["outcomeClass"],
        "checker_capability"
    );
    assert_eq!(variants[1]["frontierBlocker"]["code"], "C00.SOURCE_KIND");
    assert_eq!(
        variants[2]["case"],
        "testdata/tests/cases/compiler/zzExact.ts"
    );
    assert_eq!(variants[2]["status"], "exact_match");
    assert_eq!(variants[2]["outcomeClass"], "exact");
}

#[test]
fn scorecard_provenance_identifies_the_upstream_git_revision_and_dirty_state() {
    let repository = TestRepository::new();
    repository.write_case("exact", "// @noLib: true\nconst value: number = 1;\n", None);
    let expected_sha = repository.commit_all();
    let scorecard_path = repository.0.join("scorecard.json");

    let output = run(
        &repository.0,
        &[
            "--diagnostics",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert!(output.status.success());
    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    assert_eq!(scorecard["provenance"]["upstream"]["sha"], expected_sha);
    assert_eq!(scorecard["provenance"]["upstream"]["dirty"], false);
}

impl Drop for TestRepository {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

impl Drop for TestArtifacts {
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

fn fixed_manifest_digest(variants: &[serde_json::Value]) -> String {
    let mut bytes = Vec::new();
    for variant in variants {
        bytes.extend_from_slice(
            variant["variantKey"]
                .as_str()
                .expect("scorecard variants have stable keys")
                .as_bytes(),
        );
        bytes.push(b'\n');
    }
    format!("{:032x}", xxhash_rust::xxh3::xxh3_128(&bytes))
}

fn make_fixed_manifest(scorecard: &serde_json::Value, upstream_sha: &str) -> serde_json::Value {
    let variants = scorecard["variants"]
        .as_array()
        .unwrap()
        .iter()
        .rev()
        .map(|variant| {
            let expected_diagnostics = if variant["expectedHeader"].as_str().unwrap().is_empty() {
                "clean"
            } else {
                "error"
            };
            serde_json::json!({
                "variantKey": variant["variantKey"].clone(),
                "family": "fixture",
                "case": variant["case"].clone(),
                "options": variant["options"].clone(),
                "expectedBaseline": variant["expectedBaseline"].clone(),
                "expectedDiagnostics": expected_diagnostics,
                "fileShape": "single_file",
                "sourceKinds": ["ts"],
                "tags": ["fixture"],
            })
        })
        .collect::<Vec<_>>();
    let expected_clean = variants
        .iter()
        .filter(|variant| variant["expectedDiagnostics"] == "clean")
        .count();
    let expected_error = variants.len() - expected_clean;
    let cases = variants
        .iter()
        .map(|variant| variant["case"].as_str().unwrap())
        .collect::<BTreeSet<_>>()
        .len();
    let digest = fixed_manifest_digest(&variants);

    serde_json::json!({
        "schemaVersion": 1,
        "name": "test-fixed-v1",
        "upstream": {
            "sha": upstream_sha,
            "oracleManifestDigest": scorecard["provenance"]["manifestDigest"].clone(),
        },
        "variantKeyVersion": 1,
        "selectionEvidence": {
            "scorecardSchemaVersion": scorecard["schemaVersion"].clone(),
            "rustSha": scorecard["provenance"]["rust"]["sha"].clone(),
            "selectedCases": scorecard["summary"]["selectedCases"].clone(),
            "executedVariants": scorecard["summary"]["executedVariants"].clone(),
        },
        "policy": {
            "families": ["fixture"],
            "quotaPerFamily": variants.len(),
            "expectedDiagnosticsPerFamily": {
                "clean": expected_clean,
                "error": expected_error,
            },
        },
        "coverage": {
            "cases": cases,
            "variants": variants.len(),
            "expectedClean": expected_clean,
            "expectedError": expected_error,
            "singleFile": variants.len(),
            "multiFile": 0,
            "sourceKindMembership": {
                "ts": variants.len(),
            },
        },
        "digest": {
            "algorithm": "xxh3-128",
            "canonicalization": "ordered variantKey values encoded as UTF-8, each followed by LF",
            "value": digest,
        },
        "variants": variants,
    })
}

struct FixedCliFixture {
    repository: TestRepository,
    artifacts: TestArtifacts,
    discovery_scorecard: serde_json::Value,
    manifest: serde_json::Value,
}

impl FixedCliFixture {
    fn new() -> Self {
        let repository = TestRepository::new();
        repository.write_case(
            "aClean",
            concat!(
                "// @target: es2015, esnext\n",
                "// @noLib: true\n",
                "const value: number = 1;\n",
            ),
            None,
        );
        repository.write_case(
            "zError",
            concat!(
                "// @noLib: true\n",
                "// @noEmit: true\n",
                "const value: string = 1;\n",
            ),
            None,
        );
        repository.write_baseline(
            "zError.errors.txt",
            concat!(
                "zError.ts(1,7): error TS2322: Type 'number' is not assignable to type 'string'.\r\n",
                "\r\n",
                "\r\n",
                "==== zError.ts (1 errors) ====\r\n",
                "    const value: string = 1;\r\n",
                "          ~~~~~~~~~~~~~~~~~\r\n",
                "!!! error TS2322: Type 'number' is not assignable to type 'string'.\r\n",
                "    ",
            ),
        );
        let upstream_sha = repository.commit_all();
        let artifacts = TestArtifacts::new();
        let discovery_path = artifacts.path("discovery.json");
        let discovery = run(
            &repository.0,
            &[
                "--diagnostics",
                "--scorecard-json",
                discovery_path.to_str().unwrap(),
            ],
        );
        assert!(
            discovery.status.success(),
            "stdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&discovery.stdout),
            String::from_utf8_lossy(&discovery.stderr),
        );
        let discovery_scorecard: serde_json::Value =
            serde_json::from_str(&fs::read_to_string(discovery_path).unwrap()).unwrap();
        let manifest = make_fixed_manifest(&discovery_scorecard, &upstream_sha);
        Self {
            repository,
            artifacts,
            discovery_scorecard,
            manifest,
        }
    }

    fn write_manifest(&self, name: &str, manifest: &serde_json::Value) -> PathBuf {
        let path = self.artifacts.path(name);
        fs::write(&path, serde_json::to_vec_pretty(manifest).unwrap()).unwrap();
        path
    }

    fn invalid_manifest_error(&self, name: &str, manifest: &serde_json::Value) -> String {
        let path = self.write_manifest(name, manifest);
        let output = run(
            &self.repository.0,
            &[
                "--diagnostics",
                "--variant-manifest",
                path.to_str().unwrap(),
            ],
        );
        assert_eq!(
            output.status.code(),
            Some(2),
            "manifest={name}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        String::from_utf8(output.stderr).unwrap()
    }
}

#[test]
fn fixed_variant_manifest_resolves_exact_keys_and_executes_manifest_order() {
    let fixture = FixedCliFixture::new();
    let manifest_path = fixture.write_manifest("fixed.json", &fixture.manifest);
    let scorecard_path = fixture.artifacts.path("fixed-scorecard.json");

    let output = run(
        &fixture.repository.0,
        &[
            "--diagnostics",
            "--variant-manifest",
            manifest_path.to_str().unwrap(),
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    let expected_keys = fixture.manifest["variants"]
        .as_array()
        .unwrap()
        .iter()
        .map(|variant| variant["variantKey"].clone())
        .collect::<Vec<_>>();
    let actual_keys = scorecard["variants"]
        .as_array()
        .unwrap()
        .iter()
        .map(|variant| variant["variantKey"].clone())
        .collect::<Vec<_>>();

    assert_eq!(actual_keys, expected_keys);
    assert_eq!(
        scorecard["variants"][0]["case"],
        "testdata/tests/cases/compiler/zError.ts"
    );
    assert_eq!(
        scorecard["variants"][1]["case"],
        "testdata/tests/cases/compiler/aClean.ts"
    );
    assert_eq!(scorecard["variants"][1]["options"]["target"], "esnext");
    assert_eq!(
        scorecard["variants"][2]["case"],
        "testdata/tests/cases/compiler/aClean.ts"
    );
    assert_eq!(scorecard["variants"][2]["options"]["target"], "es2015");
    assert_eq!(scorecard["summary"]["selectedCases"], 2);
    assert_eq!(scorecard["summary"]["executedVariants"], 3);
    assert_eq!(
        scorecard["provenance"]["manifestDigest"],
        fixture.discovery_scorecard["provenance"]["manifestDigest"]
    );
    assert_ne!(
        scorecard["provenance"]["manifestDigest"],
        fixture.manifest["digest"]["value"]
    );
    assert_eq!(
        scorecard["provenance"]["fixedShard"],
        serde_json::json!({
            "name": "test-fixed-v1",
            "schemaVersion": 1,
            "variantKeyVersion": 1,
            "digest": fixture.manifest["digest"]["value"].clone(),
            "digestAlgorithm": "xxh3-128",
            "variantCount": 3,
        })
    );
}

#[test]
fn fixed_variant_manifest_does_not_parse_unrelated_runnable_cases() {
    let mut fixture = FixedCliFixture::new();
    fixture.repository.write_case(
        "unrelatedMalformed",
        concat!(
            "const sourceBeforeFirstUnit = true;\n",
            "// @filename: /actual.ts\n",
            "const selected = false;\n",
        ),
        None,
    );
    let upstream_sha = fixture.repository.commit_all();
    let oracle = run(&fixture.repository.0, &["--manifest"]);
    assert!(
        oracle.status.success(),
        "stderr:\n{}",
        String::from_utf8_lossy(&oracle.stderr)
    );
    assert!(String::from_utf8_lossy(&oracle.stdout).contains(concat!(
        "case\tgo\tcompiler\trunnable\t",
        "testdata/tests/cases/compiler/unrelatedMalformed.ts\n",
    )));
    let oracle_digest = format!("{:032x}", xxhash_rust::xxh3::xxh3_128(&oracle.stdout));
    fixture.manifest["upstream"]["sha"] = serde_json::json!(upstream_sha);
    fixture.manifest["upstream"]["oracleManifestDigest"] = serde_json::json!(oracle_digest.clone());

    let manifest_path = fixture.write_manifest("malformed-unrelated.json", &fixture.manifest);
    let scorecard_path = fixture.artifacts.path("malformed-unrelated-scorecard.json");
    let output = run(
        &fixture.repository.0,
        &[
            "--diagnostics",
            "--variant-manifest",
            manifest_path.to_str().unwrap(),
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    assert_eq!(scorecard["summary"]["discoveredCases"], 3);
    assert_eq!(scorecard["summary"]["selectedCases"], 2);
    assert_eq!(scorecard["summary"]["executedVariants"], 3);
    assert_eq!(
        scorecard["provenance"]["manifestDigest"],
        oracle_digest.as_str()
    );
}

#[test]
fn fixed_variant_manifest_rejects_tampering_stale_keys_and_dirty_upstream() {
    let fixture = FixedCliFixture::new();

    let mut wrong_digest = fixture.manifest.clone();
    wrong_digest["digest"]["value"] = serde_json::Value::String("0".repeat(32));
    assert!(
        fixture
            .invalid_manifest_error("wrong-digest.json", &wrong_digest)
            .contains("ordered-key digest")
    );

    let mut wrong_metadata = fixture.manifest.clone();
    wrong_metadata["variants"][0]["options"]["strict"] = serde_json::json!("true");
    assert!(
        fixture
            .invalid_manifest_error("wrong-metadata.json", &wrong_metadata)
            .contains("metadata disagrees")
    );

    let mut missing_baseline_field = fixture.manifest.clone();
    let removed = missing_baseline_field["variants"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|variant| variant["expectedBaseline"].is_null())
        .unwrap()
        .as_object_mut()
        .unwrap()
        .remove("expectedBaseline");
    assert!(removed.is_some());
    assert!(
        fixture
            .invalid_manifest_error("missing-baseline-field.json", &missing_baseline_field)
            .contains("expectedBaseline")
    );

    let mut wrong_policy = fixture.manifest.clone();
    wrong_policy["policy"]["expectedDiagnosticsPerFamily"]["clean"] = serde_json::json!(3);
    wrong_policy["policy"]["expectedDiagnosticsPerFamily"]["error"] = serde_json::json!(0);
    assert!(
        fixture
            .invalid_manifest_error("wrong-policy.json", &wrong_policy)
            .contains("does not satisfy its quota and clean/error policy")
    );

    let mut stale_key = fixture.manifest.clone();
    stale_key["variants"][0]["variantKey"] =
        serde_json::json!("v1:00000000000000000000000000000000");
    stale_key["digest"]["value"] = serde_json::Value::String(fixed_manifest_digest(
        stale_key["variants"].as_array().unwrap(),
    ));
    assert!(
        fixture
            .invalid_manifest_error("stale-key.json", &stale_key)
            .contains("do not resolve in the complete corpus")
    );

    fs::write(fixture.repository.0.join("dirty.txt"), "dirty\n").unwrap();
    assert!(
        fixture
            .invalid_manifest_error("dirty-upstream.json", &fixture.manifest)
            .contains("upstream checkout must be clean")
    );
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
fn canonical_checker_matches_pinned_simple_multi_file_diagnostic_and_semantic_baselines() {
    let repository = TestRepository::new();
    repository.write_case(
        "simpleTestMultiFile",
        concat!(
            "// @filename: /src/foo.ts\r\n",
            "const x: number = \"\";\r\n",
            "\r\n",
            "// @filename: /src/bar.ts\r\n",
            "const y: string = 1;",
        ),
        None,
    );
    repository.write_baseline(
        "simpleTestMultiFile.errors.txt",
        concat!(
            "/src/bar.ts(1,7): error TS2322: Type 'number' is not assignable to type 'string'.\r\n",
            "/src/foo.ts(1,7): error TS2322: Type 'string' is not assignable to type 'number'.\r\n",
            "\r\n",
            "\r\n",
            "==== /src/foo.ts (1 errors) ====\r\n",
            "    const x: number = \"\";\r\n",
            "          ~\r\n",
            "!!! error TS2322: Type 'string' is not assignable to type 'number'.\r\n",
            "    \r\n",
            "==== /src/bar.ts (1 errors) ====\r\n",
            "    const y: string = 1;\r\n",
            "          ~\r\n",
            "!!! error TS2322: Type 'number' is not assignable to type 'string'.",
        ),
    );
    repository.write_baseline(
        "simpleTestMultiFile.types",
        concat!(
            "//// [tests/cases/compiler/simpleTestMultiFile.ts] ////\r\n\r\n",
            "=== /src/foo.ts ===\r\n",
            "const x: number = \"\";\r\n",
            ">x : number\r\n",
            ">\"\" : \"\"\r\n\r\n",
            "=== /src/bar.ts ===\r\n",
            "const y: string = 1;\r\n",
            ">y : string\r\n",
            ">1 : 1\r\n\r\n",
        ),
    );
    repository.write_baseline(
        "simpleTestMultiFile.symbols",
        concat!(
            "//// [tests/cases/compiler/simpleTestMultiFile.ts] ////\r\n\r\n",
            "=== /src/foo.ts ===\r\n",
            "const x: number = \"\";\r\n",
            ">x : Symbol(x, Decl(foo.ts, 0, 5))\r\n\r\n",
            "=== /src/bar.ts ===\r\n",
            "const y: string = 1;\r\n",
            ">y : Symbol(y, Decl(bar.ts, 0, 5))\r\n\r\n",
        ),
    );

    let scorecard_path = repository.0.join("canonical-scorecard.json");
    let output = run(
        &repository.0,
        &[
            "--diagnostics",
            "--canonical-checker",
            "--semantic-artifacts",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
            "--filter",
            "simpleTestMultiFile",
        ],
    );
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("selected_cases=1 executed_variants=1 matched=1 mismatched=0"));
    assert!(stdout.contains("diagnostic_comparison=full-artifact exact_matches=1"));
    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    assert_eq!(scorecard["schemaVersion"], 5);
    assert_eq!(scorecard["checkerMode"], "canonical");
    assert_eq!(scorecard["semanticArtifacts"]["types"]["exactMatches"], 1);
    assert_eq!(scorecard["semanticArtifacts"]["symbols"]["exactMatches"], 1);
    assert_eq!(
        scorecard["variants"][0]["diagnostics"][0]["relatedInformation"],
        serde_json::json!([])
    );
}

#[test]
fn canonical_checker_matches_related_information_artifact_and_scorecard_exactly() {
    let repository = TestRepository::new();
    repository.write_case(
        "relatedInformation",
        concat!(
            "// @filename: /src/input.ts\r\n",
            "function pair(left: string, right: number): number { return right; }\r\n",
            "const result = pair(\"left\");",
        ),
        None,
    );
    repository.write_baseline(
        "relatedInformation.errors.txt",
        concat!(
            "/src/input.ts(2,16): error TS2554: Expected 2 arguments, but got 1.\r\n",
            "\r\n",
            "\r\n",
            "==== /src/input.ts (1 errors) ====\r\n",
            "    function pair(left: string, right: number): number { return right; }\r\n",
            "    const result = pair(\"left\");\r\n",
            "                   ~~~~\r\n",
            "!!! error TS2554: Expected 2 arguments, but got 1.\r\n",
            "!!! related TS6210 /src/input.ts:1:29: An argument for 'right' was not provided.",
        ),
    );

    let scorecard_path = repository.0.join("related-scorecard.json");
    let output = run(
        &repository.0,
        &[
            "--diagnostics",
            "--canonical-checker",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
            "--filter",
            "relatedInformation",
        ],
    );
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}\nscorecard:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
        fs::read_to_string(&scorecard_path).unwrap_or_default(),
    );
    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    assert_eq!(scorecard["schemaVersion"], 5);
    assert_eq!(scorecard["checkerMode"], "canonical");
    assert_eq!(scorecard["summary"]["exactMatches"], 1);
    assert_eq!(scorecard["summary"]["actualDiagnostics"], 1);
    assert_eq!(scorecard["variants"][0]["status"], "exact_match");

    let diagnostics = scorecard["variants"][0]["diagnostics"].as_array().unwrap();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0]["fileName"], "/src/input.ts");
    assert_eq!(
        diagnostics[0]["relatedInformation"][0]["fileName"],
        "/src/input.ts"
    );
    assert_eq!(diagnostics[0]["relatedInformation"][0]["code"], 6210);
    assert_eq!(
        diagnostics[0]["relatedInformation"][0]["category"],
        "message"
    );
    assert_eq!(
        diagnostics[0]["relatedInformation"][0]["relatedInformation"],
        serde_json::json!([])
    );
}

#[test]
fn semantic_artifact_mode_matches_real_type_and_symbol_baselines() {
    let repository = TestRepository::new();
    repository.write_case("semanticArtifacts", "const value: number = 1;\n", None);
    repository.write_baseline(
        "semanticArtifacts.types",
        concat!(
            "//// [tests/cases/compiler/semanticArtifacts.ts] ////\r\n\r\n",
            "=== semanticArtifacts.ts ===\r\n",
            "const value: number = 1;\r\n",
            ">value : number\r\n",
            ">1 : 1\r\n\r\n",
        ),
    );
    repository.write_baseline(
        "semanticArtifacts.symbols",
        concat!(
            "//// [tests/cases/compiler/semanticArtifacts.ts] ////\r\n\r\n",
            "=== semanticArtifacts.ts ===\r\n",
            "const value: number = 1;\r\n",
            ">value : Symbol(value, Decl(semanticArtifacts.ts, 0, 5))\r\n\r\n",
        ),
    );
    let scorecard_path = repository.0.join("semantic-scorecard.json");

    let output = run(
        &repository.0,
        &[
            "--diagnostics",
            "--canonical-checker",
            "--semantic-artifacts",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}\nscorecard:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
        fs::read_to_string(&scorecard_path).unwrap_or_default(),
    );
    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();

    assert_eq!(scorecard["summary"]["executedVariants"], 1);
    assert_eq!(scorecard["summary"]["exactMatches"], 1);
    assert_eq!(scorecard["summary"]["unsupportedDetails"], 0);
    assert_eq!(scorecard["variants"][0]["status"], "exact_match");
    assert_eq!(scorecard["variants"][0]["outcomeClass"], "exact");
    for kind in ["types", "symbols"] {
        assert_eq!(scorecard["semanticArtifacts"][kind]["expectedBaselines"], 1);
        assert_eq!(scorecard["semanticArtifacts"][kind]["missingBaselines"], 0);
        assert_eq!(scorecard["semanticArtifacts"][kind]["exactMatches"], 1);
        assert_eq!(scorecard["semanticArtifacts"][kind]["unsupported"], 0);
        assert_eq!(
            scorecard["variants"][0]["semanticArtifacts"][kind]["status"],
            "exact_match"
        );
        assert!(
            scorecard["variants"][0]["semanticArtifacts"][kind]["visitedNodes"]
                .as_u64()
                .unwrap()
                > 0
        );
        assert!(
            scorecard["variants"][0]["semanticArtifacts"][kind]["expectedBaseline"]
                .as_str()
                .unwrap()
                .ends_with(kind)
        );
    }
}

#[test]
fn semantic_artifact_mode_matches_the_pinned_single_file_oracles() {
    let repository = TestRepository::new();
    repository.write_case("simpleTestSingleFile", "const x: number = \"\";", None);
    repository.write_baseline(
        "simpleTestSingleFile.errors.txt",
        concat!(
            "simpleTestSingleFile.ts(1,7): error TS2322: Type 'string' is not assignable to type 'number'.\r\n",
            "\r\n\r\n",
            "==== simpleTestSingleFile.ts (1 errors) ====\r\n",
            "    const x: number = \"\";\r\n",
            "          ~\r\n",
            "!!! error TS2322: Type 'string' is not assignable to type 'number'.",
        ),
    );
    repository.write_baseline(
        "simpleTestSingleFile.types",
        concat!(
            "//// [tests/cases/compiler/simpleTestSingleFile.ts] ////\r\n\r\n",
            "=== simpleTestSingleFile.ts ===\r\n",
            "const x: number = \"\";\r\n",
            ">x : number\r\n",
            ">\"\" : \"\"\r\n\r\n",
        ),
    );
    repository.write_baseline(
        "simpleTestSingleFile.symbols",
        concat!(
            "//// [tests/cases/compiler/simpleTestSingleFile.ts] ////\r\n\r\n",
            "=== simpleTestSingleFile.ts ===\r\n",
            "const x: number = \"\";\r\n",
            ">x : Symbol(x, Decl(simpleTestSingleFile.ts, 0, 5))\r\n\r\n",
        ),
    );
    let scorecard_path = repository.0.join("upstream-semantic-scorecard.json");

    let output = run(
        &repository.0,
        &[
            "--diagnostics",
            "--canonical-checker",
            "--semantic-artifacts",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}\nscorecard:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
        fs::read_to_string(&scorecard_path).unwrap_or_default(),
    );
    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    assert_eq!(scorecard["summary"]["exactMatches"], 1);
    assert_eq!(scorecard["summary"]["actualDiagnostics"], 1);
    assert_eq!(scorecard["semanticArtifacts"]["types"]["exactMatches"], 1);
    assert_eq!(scorecard["semanticArtifacts"]["symbols"]["exactMatches"], 1);
}

#[test]
fn semantic_artifact_mismatches_fail_an_otherwise_exact_diagnostic_variant() {
    let repository = TestRepository::new();
    repository.write_case("semanticMismatch", "const value: number = 1;\n", None);
    repository.write_baseline("semanticMismatch.types", "incorrect type baseline\r\n");
    repository.write_baseline(
        "semanticMismatch.symbols",
        concat!(
            "//// [tests/cases/compiler/semanticMismatch.ts] ////\r\n\r\n",
            "=== semanticMismatch.ts ===\r\n",
            "const value: number = 1;\r\n",
            ">value : Symbol(value, Decl(semanticMismatch.ts, 0, 5))\r\n\r\n",
        ),
    );
    let scorecard_path = repository.0.join("semantic-mismatch-scorecard.json");

    let output = run(
        &repository.0,
        &[
            "--diagnostics",
            "--canonical-checker",
            "--semantic-artifacts",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert_eq!(output.status.code(), Some(1));
    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    assert_eq!(scorecard["summary"]["exactMatches"], 0);
    assert_eq!(scorecard["summary"]["artifactMismatches"], 1);
    assert_eq!(scorecard["variants"][0]["status"], "artifact_mismatch");
    assert_eq!(
        scorecard["variants"][0]["outcomeClass"],
        "supported_mismatch"
    );
    assert_eq!(scorecard["semanticArtifacts"]["types"]["mismatches"], 1);
    assert_eq!(scorecard["semanticArtifacts"]["symbols"]["exactMatches"], 1);
    assert_eq!(
        scorecard["variants"][0]["semanticArtifacts"]["types"]["firstDifference"]["line"],
        1
    );
}

#[test]
fn semantic_artifact_mode_reports_when_no_check_prevents_checker_queries() {
    let repository = TestRepository::new();
    repository.write_case(
        "noCheckSemanticArtifacts",
        "// @noCheck: true\n// @noLib: true\nconst value: number = 1;\n",
        None,
    );
    repository.write_baseline("noCheckSemanticArtifacts.types", "expected types\r\n");
    repository.write_baseline("noCheckSemanticArtifacts.symbols", "expected symbols\r\n");
    let scorecard_path = repository.0.join("no-check-semantic-scorecard.json");

    let output = run(
        &repository.0,
        &[
            "--diagnostics",
            "--canonical-checker",
            "--semantic-artifacts",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert_eq!(output.status.code(), Some(1));
    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    assert_eq!(scorecard["summary"]["unsupportedDetails"], 1);
    for kind in ["types", "symbols"] {
        assert_eq!(scorecard["semanticArtifacts"][kind]["unsupported"], 1);
        assert_eq!(
            scorecard["variants"][0]["semanticArtifacts"][kind]["status"],
            "unsupported"
        );
        assert!(
            scorecard["variants"][0]["semanticArtifacts"][kind]["unsupportedDetail"]
                .as_str()
                .unwrap()
                .contains("noCheck")
        );
    }
}

#[test]
fn semantic_artifact_mode_does_not_assume_missing_baselines_are_empty_matches() {
    let repository = TestRepository::new();
    repository.write_case(
        "missingSemanticBaselines",
        "// @noLib: true\nconst value: number = 1;\n",
        None,
    );
    let scorecard_path = repository.0.join("missing-semantic-scorecard.json");

    let output = run(
        &repository.0,
        &[
            "--diagnostics",
            "--canonical-checker",
            "--semantic-artifacts",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert_eq!(output.status.code(), Some(1));
    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    assert_eq!(scorecard["summary"]["exactMatches"], 0);
    for kind in ["types", "symbols"] {
        assert_eq!(scorecard["semanticArtifacts"][kind]["expectedBaselines"], 0);
        assert_eq!(scorecard["semanticArtifacts"][kind]["missingBaselines"], 1);
        assert_eq!(scorecard["semanticArtifacts"][kind]["mismatches"], 1);
        assert_eq!(scorecard["semanticArtifacts"][kind]["unsupported"], 0);
        assert_eq!(
            scorecard["variants"][0]["semanticArtifacts"][kind]["status"],
            "mismatch"
        );
        assert!(scorecard["variants"][0]["semanticArtifacts"][kind]["expectedBaseline"].is_null());
    }
}

#[test]
fn semantic_artifact_mode_preserves_the_upstream_no_types_and_symbols_skip() {
    let repository = TestRepository::new();
    repository.write_case(
        "skipSemanticBaselines",
        concat!(
            "// @noTypesAndSymbols: true\n",
            "const value: number = 1;\n",
        ),
        None,
    );
    let scorecard_path = repository.0.join("skipped-semantic-scorecard.json");

    let output = run(
        &repository.0,
        &[
            "--diagnostics",
            "--canonical-checker",
            "--semantic-artifacts",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    assert_eq!(scorecard["summary"]["exactMatches"], 1);
    for kind in ["types", "symbols"] {
        assert_eq!(scorecard["semanticArtifacts"][kind]["upstreamSkipped"], 1);
        assert_eq!(scorecard["semanticArtifacts"][kind]["unsupported"], 0);
        assert_eq!(
            scorecard["variants"][0]["semanticArtifacts"][kind]["status"],
            "upstream_skipped"
        );
    }
}

#[test]
fn semantic_artifacts_follow_configured_option_matrix_baselines() {
    let repository = TestRepository::new();
    repository.write_case(
        "configuredSemanticBaselines",
        concat!(
            "// @target: es2015, esnext\n",
            "// @noLib: true\n",
            "const value: number = 1;\n",
        ),
        None,
    );
    for target in ["es2015", "esnext"] {
        repository.write_baseline(
            &format!("configuredSemanticBaselines(target={target}).types"),
            "configured types\n",
        );
        repository.write_baseline(
            &format!("configuredSemanticBaselines(target={target}).symbols"),
            "configured symbols\n",
        );
    }
    let scorecard_path = repository.0.join("configured-semantic-scorecard.json");

    let output = run(
        &repository.0,
        &[
            "--diagnostics",
            "--canonical-checker",
            "--semantic-artifacts",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert_eq!(output.status.code(), Some(1));
    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    let variants = scorecard["variants"].as_array().unwrap();
    assert_eq!(variants.len(), 2);
    for variant in variants {
        let target = variant["options"]["target"].as_str().unwrap();
        for kind in ["types", "symbols"] {
            let baseline = variant["semanticArtifacts"][kind]["expectedBaseline"]
                .as_str()
                .unwrap();
            assert!(baseline.ends_with(&format!("(target={target}).{kind}")));
        }
    }
}

#[test]
fn semantic_artifacts_remain_not_reached_after_a_checker_capability() {
    let repository = TestRepository::new();
    repository.write_case(
        "unsupportedSemanticSource",
        concat!(
            "// @allowJs: true\n",
            "// @filename: unsupported.js\n",
            "const value = 1;\n",
        ),
        None,
    );
    let scorecard_path = repository.0.join("not-reached-semantic-scorecard.json");

    let output = run(
        &repository.0,
        &[
            "--diagnostics",
            "--canonical-checker",
            "--semantic-artifacts",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert_eq!(output.status.code(), Some(1));
    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    assert_eq!(
        scorecard["variants"][0]["outcomeClass"],
        "checker_capability"
    );
    assert_eq!(
        scorecard["variants"][0]["frontierBlocker"]["code"],
        "C00.SOURCE_KIND"
    );
    for kind in ["types", "symbols"] {
        assert_eq!(scorecard["semanticArtifacts"][kind]["notReached"], 1);
        assert_eq!(scorecard["semanticArtifacts"][kind]["unsupported"], 0);
        assert_eq!(
            scorecard["variants"][0]["semanticArtifacts"][kind]["status"],
            "not_reached"
        );
    }
}

#[test]
fn canonical_checker_cli_rejects_non_diagnostic_modes() {
    let repository = TestRepository::new();
    let artifact = run(&repository.0, &["--canonical-checker"]);
    assert_eq!(artifact.status.code(), Some(2));
    assert_eq!(
        String::from_utf8(artifact.stderr).unwrap(),
        "error: --canonical-checker requires --diagnostics\n"
    );

    let manifest = run(
        &repository.0,
        &["--diagnostics", "--canonical-checker", "--manifest"],
    );
    assert_eq!(manifest.status.code(), Some(2));
    assert_eq!(
        String::from_utf8(manifest.stderr).unwrap(),
        "error: --canonical-checker cannot be used with --manifest\n"
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
        "summary: discovered_cases=1 upstream_skipped_cases=1 selected_cases=0 executed_variants=0 matched=0 mismatched=0 missing=0 content=0 missing_sections=0 unexpected_sections=0 diagnostics=0 diagnostic_comparison=full-artifact exact_matches=0 header_only_matches=0 code_mismatches=0 span_mismatches=0 message_mismatches=0 order_mismatches=0 unsupported_details=0 header_mismatches=0 artifact_mismatches=0 fatal_invariants=0\n"
    );
}

#[test]
fn upstream_skipped_option_variants_are_not_executed_or_counted_as_matches() {
    let repository = TestRepository::new();
    repository.write_case(
        "classicResolutionSkip",
        concat!(
            "// @moduleResolution: classic\n",
            "// @strict: true\n",
            "const value: string = undefined;\n",
        ),
        None,
    );
    let scorecard_path = repository.0.join("skipped-option-scorecard.json");

    let output = run(
        &repository.0,
        &[
            "--diagnostics",
            "--canonical-checker",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    assert_eq!(scorecard["summary"]["selectedCases"], 1);
    assert_eq!(scorecard["summary"]["executedVariants"], 0);
    assert_eq!(scorecard["summary"]["upstreamSkippedVariants"], 1);
    assert_eq!(scorecard["summary"]["exactMatches"], 0);
    assert_eq!(scorecard["summary"]["actualDiagnostics"], 0);
    assert_eq!(scorecard["variants"][0]["status"], "upstream_skipped");
    assert_eq!(scorecard["variants"][0]["outcomeClass"], "upstream_skipped");
    assert_eq!(
        scorecard["variants"][0]["diagnostics"],
        serde_json::json!([])
    );
    assert!(
        scorecard["variants"][0]["frontierBlocker"]["detail"]
            .as_str()
            .unwrap()
            .contains("classic module resolution")
    );
}

#[test]
fn upstream_skipped_resolution_variants_do_not_change_runnable_denominators() {
    let repository = TestRepository::new();
    repository.write_case(
        "mixedResolutionModes",
        concat!(
            "// @moduleResolution: classic,bundler\n",
            "// @module: esnext\n",
            "const value: number = 1;\n",
        ),
        None,
    );
    repository.write_baseline(
        "mixedResolutionModes(moduleresolution=bundler).types",
        concat!(
            "//// [tests/cases/compiler/mixedResolutionModes.ts] ////\r\n\r\n",
            "=== mixedResolutionModes.ts ===\r\n",
            "const value: number = 1;\r\n",
            ">value : number\r\n",
            ">1 : 1\r\n\r\n",
        ),
    );
    repository.write_baseline(
        "mixedResolutionModes(moduleresolution=bundler).symbols",
        concat!(
            "//// [tests/cases/compiler/mixedResolutionModes.ts] ////\r\n\r\n",
            "=== mixedResolutionModes.ts ===\r\n",
            "const value: number = 1;\r\n",
            ">value : Symbol(value, Decl(mixedResolutionModes.ts, 0, 5))\r\n\r\n",
        ),
    );
    let scorecard_path = repository.0.join("mixed-resolution-scorecard.json");

    let output = run(
        &repository.0,
        &[
            "--diagnostics",
            "--canonical-checker",
            "--semantic-artifacts",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}\nscorecard:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
        fs::read_to_string(&scorecard_path).unwrap_or_default(),
    );
    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    assert_eq!(scorecard["summary"]["selectedCases"], 1);
    assert_eq!(scorecard["summary"]["upstreamSkippedVariants"], 1);
    assert_eq!(scorecard["summary"]["executedVariants"], 1);
    assert_eq!(scorecard["summary"]["exactMatches"], 1);
    for kind in ["types", "symbols"] {
        assert_eq!(scorecard["semanticArtifacts"][kind]["upstreamSkipped"], 1);
        assert_eq!(scorecard["semanticArtifacts"][kind]["expectedBaselines"], 1);
        assert_eq!(scorecard["semanticArtifacts"][kind]["exactMatches"], 1);
        assert_eq!(scorecard["semanticArtifacts"][kind]["missingBaselines"], 0);
    }
    assert_eq!(scorecard["variants"][0]["status"], "upstream_skipped");
    assert_eq!(scorecard["variants"][1]["status"], "exact_match");
}

#[test]
fn matches_a_nonempty_full_diagnostic_artifact_exactly() {
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
            "    const value: string = 1;\r\n",
            "          ~~~~~~~~~~~~~~~~~\r\n",
            "!!! error TS2322: Type 'number' is not assignable to type 'string'.\r\n",
            "    ",
        ),
    );

    let output = run(
        &repository.0,
        &["--diagnostics", "--filter", "diagnosticParity"],
    );
    assert!(output.status.success());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "summary: discovered_cases=1 upstream_skipped_cases=0 selected_cases=1 executed_variants=1 matched=1 mismatched=0 missing=0 content=0 missing_sections=0 unexpected_sections=0 diagnostics=0 diagnostic_comparison=full-artifact exact_matches=1 header_only_matches=0 code_mismatches=0 span_mismatches=0 message_mismatches=0 order_mismatches=0 unsupported_details=0 header_mismatches=0 artifact_mismatches=0 fatal_invariants=0\n"
    );
}

#[test]
#[allow(clippy::too_many_lines)] // The scorecard contract is clearest as one end-to-end assertion.
fn writes_deterministic_structured_full_artifact_scorecard() {
    let repository = TestRepository::new();
    repository.write_case(
        "aHeaderMatch",
        "// @noLib: true\nconst value: string = 1;\n",
        None,
    );
    repository.write_baseline(
        "aHeaderMatch.errors.txt",
        concat!(
            "aHeaderMatch.ts(1,7): error TS2322: Type 'number' is not assignable to type 'string'.\r\n",
            "\r\n",
            "\r\n",
            "==== aHeaderMatch.ts (1 errors) ====\r\n",
            "    const value: string = 1;\r\n",
            "          ~~~~~~~~~~~~~~~~~\r\n",
            "!!! error TS2322: Type 'number' is not assignable to type 'string'.\r\n",
            "    ",
        ),
    );
    repository.write_case(
        "bHeaderMismatch",
        "// @noLib: true\nconst value: string = 1;\n",
        None,
    );
    repository.write_baseline(
        "bHeaderMismatch.errors.txt",
        concat!(
            "bHeaderMismatch.ts(1,7): error TS9999: Type 'number' is not assignable to type 'string'.\r\n",
            "\r\n",
            "\r\n",
            "==== bHeaderMismatch.ts (1 errors) ====\r\n",
            "    const value: string = 1;\r\n",
            "          ~~~~~~~~~~~~~~~~~\r\n",
            "!!! error TS9999: Type 'number' is not assignable to type 'string'.\r\n",
            "    ",
        ),
    );

    let scorecard_path = repository.0.join("scorecard.json");
    let first = run(
        &repository.0,
        &[
            "--diagnostics",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert_eq!(first.status.code(), Some(1));
    let first_json = fs::read_to_string(&scorecard_path).unwrap();

    let second = run(
        &repository.0,
        &[
            "--diagnostics",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert_eq!(second.status.code(), Some(1));
    assert_eq!(first_json, fs::read_to_string(&scorecard_path).unwrap());

    let scorecard: serde_json::Value = serde_json::from_str(&first_json).unwrap();
    assert_eq!(scorecard["schemaVersion"], 5);
    assert_eq!(scorecard["checkerMode"], "legacy");
    assert_eq!(scorecard["comparisonScope"], "full_artifact");
    assert_eq!(scorecard["fullArtifactComparison"], true);
    assert_eq!(scorecard["summary"]["executedVariants"], 2);
    assert_eq!(scorecard["summary"]["exactMatches"], 1);
    assert_eq!(scorecard["summary"]["headerOnlyMatches"], 0);
    assert_eq!(scorecard["summary"]["codeMismatches"], 1);
    assert_eq!(scorecard["summary"]["unsupportedDetails"], 0);
    assert_eq!(scorecard["summary"]["fatalInvariants"], 0);
    assert_eq!(scorecard["summary"]["headerMismatches"], 1);
    assert_eq!(scorecard["summary"]["actualDiagnostics"], 2);
    assert_eq!(scorecard["provenance"]["digestAlgorithm"], "xxh3-128");
    assert_eq!(
        scorecard["provenance"]["upstream"]["sha"],
        serde_json::Value::Null
    );
    assert_eq!(
        scorecard["provenance"]["rust"]["sha"]
            .as_str()
            .unwrap()
            .len(),
        40
    );
    assert!(scorecard["provenance"]["rust"]["dirty"].is_boolean());
    assert_eq!(
        scorecard["provenance"]["manifestDigest"]
            .as_str()
            .unwrap()
            .len(),
        32
    );
    assert_eq!(scorecard["provenance"]["capabilityRegistry"]["version"], 1);
    assert_eq!(
        scorecard["provenance"]["invocation"],
        serde_json::json!([
            env!("CARGO_BIN_EXE_ts_fixture_baseline"),
            "--diagnostics",
            "--scorecard-json",
            scorecard_path.to_str().unwrap()
        ])
    );

    let variants = scorecard["variants"].as_array().unwrap();
    assert_eq!(
        variants[0]["case"],
        "testdata/tests/cases/compiler/aHeaderMatch.ts"
    );
    assert_eq!(variants[0]["status"], "exact_match");
    assert_eq!(variants[0]["outcomeClass"], "exact");
    assert_eq!(variants[0]["frontierBlocker"], serde_json::Value::Null);
    assert!(
        variants[0]["variantKey"]
            .as_str()
            .unwrap()
            .starts_with("v1:")
    );
    assert_eq!(variants[0]["comparisonScope"], "full_artifact");
    assert_eq!(
        variants[0]["expectedBaseline"],
        "testdata/baselines/reference/compiler/aHeaderMatch.errors.txt"
    );
    assert_eq!(variants[1]["status"], "code_mismatch");
    assert_eq!(variants[1]["outcomeClass"], "supported_mismatch");
    assert_eq!(
        variants[1]["frontierBlocker"]["outcomeClass"],
        "supported_mismatch"
    );

    let diagnostic = &variants[0]["diagnostics"][0];
    assert_eq!(diagnostic["fileName"], "/.src/aHeaderMatch.ts");
    assert_eq!(diagnostic["range"]["start"], 6);
    assert_eq!(diagnostic["range"]["length"], 17);
    assert_eq!(diagnostic["code"], 2322);
    assert_eq!(diagnostic["category"], "error");
    assert_eq!(
        diagnostic["message"],
        "Type 'number' is not assignable to type 'string'."
    );
    assert_eq!(diagnostic["relatedInformation"], serde_json::json!([]));
}

#[test]
fn diagnostics_mode_counts_a_clean_missing_baseline_as_an_exact_match() {
    let repository = TestRepository::new();
    repository.write_case(
        "cleanDiagnostic",
        "// @noLib: true\nconst value: number = 1;\n",
        None,
    );

    let output = run(
        &repository.0,
        &["--diagnostics", "--filter", "cleanDiagnostic"],
    );
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("matched=1 mismatched=0"));
    assert!(stdout.contains("diagnostic_comparison=full-artifact exact_matches=1"));
}

#[test]
fn omitted_pinned_boolean_axis_is_enumerated_but_never_counted_exact() {
    let repository = TestRepository::new();
    repository.write_case(
        "typeSatisfaction_propertyValueConformance2",
        concat!(
            "// @target: es2015\n",
            "// @noUncheckedIndexedAccess: true, false\n",
            "\n",
            "type Facts = { [key: string]: boolean };\n",
            "declare function checkTruths(x: Facts): void;\n",
            "declare function checkM(x: { m: boolean }): void;\n",
            "const x = {\n",
            "    m: true\n",
            "};\n",
            "\n",
            "// Should be OK\n",
            "checkTruths(x);\n",
            "// Should be OK\n",
            "checkM(x);\n",
            "console.log(x.z);\n",
            "// Should be OK under --noUncheckedIndexedAccess\n",
            "const m: boolean = x.m;\n",
            "\n",
            "// Should be 'm'\n",
            "type M = keyof typeof x;\n",
            "\n",
            "// Should be able to detect a failure here\n",
            "const x2 = {\n",
            "    m: true,\n",
            "    s: \"false\"\n",
            "} satisfies Facts;\n",
        ),
        None,
    );
    let scorecard_path = repository.0.join("matrix-scorecard.json");

    let output = run(
        &repository.0,
        &[
            "--diagnostics",
            "--filter",
            "typeSatisfaction_propertyValueConformance2",
            "--scorecard-json",
            scorecard_path.to_str().unwrap(),
        ],
    );
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("[noUncheckedIndexedAccess=true]"));
    assert!(stdout.contains("[noUncheckedIndexedAccess=false]"));
    assert!(stdout.contains("executed_variants=2 matched=0 mismatched=2"));
    assert!(stdout.contains("exact_matches=0"));
    assert!(stdout.contains("unsupported_details=2"));

    let scorecard: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(scorecard_path).unwrap()).unwrap();
    assert_eq!(scorecard["summary"]["executedVariants"], 2);
    assert_eq!(scorecard["summary"]["exactMatches"], 0);
    assert_eq!(scorecard["summary"]["unsupportedDetails"], 2);
    let variants = scorecard["variants"].as_array().unwrap();
    assert_eq!(variants[0]["options"]["noUncheckedIndexedAccess"], "true");
    assert_eq!(variants[1]["options"]["noUncheckedIndexedAccess"], "false");
    assert!(
        variants
            .iter()
            .all(|variant| variant["status"] == "unsupported_detail")
    );
    assert!(
        variants
            .iter()
            .all(|variant| variant["outcomeClass"] == "harness_config")
    );
}

#[test]
fn emit_mode_never_counts_unsupported_variants_as_clean_exact_matches() {
    let repository = TestRepository::new();
    repository.write_case(
        "unsupportedEmitMatrix",
        concat!(
            "// @noLib: true\n",
            "// @noEmit: true\n",
            "// @noUncheckedIndexedAccess: true, false\n",
            "const value = 1;\n",
        ),
        None,
    );

    let output = run(&repository.0, &["--filter", "unsupportedEmitMatrix"]);
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("[noUncheckedIndexedAccess=true]"));
    assert!(stdout.contains("[noUncheckedIndexedAccess=false]"));
    assert!(stdout.contains("unsupported configuration"));
    assert!(stdout.contains("executed_variants=2 matched=0 mismatched=2"));
}

#[test]
fn pretty_diagnostic_fixture_is_explicitly_unsupported_instead_of_nonpretty_exact() {
    let repository = TestRepository::new();
    repository.write_case(
        "prettyDiagnostic",
        "// @pretty: true\n// @noLib: true\nconst value = 1;\n",
        None,
    );

    let output = run(
        &repository.0,
        &["--diagnostics", "--filter", "prettyDiagnostic"],
    );
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("UnsupportedDetail"));
    assert!(stdout.contains("pretty diagnostic baselines are not implemented"));
    assert!(stdout.contains("exact_matches=0"));
    assert!(stdout.contains("unsupported_details=1"));
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
    assert!(stdout.contains("HeaderMismatch at artifact line 1"));
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
fn refuses_exact_emit_parity_for_a_virtual_project_config() {
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
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        concat!(
            "MISMATCH testdata/tests/cases/compiler/projectNoEmit.ts: unsupported configuration: virtual project configurations are not modeled with pinned root/other-file semantics\n",
            "summary: discovered_cases=1 upstream_skipped_cases=0 selected_cases=1 executed_variants=1 matched=0 mismatched=1 missing=0 content=0 missing_sections=0 unexpected_sections=0 diagnostics=0\n",
        )
    );
}

#[test]
fn compiles_and_matches_option_variants() {
    let repository = TestRepository::new();
    repository.write_case(
        "matrix",
        "// @target: es2015, esnext\n// @module: esnext\n// @noLib: true\nconst value = 1;\n",
        None,
    );
    repository.write_baseline(
        "matrix(target=es2015).js",
        "//// [matrix.js] ////\n\"use strict\";\nconst value = 1;\n",
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
    assert!(stdout.contains("/.src/diagnostic.ts"));
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
        "// @declaration: true\n// @target: es2015\nconst value = 1;\n",
        Some("//// [unexpectedSection.js] ////\n\"use strict\";\nconst value = 1;\n"),
    );
    let unexpected = run(&repository.0, &["--filter", "unexpectedSection"]);
    assert_eq!(unexpected.status.code(), Some(1));
    assert!(
        String::from_utf8(unexpected.stdout)
            .unwrap()
            .contains("content=0 missing_sections=0 unexpected_sections=1 diagnostics=0")
    );
}
