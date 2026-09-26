use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicUsize, Ordering},
    time::Duration,
};

use serde_json::{Value, json};
use ts_compiler::Program;
use ts_fixture::project::{
    ProjectCensusAttempt, ProjectCensusDiagnosticScope, ProjectCensusDiagnostics,
    ProjectCensusEvent, ProjectCensusOptions, ProjectCensusOutcome, ProjectCensusReadback,
    ProjectCensusRecord, ProjectDiagnosticRecord, read_project_census, run_project_census,
};
use ts_vfs::OsFileSystem;

const PARTIAL_PROGRAM_POLICY: &str = "The final Program diagnostic snapshot was collected, but the ordinary post-source attempt failed afterward.";

struct TestProject(PathBuf);

impl TestProject {
    fn new(config: &str, files: &[(&str, &str)]) -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "ts-project-census-diagnostics-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("tsconfig.json"), config).unwrap();
        for (name, source) in files {
            fs::write(path.join(name), source).unwrap();
        }
        Self(path)
    }

    fn census(&self) -> ProjectCensusReadback {
        census(&self.0.join("tsconfig.json"), &Default::default())
    }

    fn program_diagnostics(&self) -> Vec<Value> {
        let config = self.0.join("tsconfig.json");
        let (program, checked) = Program::try_from_config_with_canonical_checker_and_queries(
            &OsFileSystem::default(),
            config.to_str().unwrap(),
            |_, _| (),
        )
        .unwrap();
        assert_eq!(checked, Some(()));
        program
            .diagnostics()
            .iter()
            .map(|diagnostic| {
                serde_json::to_value(ProjectDiagnosticRecord::from(diagnostic)).unwrap()
            })
            .collect()
    }
}

impl Drop for TestProject {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

fn census(config: &Path, options: &ProjectCensusOptions) -> ProjectCensusReadback {
    let mut bytes = Vec::new();
    run_project_census(config, None, "diagnostic-payload-test", options, &mut bytes).unwrap();
    read_project_census(bytes.as_slice()).unwrap()
}

fn encode<T: serde::Serialize>(records: &[T]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for record in records {
        serde_json::to_writer(&mut bytes, record).unwrap();
        bytes.push(b'\n');
    }
    bytes
}

#[test]
fn census_diagnostics_match_final_program_order() {
    const MAIN: &str = concat!(
        "import { pair } from './target';\n",
        "const bad: string = null;\n",
        "const tooFew = pair<string, number>('left');\n",
    );
    const TARGET: &str = "export function pair<T, U>(left: T, right: U): U { return right; }\n";
    let project = TestProject::new(
        r#"{
                "extends":"./missing.json",
                "files":["main.ts","duplicate.ts"],
                "compilerOptions":{
                    "strict":true,"noEmit":true,"lib":["es5"],"types":[],
                    "module":"esnext","moduleResolution":"bundler",
                    "unknownCompilerOption":true
                }
            }"#,
        &[
            ("main.ts", MAIN),
            ("target.ts", TARGET),
            (
                "duplicate.ts",
                "let duplicate: number = 1; let duplicate: number = 2;\n",
            ),
        ],
    );
    let report = project.census();
    assert_eq!(report.ordinary, ProjectCensusOutcome::OrdinaryCheckComplete);
    let ProjectCensusDiagnostics::CompleteProgram { records, .. } = &report.ordinary_diagnostics
    else {
        panic!(
            "missing final Program diagnostics: {:?}",
            report.ordinary_diagnostics
        );
    };
    assert_eq!(records, &project.program_diagnostics());
    for code in [2322, 2451, 5023, 6053] {
        assert!(records.iter().any(|record| record["code"] == code));
    }
    let arity = records
        .iter()
        .find(|record| record["code"] == 2554)
        .unwrap();
    let start = MAIN.find("pair<string, number>('left')").unwrap();
    let related_start = TARGET.find("right: U").unwrap();
    assert_eq!(
        arity,
        &json!({
            "fileName": project.0.join("main.ts").to_str().unwrap(),
            "range": { "startByte": start, "endByte": start + "pair".len() },
            "code": 2554,
            "category": "error",
            "message": "Expected 2 arguments, but got 1.",
            "relatedInformation": [{
                "fileName": project.0.join("target.ts").to_str().unwrap(),
                "range": {
                    "startByte": related_start,
                    "endByte": related_start + "right: U".len()
                },
                "code": 6210,
                "category": "message",
                "message": "An argument for 'right' was not provided.",
                "relatedInformation": []
            }]
        })
    );
    assert_eq!(report.roots.as_ref().unwrap().len(), 2);
    let ProjectCensusEvent::Loaded {
        graph,
        load_diagnostics,
        ..
    } = &report
        .records
        .iter()
        .find(|record| matches!(record.event, ProjectCensusEvent::Loaded { .. }))
        .unwrap()
        .event
    else {
        unreachable!()
    };
    assert!(
        load_diagnostics
            .iter()
            .all(|diagnostic| records.contains(diagnostic))
    );
    assert!(
        graph["evidence"]["sources"]
            .as_array()
            .unwrap()
            .iter()
            .any(|source| { source["fileName"].as_str() == project.0.join("target.ts").to_str() })
    );
    let reread = read_project_census(encode(&report.records).as_slice()).unwrap();
    assert_eq!(reread, report);
}

fn assert_raw_comment_directive_policy() {
    let project = TestProject::new(
        r#"{
                "files":["main.ts","ignored.ts","unchecked.js","skipped.d.ts"],
                "compilerOptions":{
                    "strict":true,"noEmit":true,"lib":["es5"],"types":[],
                    "allowJs":true,"checkJs":false,"skipLibCheck":true
                }
            }"#,
        &[
            (
                "main.ts",
                concat!(
                    "// @ts-expect-error\n",
                    "const suppressed: string = null;\n",
                    "// @ts-ignore\n",
                    "const ignored: string = null;\n",
                    "// @ts-expect-error\n",
                    "const unused: number = 1;\n",
                    "const visible: string = null;\n",
                ),
            ),
            (
                "ignored.ts",
                "// @ts-nocheck\nconst ignoredFile: string = null;\n",
            ),
            ("unchecked.js", "const unchecked = MissingGlobal;\n"),
            ("skipped.d.ts", "declare const skipped: NeverProvided;\n"),
        ],
    );
    let report = project.census();
    let ProjectCensusDiagnostics::CompleteProgram { records, .. } = &report.ordinary_diagnostics
    else {
        panic!("ordinary diagnostics were not complete");
    };
    assert_eq!(records, &project.program_diagnostics());
    assert_eq!(
        records
            .iter()
            .map(|record| &record["code"])
            .collect::<Vec<_>>(),
        [&json!(2578), &json!(2322)]
    );
    let roots = report.roots.as_ref().unwrap();
    let ProjectCensusDiagnostics::CompleteSourceContext { records, policy } = &roots[0].diagnostics
    else {
        panic!("cold source diagnostics were not captured");
    };
    assert_eq!(
        records
            .iter()
            .filter(|record| record["code"] == 2322)
            .count(),
        3
    );
    assert!(records.iter().all(|record| record["code"] != 2578));
    let policy = policy.to_ascii_lowercase();
    assert!(policy.contains("raw"));
    assert!(policy.contains("directive"));
    for (root, reason) in roots[1..].iter().zip([
        "no_check_directive",
        "unchecked_javascript",
        "declaration_file",
    ]) {
        assert_eq!(
            root.diagnostics,
            ProjectCensusDiagnostics::Skipped {
                reason: reason.to_owned()
            }
        );
    }
}

#[test]
fn census_diagnostics_keep_cold_context_and_partial_failures() {
    let project = TestProject::new(
        r#"{"compilerOptions":{"noLib":true,"noEmit":true,"strict":true},"files":["wrong.ts","broken.ts"]}"#,
        &[
            ("wrong.ts", "const wrong: number = 'text';"),
            ("broken.ts", "function* first() { yield 1; }"),
        ],
    );
    let report = project.census();
    let ProjectCensusOutcome::Unsupported { failure } = &report.ordinary else {
        panic!(
            "the ordinary source failure is missing: {:?}",
            report.ordinary
        );
    };
    assert_eq!(failure.phase, "source");
    assert_eq!(
        failure.reported_file_name.as_deref(),
        project.0.join("broken.ts").to_str()
    );
    let ProjectCensusDiagnostics::Partial {
        scope: ProjectCensusDiagnosticScope::RawContext,
        records,
        conversion_error: None,
        ..
    } = &report.ordinary_diagnostics
    else {
        panic!("ordinary early diagnostics must remain partial");
    };
    let mismatch = records
        .iter()
        .find(|record| record["code"] == 2322)
        .unwrap();
    assert_eq!(
        mismatch["fileName"].as_str(),
        project.0.join("wrong.ts").to_str()
    );
    let roots = report.roots.as_ref().unwrap();
    assert_eq!(roots.len(), 2);
    assert_eq!(roots[0].outcome, ProjectCensusOutcome::SourceCheckComplete);
    let ProjectCensusDiagnostics::CompleteSourceContext { records, .. } = &roots[0].diagnostics
    else {
        panic!("first cold source diagnostics were not captured");
    };
    assert_eq!(
        records
            .iter()
            .filter(|record| record["code"] == 2322)
            .collect::<Vec<_>>(),
        [mismatch]
    );
    assert_eq!(roots[1].outcome, report.ordinary);
    let ProjectCensusDiagnostics::Partial {
        scope: ProjectCensusDiagnosticScope::RawContext,
        records,
        conversion_error: None,
        ..
    } = &roots[1].diagnostics
    else {
        panic!("failed cold source diagnostics must remain partial");
    };
    assert!(records.iter().all(|record| record["code"] != 2322));
    assert!(!report.records.iter().any(|record| matches!(
        &record.event,
        ProjectCensusEvent::PhaseStarted { phase, .. } if phase == "post_source"
    )));

    let mut changed = report.records.clone();
    let payload = changed
        .iter_mut()
        .find_map(|record| match &mut record.event {
            ProjectCensusEvent::AttemptFinished {
                attempt: ProjectCensusAttempt::Ordinary,
                diagnostics,
                ..
            } => diagnostics.as_mut(),
            _ => None,
        })
        .unwrap();
    let ProjectCensusDiagnostics::Partial { scope, policy, .. } = payload else {
        unreachable!()
    };
    *scope = ProjectCensusDiagnosticScope::Program;
    *policy = PARTIAL_PROGRAM_POLICY.to_owned();
    assert_eq!(
        read_project_census(encode(&changed).as_slice())
            .unwrap_err()
            .kind(),
        std::io::ErrorKind::InvalidData
    );
    assert_raw_comment_directive_policy();
}

fn assert_unavailable_and_skipped_results() {
    let project = TestProject::new(
        r#"{"compilerOptions":{"noLib":true,"noCheck":true},"files":["input.ts","input.ts","missing.ts"]}"#,
        &[("input.ts", "const value = (a, b) => a;\n")],
    );
    let report = project.census();
    assert_eq!(report.completion.as_deref(), Some("no_check"));
    assert_eq!(
        report.ordinary_diagnostics,
        ProjectCensusDiagnostics::Skipped {
            reason: "no_check".to_owned()
        }
    );
    let roots = report.roots.as_ref().unwrap();
    assert_eq!(roots.len(), 2);
    assert_eq!(roots[0].diagnostics, report.ordinary_diagnostics);
    assert!(
        matches!(&roots[1].diagnostics, ProjectCensusDiagnostics::Unattempted { reason } if reason.contains("not loaded"))
    );
    for diagnostic_state in [
        &report.ordinary_diagnostics,
        &roots[0].diagnostics,
        &roots[1].diagnostics,
    ] {
        assert!(
            serde_json::to_value(diagnostic_state)
                .unwrap()
                .get("records")
                .is_none()
        );
    }

    let missing = census(&project.0.join("absent.json"), &Default::default());
    assert_eq!(missing.completion.as_deref(), Some("load_unavailable"));
    assert!(!missing.ordinary_started);
    assert!(matches!(
        missing.ordinary_diagnostics,
        ProjectCensusDiagnostics::Unattempted { .. }
    ));
    assert!(missing.roots.is_none());
    assert!(missing.records.iter().any(|record| matches!(
        &record.event,
        ProjectCensusEvent::Loaded { load_diagnostics, .. } if !load_diagnostics.is_empty()
    )));

    let stopped = census(
        &project.0.join("tsconfig.json"),
        &ProjectCensusOptions {
            soft_deadline: Some(Duration::ZERO),
            ..Default::default()
        },
    );
    assert_eq!(stopped.completion.as_deref(), Some("stopped"));
    assert!(!stopped.ordinary_started);
    assert!(matches!(
        stopped.ordinary_diagnostics,
        ProjectCensusDiagnostics::Unattempted { .. }
    ));
    assert!(stopped.roots.is_none());

    let context_failure = TestProject::new(
        r#"{"compilerOptions":{"noLib":true,"noEmit":true},"files":["input.ts"]}"#,
        &[("input.ts", "var undefined: number;")],
    )
    .census();
    assert_eq!(
        context_failure.completion.as_deref(),
        Some("preparation_failed")
    );
    assert_eq!(
        context_failure.ordinary_diagnostics,
        ProjectCensusDiagnostics::UnavailableBeforeContext
    );
    let (ProjectCensusOutcome::Unsupported { failure }
    | ProjectCensusOutcome::Invariant { failure }) = &context_failure.ordinary
    else {
        panic!("missing context construction failure");
    };
    assert_eq!(failure.phase, "context");
    let roots = context_failure.roots.as_ref().unwrap();
    assert_eq!(roots.len(), 1);
    assert!(!roots[0].started);
    assert!(matches!(
        &roots[0].diagnostics,
        ProjectCensusDiagnostics::Unattempted { .. }
    ));
}

fn assert_legacy_and_truncated_records(report: &ProjectCensusReadback) {
    let mut legacy_values = report
        .records
        .iter()
        .map(|record| serde_json::to_value(record).unwrap())
        .collect::<Vec<_>>();
    for record in &mut legacy_values {
        record.as_object_mut().unwrap().remove("diagnostics");
    }
    let legacy = read_project_census(encode(&legacy_values).as_slice()).unwrap();
    assert_eq!(legacy.ordinary, ProjectCensusOutcome::OrdinaryCheckComplete);
    assert_eq!(
        legacy.ordinary_diagnostics,
        ProjectCensusDiagnostics::NotRecorded
    );
    let roots = legacy.roots.as_ref().unwrap();
    assert_eq!(roots[0].outcome, ProjectCensusOutcome::SourceCheckComplete);
    assert_eq!(roots[0].diagnostics, ProjectCensusDiagnostics::NotRecorded);
    assert_eq!(legacy.input_identity, report.input_identity);
    assert_eq!(
        serde_json::to_value(&legacy.records).unwrap(),
        json!(legacy_values)
    );

    let root_finish = report
        .records
        .iter()
        .position(|record| {
            matches!(
                record.event,
                ProjectCensusEvent::AttemptFinished {
                    attempt: ProjectCensusAttempt::Root { root_index: 0 },
                    ..
                }
            )
        })
        .unwrap();
    let mut bytes = encode(&report.records[..root_finish]);
    bytes.extend_from_slice(b"{\"schemaVersion\":");
    let truncated = read_project_census(bytes.as_slice()).unwrap();
    assert!(truncated.truncated_final_record);
    assert!(!truncated.has_footer);
    assert_eq!(truncated.ordinary_diagnostics, report.ordinary_diagnostics);
    let roots = truncated.roots.as_ref().unwrap();
    assert!(roots[0].started);
    assert!(
        matches!(&roots[0].outcome, ProjectCensusOutcome::Unattempted { reason } if reason.contains("cause is unknown"))
    );
    assert!(matches!(
        &roots[0].diagnostics,
        ProjectCensusDiagnostics::Unattempted { .. }
    ));
}

fn assert_rejected_diagnostic_state(
    records: &[ProjectCensusRecord],
    selected: ProjectCensusAttempt,
    payload: ProjectCensusDiagnostics,
) {
    let mut changed = records.to_vec();
    let event = changed
        .iter_mut()
        .find_map(|record| match &mut record.event {
            ProjectCensusEvent::AttemptFinished {
                attempt,
                diagnostics,
                ..
            } if *attempt == selected => Some(diagnostics),
            _ => None,
        })
        .unwrap();
    *event = Some(payload);
    assert_eq!(
        read_project_census(encode(&changed).as_slice())
            .unwrap_err()
            .kind(),
        std::io::ErrorKind::InvalidData
    );
}

#[test]
fn census_diagnostics_keep_missing_and_stopped_results_distinct() {
    assert_unavailable_and_skipped_results();
    let project = TestProject::new(
        r#"{"compilerOptions":{"noLib":true,"noEmit":true},"files":["input.ts"]}"#,
        &[("input.ts", "const value: number = 1;")],
    );
    let report = project.census();
    assert_legacy_and_truncated_records(&report);
    let root = &report.roots.as_ref().unwrap()[0];
    let ProjectCensusDiagnostics::CompleteSourceContext { records, policy } = &root.diagnostics
    else {
        panic!("missing cold source context")
    };
    for (attempt, payload) in [
        (ProjectCensusAttempt::Ordinary, root.diagnostics.clone()),
        (
            ProjectCensusAttempt::Root { root_index: 0 },
            report.ordinary_diagnostics.clone(),
        ),
        (
            ProjectCensusAttempt::Root { root_index: 0 },
            ProjectCensusDiagnostics::UnavailableBeforeContext,
        ),
        (
            ProjectCensusAttempt::Root { root_index: 0 },
            ProjectCensusDiagnostics::Skipped {
                reason: "no_check".to_owned(),
            },
        ),
        (
            ProjectCensusAttempt::Root { root_index: 0 },
            ProjectCensusDiagnostics::NotRecorded,
        ),
        (
            ProjectCensusAttempt::Root { root_index: 0 },
            ProjectCensusDiagnostics::Partial {
                scope: ProjectCensusDiagnosticScope::RawContext,
                records: records.clone(),
                policy: policy.clone(),
                conversion_error: None,
            },
        ),
        (
            ProjectCensusAttempt::Ordinary,
            ProjectCensusDiagnostics::Partial {
                scope: ProjectCensusDiagnosticScope::Program,
                records: records.clone(),
                policy: PARTIAL_PROGRAM_POLICY.to_owned(),
                conversion_error: None,
            },
        ),
    ] {
        assert_rejected_diagnostic_state(&report.records, attempt, payload);
    }
}
