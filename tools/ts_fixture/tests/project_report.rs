use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicUsize, Ordering},
};

use ts_fixture::project::{ProjectReport, ProjectStage, run_project};

struct TestProject(PathBuf);

impl TestProject {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "ts-project-report-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn write(&self, path: &str, text: &str) -> PathBuf {
        let path = self.0.join(path);
        fs::write(&path, text).unwrap();
        path
    }

    fn run(&self, config: &str) -> ProjectReport {
        let path = self.write("tsconfig.json", config);
        run_project(&path, Some("project-test"), "test-process").unwrap()
    }
}

impl Drop for TestProject {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn project_report_forces_replay_and_compares_owned_artifacts_and_identities() {
    let project = TestProject::new();
    project.write("index.ts", "const value: number = 1;\nvalue;\n");
    let report = project.run(
        r#"{
        "compilerOptions": {"noLib": true, "noEmit": true},
        "files": ["index.ts"]
    }"#,
    );
    assert!(matches!(report.construction, ProjectStage::Complete { .. }));
    assert!(!report.has_invariant_failure());
    let ProjectStage::Complete { value: equality } = &report.replay_equality else {
        panic!("replay was not compared: {:?}", report.replay_equality);
    };
    assert!(equality.diagnostic_records);
    assert!(equality.checker_store_identity);
    assert_eq!(equality.type_bytes, Some(true));
    assert_eq!(equality.symbol_bytes, Some(true));
    assert_eq!(equality.type_walk, Some(true));
    assert_eq!(equality.symbol_walk, Some(true));
    assert_eq!(equality.type_identities, Some(true));
    assert_eq!(equality.symbol_identities, Some(true));
    let ProjectStage::Complete { value: graph } = &report.graph else {
        panic!("missing graph");
    };
    assert_eq!(graph.evidence["options"]["no_emit"], true);
    assert_eq!(graph.evidence["options"]["no_lib"], true);
    assert!(
        !graph
            .missing_evidence
            .contains(&"config_extends_inputs".to_owned())
    );
    assert_eq!(
        graph.evidence["configResolutionObservation"]["retentionComplete"],
        true
    );
    assert!(
        graph
            .missing_evidence
            .contains(&"source_real_paths".to_owned())
    );
    assert!(!project.0.join("index.js").exists());
    assert!(matches!(
        report.cross_implementation_comparison,
        ProjectStage::Unavailable { .. }
    ));
    let encoded = serde_json::to_value(&report).unwrap();
    assert!(encoded["cold"]["types"]["walkDigest"].is_string());
    assert!(matches!(
        encoded["cold"]["diagnostics"]["value"]["pinnedErrorBaseline"]["status"].as_str(),
        Some("complete" | "no_content")
    ));
}

#[test]
fn project_report_records_no_check_without_empty_semantic_placeholders() {
    let project = TestProject::new();
    project.write("index.ts", "const value = 1;\n");
    let report = project.run(
        r#"{
        "compilerOptions": {"noLib": true, "noCheck": true},
        "files": ["index.ts"]
    }"#,
    );
    assert!(matches!(
        report.construction,
        ProjectStage::Unavailable { .. }
    ));
    assert!(matches!(report.replay, ProjectStage::Unavailable { .. }));
    assert!(matches!(
        report.cold.types.output,
        ProjectStage::Unavailable { .. }
    ));
    assert_eq!(report.cold.types.visited_nodes, None);
    assert_eq!(report.cold.types.walk_digest, None);
    assert!(
        serde_json::to_value(&report).unwrap()["cold"]["types"]["output"]
            .get("value")
            .is_none()
    );
    assert!(!project.0.join("index.js").exists());
}

#[test]
fn project_report_keeps_unreadable_config_and_unsupported_references_distinct() {
    let project = TestProject::new();
    let missing = run_project(&project.0.join("missing.json"), None, "missing-config").unwrap();
    assert!(matches!(
        missing.construction,
        ProjectStage::Unavailable { .. }
    ));
    let ProjectStage::Complete { value: diagnostics } = &missing.cold.diagnostics else {
        panic!("missing config diagnostic");
    };
    assert!(!diagnostics.records.is_empty());
    project.write("index.ts", "const value = 1;\n");
    let unsupported = project.run(
        r#"{
        "compilerOptions": {"noLib": true, "noEmit": true},
        "files": ["index.ts"], "references": [{"path": "./other"}]
    }"#,
    );
    assert!(matches!(
        unsupported.construction,
        ProjectStage::Unsupported { .. }
    ));
    assert!(matches!(
        unsupported.graph,
        ProjectStage::Unavailable { .. }
    ));
    assert!(matches!(
        unsupported.cold.diagnostics,
        ProjectStage::Unavailable { .. }
    ));
    assert!(matches!(
        unsupported.cold.types.output,
        ProjectStage::Unavailable { .. }
    ));
    assert!(!unsupported.has_invariant_failure());
}

#[test]
fn project_report_keeps_dependency_declarations_in_file_order_and_input_digests() {
    let project = TestProject::new();
    let root = project.write(
        "index.ts",
        "/// <reference path=\"./dependency.d.ts\" />\nconst value = 1;\n",
    );
    let dependency = project.write("dependency.d.ts", "type Dependency = number;\n");
    let report = project.run(
        r#"{
        "compilerOptions": {"noLib": true, "skipLibCheck": true, "noEmit": true},
        "files": ["index.ts"]
    }"#,
    );
    let ProjectStage::Complete { value: graph } = &report.graph else {
        panic!("missing graph");
    };
    assert_eq!(
        graph.evidence["artifactFileOrder"],
        serde_json::json!([root.to_str(), dependency.to_str()])
    );
    let sources = graph.evidence["sources"].as_array().unwrap();
    assert_eq!(sources.len(), 2);
    assert!(sources.iter().all(|source| {
        source["digest"]
            .as_str()
            .is_some_and(|digest| digest.len() == 32)
    }));
    assert!(
        sources
            .iter()
            .any(|source| source["declarationFile"] == true)
    );
}

#[test]
fn project_report_keeps_package_parser_text_separate_from_disk_bom_bytes() {
    let project = TestProject::new();
    project.write(
        "index.ts",
        "import { value } from 'pkg'; export { value };\n",
    );
    project.write("package.json", r#"{"type":"module"}"#);
    fs::create_dir_all(project.0.join("node_modules/pkg")).unwrap();
    let target = project.write(
        "node_modules/pkg/index.d.ts",
        "export declare const value: number;\n",
    );
    let text = "{\r\n\"type\":\"module\",\"types\":\"index.d.ts\",\"unused\":\"\u{00e9}\"}\r\n";
    let package = project.write("node_modules/pkg/package.json", &format!("\u{feff}{text}"));
    let config = r#"{
        "compilerOptions": {
            "noLib": true, "noCheck": true, "noEmit": true, "types": [],
            "module": "ESNext", "moduleResolution": "Bundler"
        },
        "files": ["index.ts"]
    }"#;
    let ProjectStage::Complete { value: graph } = project.run(config).graph else {
        panic!("missing graph");
    };
    let resolution = &graph.evidence["resolutions"][0];
    let inputs = &resolution["packageJsonInputs"];
    assert_eq!(inputs["inputOrigin"], "resolver_worker");
    assert_eq!(inputs["textRepresentation"], "vfs_parser_input");
    let reads = inputs["events"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|event| event["kind"] == "read_file")
        .filter(|event| event["path"].as_str() == package.to_str())
        .collect::<Vec<_>>();
    assert!(!reads.is_empty());
    for read in reads {
        assert_eq!(read["path"].as_str(), package.to_str());
        assert_eq!(read["result"]["parserInputText"], text);
        assert_eq!(read["result"]["parserInputTextUtf8ByteCount"], text.len());
    }
    let scopes = &graph.evidence["sourcePackageScopeObservation"];
    assert_eq!(scopes["retentionComplete"], true);
    assert!(scopes["events"].as_array().unwrap().iter().any(|event| {
        event["sourceFile"].as_str() == target.to_str()
            && event["path"].as_str() == package.to_str()
            && event["result"]["parserInputText"] == text
    }));
    for gap in ["source_package_scopes", "resolution_package_json_inputs"] {
        assert!(!graph.missing_evidence.iter().any(|value| value == gap));
    }
    for gap in ["source_real_paths", "package_identities"] {
        assert!(graph.missing_evidence.iter().any(|value| value == gap));
    }
    fs::write(package, text).unwrap();
    let ProjectStage::Complete { value: without_bom } = project.run(config).graph else {
        panic!("missing graph");
    };
    assert_eq!(graph, without_bom);
}

#[test]
fn project_report_rejects_relative_config_paths() {
    let error = run_project(std::path::Path::new("tsconfig.json"), None, "relative").unwrap_err();
    assert_eq!(error.kind(), std::io::ErrorKind::InvalidInput);
}

fn census(
    project: &TestProject,
    config: &str,
    options: &ts_fixture::project::ProjectCensusOptions,
) -> (Vec<u8>, ts_fixture::project::ProjectCensusReadback) {
    let mut bytes = Vec::new();
    ts_fixture::project::run_project_census(
        &project.write("census.json", config),
        Some("full-input-census"),
        "census-test",
        options,
        &mut bytes,
    )
    .unwrap();
    let report = ts_fixture::project::read_project_census(bytes.as_slice()).unwrap();
    (bytes, report)
}

#[test]
fn project_census_keeps_two_returned_root_failures_and_the_ordinary_control() {
    use ts_fixture::project::{ProjectCensusEvent, ProjectCensusOutcome};
    let project = TestProject::new();
    project.write("first.ts", "function* first() { yield 1; }\n");
    project.write("second.ts", "function* second() { yield 2; }\n");
    let (_, report) = census(
        &project,
        r#"{"compilerOptions":{"noLib":true,"noEmit":true},"files":["first.ts","second.ts"]}"#,
        &Default::default(),
    );
    assert!(report.has_footer);
    assert_eq!(report.completion.as_deref(), Some("complete"));
    assert!(!report.truncated_final_record);
    let ProjectCensusOutcome::Unsupported { failure: ordinary } = &report.ordinary else {
        panic!(
            "ordinary control did not retain its first failure: {:?}",
            report.ordinary
        );
    };
    assert_eq!(ordinary.phase, "source");
    let roots = report.roots.as_ref().unwrap();
    assert_eq!(roots.len(), 2);
    for (index, root) in roots.iter().enumerate() {
        assert_eq!(root.root.root_index, index);
        assert!(root.started);
        assert_eq!(root.input_identity, report.input_identity);
        assert_eq!(root.phase_reached.as_deref(), Some("source"));
        assert!(root.elapsed_ms.is_some());
        let ProjectCensusOutcome::Unsupported { failure } = &root.outcome else {
            panic!(
                "cold root did not retain its own returned failure: {:?}",
                root.outcome
            );
        };
        assert_eq!(failure.phase, "source");
        assert!(failure.returned_error.contains("SourceCheck"));
        assert!(
            failure
                .returned_error
                .contains(if index == 0 { "first.ts" } else { "second.ts" })
        );
        let location = failure.location.as_ref().unwrap();
        assert_eq!(location.file_name, root.root.file_name);
        assert!(location.start_byte < location.end_byte);
    }
    assert!(ordinary.returned_error.contains("first.ts"));
    let loaded = report
        .records
        .iter()
        .position(|record| matches!(record.event, ProjectCensusEvent::Loaded { .. }))
        .unwrap();
    let ordinary_start = report
        .records
        .iter()
        .position(|record| matches!(record.event, ProjectCensusEvent::AttemptStarted { .. }))
        .unwrap();
    assert!(loaded < ordinary_start);
    assert!(
        report.records[loaded..]
            .iter()
            .all(|record| record.input_identity == report.input_identity)
    );
    for phase in ["binding", "context", "source"] {
        assert_eq!(report.records.iter().filter(|record| matches!(&record.event, ProjectCensusEvent::PhaseFinished { phase: actual, .. } if actual == phase)).count(), 3);
    }
    assert!(!report.records.iter().any(|record| matches!(&record.event, ProjectCensusEvent::PhaseStarted { attempt: ts_fixture::project::ProjectCensusAttempt::Root { .. }, phase } if phase == "post_source")));
}

#[test]
fn project_census_keeps_full_binding_policy_and_diagnostics_unavailable_for_cold_roots() {
    use ts_fixture::project::{ProjectCensusEvent, ProjectCensusOutcome};
    let project = TestProject::new();
    project.write("globals.d.ts", "declare const shared: number;\n");
    project.write(
        "input.ts",
        "const value: number = shared;\nconst mismatch: number = \"wrong\";\n",
    );
    project.write("skip.ts", "// @ts-nocheck\nconst skipped = (a, b) => a;\n");
    let (_, report) = census(
        &project,
        r#"{"compilerOptions":{"noLib":true,"skipLibCheck":true,"noEmit":true},"files":["globals.d.ts","input.ts","skip.ts"]}"#,
        &Default::default(),
    );
    assert_eq!(report.ordinary, ProjectCensusOutcome::OrdinaryCheckComplete);
    let roots = report.roots.as_ref().unwrap();
    assert_eq!(roots.len(), 3);
    assert!(
        matches!(&roots[0].outcome, ProjectCensusOutcome::SkippedByOriginalPolicy { reason } if reason == "declaration_file")
    );
    assert_eq!(roots[1].outcome, ProjectCensusOutcome::SourceCheckComplete);
    assert!(
        matches!(&roots[2].outcome, ProjectCensusOutcome::SkippedByOriginalPolicy { reason } if reason == "no_check_directive")
    );
    let ProjectCensusEvent::Loaded { graph, .. } = &report
        .records
        .iter()
        .find(|record| matches!(record.event, ProjectCensusEvent::Loaded { .. }))
        .unwrap()
        .event
    else {
        unreachable!()
    };
    assert_eq!(graph["evidence"]["sources"].as_array().unwrap().len(), 3);
    let ProjectCensusEvent::RunStarted { unavailable, .. } = &report.records[0].event else {
        unreachable!()
    };
    assert!(
        unavailable
            .iter()
            .any(|detail| detail.contains("complete diagnostics"))
    );
    let encoded = serde_json::to_value(&report.records).unwrap();
    assert!(
        !encoded
            .to_string()
            .contains("Complete canonical Program snapshot")
    );
    assert!(
        encoded
            .as_array()
            .unwrap()
            .iter()
            .all(|record| record.get("diagnostics").is_none())
    );
}

#[test]
fn project_census_keeps_no_check_load_failures_and_soft_stops_distinct() {
    use ts_fixture::project::{ProjectCensusEvent, ProjectCensusOptions, ProjectCensusOutcome};
    let project = TestProject::new();
    project.write("input.ts", "const value = (a, b) => a;\n");
    let (_, no_check) = census(
        &project,
        r#"{"compilerOptions":{"noLib":true,"noCheck":true},"files":["input.ts","input.ts","missing.ts"]}"#,
        &Default::default(),
    );
    assert_eq!(no_check.completion.as_deref(), Some("no_check"));
    assert!(no_check.ordinary_started);
    assert!(
        matches!(&no_check.ordinary, ProjectCensusOutcome::SkippedByOriginalPolicy { reason } if reason == "no_check")
    );
    assert!(
        !no_check
            .records
            .iter()
            .any(|record| matches!(record.event, ProjectCensusEvent::PhaseStarted { .. }))
    );
    let roots = no_check.roots.as_ref().unwrap();
    assert_eq!(roots.len(), 2);
    assert!(roots[0].root.file_id.is_some());
    assert_eq!(roots[1].root.file_id, None);
    let ProjectCensusEvent::Loaded { graph, .. } = &no_check
        .records
        .iter()
        .find(|record| matches!(record.event, ProjectCensusEvent::Loaded { .. }))
        .unwrap()
        .event
    else {
        unreachable!()
    };
    let files = graph["evidence"]["config"]["resolvedFiles"]
        .as_array()
        .unwrap();
    assert_eq!(files.len(), 3);
    assert_eq!(files[0], files[1]);
    assert!(
        matches!(&roots[0].outcome, ProjectCensusOutcome::SkippedByOriginalPolicy { reason } if reason == "no_check")
    );
    assert!(
        matches!(&roots[1].outcome, ProjectCensusOutcome::Unattempted { reason } if reason.contains("not loaded"))
    );

    let mut missing_bytes = Vec::new();
    ts_fixture::project::run_project_census(
        &project.0.join("absent.json"),
        None,
        "missing-config",
        &Default::default(),
        &mut missing_bytes,
    )
    .unwrap();
    let missing = ts_fixture::project::read_project_census(missing_bytes.as_slice()).unwrap();
    assert_eq!(missing.completion.as_deref(), Some("load_unavailable"));
    assert!(missing.roots.is_none());
    assert!(missing.records.iter().any(|record| matches!(&record.event, ProjectCensusEvent::Loaded { disposition, load_diagnostics, .. } if disposition == "config_unavailable" && !load_diagnostics.is_empty())));
    let (_, references) = census(
        &project,
        r#"{"compilerOptions":{"noLib":true},"files":["input.ts"],"references":[{"path":"./other"}]}"#,
        &Default::default(),
    );
    assert!(references.roots.is_none());
    assert!(references.records.iter().any(|record| matches!(&record.event, ProjectCensusEvent::LoadFailed { failure, .. } if failure.class == "unsupported" && failure.returned_error.contains("ProjectReferencesUnsupported"))));

    let (_, stopped) = census(
        &project,
        r#"{"compilerOptions":{"noLib":true},"files":["input.ts"]}"#,
        &ProjectCensusOptions {
            soft_deadline: Some(std::time::Duration::ZERO),
            ..Default::default()
        },
    );
    assert_eq!(stopped.completion.as_deref(), Some("stopped"));
    assert!(stopped.roots.is_none());
    assert_eq!(stopped.records.len(), 3);
    assert!(matches!(
        stopped.records[1].event,
        ProjectCensusEvent::LoadStarted
    ));
    assert!(!stopped.ordinary_started);
}

#[test]
fn project_census_flush_errors_and_truncated_streams_keep_prior_results() {
    use std::io::{self, Write};
    use ts_fixture::project::{ProjectCensusOutcome, read_project_census, run_project_census};
    struct StopWriter {
        bytes: Vec<u8>,
        failed: bool,
        writes_after_failure: usize,
        flushes: usize,
    }
    impl Write for StopWriter {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            if self.failed {
                self.writes_after_failure += 1;
                return Err(io::Error::other("write after failed flush"));
            }
            self.bytes.extend_from_slice(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            self.flushes += 1;
            let last = self
                .bytes
                .split(|byte| *byte == b'\n')
                .rev()
                .find(|line| !line.is_empty())
                .unwrap();
            let record: serde_json::Value = serde_json::from_slice(last).unwrap();
            if record["event"] == "attempt_started" && record["attempt"]["root_index"] == 1 {
                self.failed = true;
                return Err(io::Error::other("planned output failure"));
            }
            Ok(())
        }
    }
    let project = TestProject::new();
    project.write("first.ts", "const first: number = 1;\n");
    project.write("second.ts", "const second: number = 2;\n");
    let config = project.write(
        "census.json",
        r#"{"compilerOptions":{"noLib":true},"files":["first.ts","second.ts"]}"#,
    );
    let mut writer = StopWriter {
        bytes: Vec::new(),
        failed: false,
        writes_after_failure: 0,
        flushes: 0,
    };
    let error = run_project_census(
        &config,
        None,
        "output-failure",
        &Default::default(),
        &mut writer,
    )
    .unwrap_err();
    assert_eq!(error.to_string(), "planned output failure");
    assert!(writer.failed);
    assert_eq!(writer.writes_after_failure, 0);
    let partial = read_project_census(writer.bytes.as_slice()).unwrap();
    assert_census_roster_evidence(&partial.records);
    assert_eq!(writer.flushes, partial.records.len());
    assert!(!partial.has_footer);
    let roots = partial.roots.as_ref().unwrap();
    assert_eq!(roots[0].outcome, ProjectCensusOutcome::SourceCheckComplete);
    assert!(roots[1].started);
    assert!(
        matches!(&roots[1].outcome, ProjectCensusOutcome::Unattempted { reason } if reason.contains("cause is unknown"))
    );
    writer.bytes.extend_from_slice(b"{\"schemaVersion\":");
    let truncated = read_project_census(writer.bytes.as_slice()).unwrap();
    assert!(truncated.truncated_final_record);
    assert_eq!(truncated.roots, partial.roots);
    writer.bytes.push(b'\n');
    assert!(read_project_census(writer.bytes.as_slice()).is_err());
    let mut malformed = Vec::new();
    for (index, record) in partial.records.iter().enumerate() {
        let mut record = record.clone();
        if index == 1 {
            record.sequence += 1;
        }
        serde_json::to_writer(&mut malformed, &record).unwrap();
        malformed.push(b'\n');
    }
    assert!(read_project_census(malformed.as_slice()).is_err());
}

fn assert_census_roster_evidence(records: &[ts_fixture::project::ProjectCensusRecord]) {
    use ts_fixture::project::{ProjectCensusEvent, ProjectCensusRecord, read_project_census};

    fn encode(records: &[ProjectCensusRecord]) -> Vec<u8> {
        let mut bytes = Vec::new();
        for record in records {
            serde_json::to_writer(&mut bytes, record).unwrap();
            bytes.push(b'\n');
        }
        bytes
    }

    fn rebind(records: &mut [ProjectCensusRecord]) {
        let mut identity = None;
        for record in records {
            if let ProjectCensusEvent::Loaded { graph, roots, .. } = &record.event {
                let bytes = serde_json::to_vec(&(graph, roots.as_deref())).unwrap();
                identity = Some(format!("{:032x}", xxhash_rust::xxh3::xxh3_128(&bytes)));
            }
            record.input_identity.clone_from(&identity);
        }
    }

    let loaded = records
        .iter()
        .position(|record| matches!(record.event, ProjectCensusEvent::Loaded { .. }))
        .unwrap();
    let mut rebound = records.to_vec();
    rebind(&mut rebound);
    assert_eq!(encode(&rebound), encode(records));
    assert!(read_project_census(encode(&rebound).as_slice()).is_ok());
    for change in 0..5 {
        for recompute_identity in [false, true] {
            let mut damaged = records.to_vec();
            let ProjectCensusEvent::Loaded { roots, .. } = &mut damaged[loaded].event else {
                unreachable!()
            };
            let roots = roots.as_mut().unwrap();
            match change {
                0 => roots[0].requested_name.push_str(".changed"),
                1 => roots[0].file_name.push_str(".changed"),
                2 => {
                    assert_ne!(roots[0].file_id, roots[1].file_id);
                    roots[0].file_id = roots[1].file_id;
                }
                3 => roots[0].file_id = None,
                4 => {
                    roots.pop();
                }
                _ => unreachable!(),
            }
            if recompute_identity {
                rebind(&mut damaged);
            }
            let error = read_project_census(encode(&damaged).as_slice()).unwrap_err();
            assert_eq!(error.kind(), std::io::ErrorKind::InvalidData);
            assert!(error.to_string().contains("graph"));
        }
    }

    // A loaded source can use different path case than the requested root.
    let mut insensitive = records.to_vec();
    let ProjectCensusEvent::Loaded { graph, roots, .. } = &mut insensitive[loaded].event else {
        unreachable!()
    };
    let root = &roots.as_ref().unwrap()[0];
    graph["evidence"]["caseSensitive"] = false.into();
    graph["evidence"]["sources"][root.file_id.unwrap()]["fileName"] =
        root.file_name.to_uppercase().into();
    rebind(&mut insensitive);
    assert!(read_project_census(encode(&insensitive).as_slice()).is_ok());
    let ProjectCensusEvent::Loaded { graph, .. } = &mut insensitive[loaded].event else {
        unreachable!()
    };
    graph["evidence"]["caseSensitive"] = true.into();
    rebind(&mut insensitive);
    let error = read_project_census(encode(&insensitive).as_slice()).unwrap_err();
    assert_eq!(
        error.to_string(),
        "The census file ID names a different graph source."
    );
}
